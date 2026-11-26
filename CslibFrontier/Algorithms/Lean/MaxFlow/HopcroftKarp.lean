/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt

/-!
# Hopcroft–Karp Maximum Bipartite Matching

Pure executable specification and correctness proofs for the **Hopcroft–Karp algorithm**
([HopcroftKarp1973]; [CLRS2009], Problem 26-6) on `G : Fin m × Fin r → Bool` with candidate
neighbour lists `adj : Fin m → List (Fin r)`. Returns a maximum matching together with a minimum
König vertex cover after at most `2⌊√ν⌋` augmenting phases (`ν` the maximum matching size).

Machine-checked `O((m + r + |E|) √ν)` sparse and `O((m + r)² √ν)` dense running-time bounds on the
word RAM live in `CslibFrontier.Algorithms.WordRAM.HopcroftKarp`.

## Algorithm and source mapping

The matching is stored as a right-indexed mate table `mate : Vector (Option (Fin m)) r`
(`mateMatching`). Each round of `hkLoop` is:

1. **Breadth-first layering (`hkBfs`):** computes the exact alternating layers `IsLayer` of
   `CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath` in FIFO queue order up to the first layer
   `k` adjacent to a free right vertex (`hkBfs_spec`). If there is none, the layers have closed up
   and the unreached left vertices together with the reached right vertices form a König cover
   certifying maximality (`isMaxMatching_isMinVertexCover_of_stable`).
2. **Depth-first phase (`hkPhase`):** a depth-first search from every free left vertex along
   the layers, sharing one visited table over right vertices, collects vertex-disjoint shortest
   augmenting paths (`hkDfsRoots`). The collected edge list is an `IsLayeredFamily` admitting
   no further layered path, hence an `IsMaximalLayeredAugmentation`; the
   mate table is then rematched along it (`hkPhase_spec`). The phase lemma
   `IsMaximalLayeredAugmentation.noShortAug_augment` and the phase bound
   `IsPhaseRun.le_two_mul_sqrt` give at most `2⌊√ν⌋` rounds that augment. This is slightly
   sharper than the `2⌊√s⌋ + 2` bound of [HopcroftKarp1973], Theorem 3, which counts distinct
   shortest augmenting path lengths.

The phase bound and Berge's theorem are proved through the layered counting lemma
`card_mul_le_of_noShortAug` rather than the textbook decomposition of `M ⊕ M*` into
vertex-disjoint augmenting paths; see `CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath`.

## Main definitions

* `BipAdjValid`, `bipAdjSteps`, `denseBipAdj`, `exactBipAdj`: candidate neighbour lists and their
  total length.
* `mateMatching`: the matching encoded by a mate table.
* `hkBfs`, `hkDfs`, `hkDfsRoots`, `hkPhase`, `hkLoop`: layering, depth-first search, one phase,
  and the phase loop.
* `HopcroftKarpOutput`, `hopcroftKarp`, `hopcroftKarpDense`, `decidePerfectMatchingHK`.
* `vecPotential`, `hkDfsCost`: potential functions bounding total vertex/edge inspections per round
  (reused by the word-RAM cost analysis).

## Main results

* `hopcroftKarp_correct`: maximum matching, minimum vertex cover, equal sizes (König), and at
  most `2⌊√ν⌋` phases.
* `hopcroftKarpDense_correct`, `hopcroftKarp_exactBipAdj`: the dense instance and its agreement
  with exact filtered neighbour lists.
* `card_hopcroftKarp_matching_eq`: agreement in matching size with any maximum matching of `G`.
* `decidePerfectMatchingHK_eq_true_iff`: perfect-matching decision characterization
  (`HasPerfectMatching`).

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean

/-! ### Graph inputs and mate tables -/

variable {m r : ℕ}

/-- Candidate neighbour lists `adj` cover every edge of `G`. -/
@[expose] def BipAdjValid (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) : Prop :=
  ∀ u v, G (u, v) = true → v ∈ adj u

/-- Total length of the candidate neighbour lists (`|E|` for exact adjacency lists). -/
@[expose] def bipAdjSteps (adj : Fin m → List (Fin r)) : ℕ := ∑ u, (adj u).length

/-- Dense candidate neighbour lists enumerating every right vertex. -/
@[expose] def denseBipAdj (m r : ℕ) : Fin m → List (Fin r) := fun _ => List.finRange r

/-- Exact neighbour lists of `G`, enumerating the right neighbours of `u` in ascending order. -/
@[expose] def exactBipAdj (G : Fin m × Fin r → Bool) (u : Fin m) : List (Fin r) :=
  (List.finRange r).filter fun v => G (u, v)

theorem bipAdjValid_denseBipAdj (G : Fin m × Fin r → Bool) : BipAdjValid G (denseBipAdj m r) :=
  fun _ v _ => List.mem_finRange v

theorem bipAdjValid_exactBipAdj (G : Fin m × Fin r → Bool) : BipAdjValid G (exactBipAdj G) :=
  fun _ v hG => List.mem_filter.mpr ⟨List.mem_finRange v, hG⟩

@[simp]
theorem bipAdjSteps_denseBipAdj : bipAdjSteps (denseBipAdj m r) = m * r := by
  simp [bipAdjSteps, denseBipAdj, Finset.sum_const]

theorem bipAdjSteps_exactBipAdj_le (G : Fin m × Fin r → Bool) :
    bipAdjSteps (exactBipAdj G) ≤ m * r := by
  have hle : ∀ u : Fin m, (exactBipAdj G u).length ≤ r := fun u =>
    (List.length_filter_le _ _).trans_eq (List.length_finRange)
  calc bipAdjSteps (exactBipAdj G)
      ≤ ∑ _ : Fin m, r := Finset.sum_le_sum fun u _ => hle u
    _ = m * r := by simp [Finset.sum_const]

/-- Matching encoded by a right-vertex mate table: `(u, v)` is matched iff `mate[v] = some u`. -/
@[expose] def mateMatching (mate : Vector (Option (Fin m)) r) : Finset (Fin m × Fin r) :=
  Finset.univ.filter fun e => vget mate e.2 = some e.1

@[simp]
theorem mem_mateMatching {mate : Vector (Option (Fin m)) r} {e : Fin m × Fin r} :
    e ∈ mateMatching mate ↔ vget mate e.2 = some e.1 := by
  simp [mateMatching]

/-! ### Breadth-first layering -/

/-- Mark the mate of the right vertex `v`. -/
@[expose] def hkMarkStep (mate : Vector (Option (Fin m)) r) (b : Vector Bool m) (v : Fin r) :
    Vector Bool m :=
  match vget mate v with
  | some u => vset b u true
  | none => b

/-- Mark the left vertices matched by `mate`. -/
@[expose] def hkMatchedLeft (mate : Vector (Option (Fin m)) r) : Vector Bool m :=
  (List.finRange r).foldl (hkMarkStep mate) (Vector.replicate m false)

/-- State of the expansion of one breadth-first layer. -/
structure HKBfsState (m : ℕ) where
  /-- Layer index of each discovered left vertex. -/
  dist : Vector (Option ℕ) m
  /-- Left vertices discovered for the next layer (in FIFO order). -/
  next : List (Fin m)
  /-- Whether a free right vertex is adjacent to the current layer. -/
  found : Bool

/-- Inspect the candidate edge `(u, v)` from layer `j`: a free `v` sets `found`; the mate `w` of a
matched `v` is discovered in layer `j + 1` unless already discovered. -/
@[expose] def hkBfsStep (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (j : ℕ)
    (u : Fin m) (s : HKBfsState m) (v : Fin r) : HKBfsState m :=
  if G (u, v) = true then
    match vget mate v with
    | none => { s with found := true }
    | some w =>
      if vget s.dist w = none then
        { s with dist := vset s.dist w (some (j + 1)), next := s.next ++ [w] }
      else s
  else s

/-- Expand the frontier `us` of layer `j`. -/
@[expose] def hkBfsLayer (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    HKBfsState m :=
  us.foldl (fun s u => (adj u).foldl (hkBfsStep G mate j u) s) s

/-- Result of a breadth-first layering: layer indices, the last layer `k`, and whether a free right
vertex is adjacent to layer `k`. -/
structure HKBfsResult (m : ℕ) where
  /-- Layer index of each reached left vertex. -/
  dist : Vector (Option ℕ) m
  /-- Index of the last expanded layer. -/
  k : ℕ
  /-- Whether layer `k` reaches a free right vertex. -/
  found : Bool

/-- Expand layers `j, j + 1, …` until a free right vertex is found or no new vertex appears. -/
@[expose] def hkBfsLoop (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) :
    ℕ → ℕ → Vector (Option ℕ) m → List (Fin m) → HKBfsResult m
  | 0, j, dist, _ => ⟨dist, j, false⟩
  | fuel + 1, j, dist, frontier =>
    let s := hkBfsLayer G adj mate j frontier ⟨dist, [], false⟩
    if s.found then ⟨s.dist, j, true⟩
    else if s.next.isEmpty then ⟨s.dist, j, false⟩
    else hkBfsLoop G adj mate fuel (j + 1) s.dist s.next

/-- Put a free left vertex into layer `0` (in ascending FIFO order). -/
@[expose] def hkBfsInitStep (ml : Vector Bool m) (p : Vector (Option ℕ) m × List (Fin m))
    (u : Fin m) : Vector (Option ℕ) m × List (Fin m) :=
  if vget ml u = true then p else (vset p.1 u (some 0), p.2 ++ [u])

/-- Breadth-first layering of the alternating graph of the matching encoded by `mate`. -/
@[expose] def hkBfs (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) : HKBfsResult m :=
  let ml := hkMatchedLeft mate
  let p := (List.finRange m).foldl (hkBfsInitStep ml) (Vector.replicate m none, [])
  hkBfsLoop G adj mate (m + 1) 0 p.1 p.2

/-! ### Depth-first search for vertex-disjoint shortest augmenting paths -/

/-- Scan the candidates `vs` of `u` in layer `i`. With `accept`, take a free unvisited `v`;
otherwise descend through an unvisited matched `v` whose mate lies in layer `i + 1` using
`next`. Visited right vertices are never revisited. Returns the visited table and, on success,
the found path's non-matching edges prepended to `acc`. -/
@[expose] def hkDfsLevel (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (accept : Bool) (i : ℕ)
    (next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r)))
    (u : Fin m) : List (Fin r) → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))
  | [], vis, _ => (vis, none)
  | v :: vs, vis, acc =>
    if G (u, v) = true ∧ vget vis v = false then
      match vget mate v with
      | none =>
        if accept = true then (vset vis v true, some ((u, v) :: acc))
        else hkDfsLevel G mate dist accept i next u vs vis acc
      | some w =>
        if accept = false ∧ vget dist w = some (i + 1) then
          let res := next w (vset vis v true) acc
          match res.2 with
          | some q => (res.1, some ((u, v) :: q))
          | none => hkDfsLevel G mate dist accept i next u vs res.1 acc
        else hkDfsLevel G mate dist accept i next u vs vis acc
    else hkDfsLevel G mate dist accept i next u vs vis acc

/-- Depth-first search from `u` in layer `i` with `f` layers remaining. -/
@[expose] def hkDfs (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ℕ → ℕ → Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))
  | 0, i, u, vis, acc =>
    hkDfsLevel G mate dist true i (fun _ vis _ => (vis, none)) u (adj u) vis acc
  | f + 1, i, u, vis, acc =>
    hkDfsLevel G mate dist false i (hkDfs G adj mate dist f (i + 1)) u (adj u) vis acc

/-- Run the depth-first search from every layer-`0` vertex of `us`, sharing the visited table. -/
@[expose] def hkDfsRoots (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) (k : ℕ) :
    List (Fin m) → Vector Bool r → List (Fin m × Fin r) → List (Fin m × Fin r)
  | [], _, acc => acc
  | u :: us, vis, acc =>
    if vget dist u = some 0 then
      let res := hkDfs G adj mate dist k 0 u vis acc
      hkDfsRoots G adj mate dist k us res.1 (res.2.getD acc)
    else hkDfsRoots G adj mate dist k us vis acc

/-- Rematch the right end of every edge of `es` to its left end. -/
@[expose] def hkApplyEdges (mate : Vector (Option (Fin m)) r) (es : List (Fin m × Fin r)) :
    Vector (Option (Fin m)) r :=
  es.foldl (fun mt e => vset mt e.2 (some e.1)) mate

/-- One augmenting phase for the layering `dist` with shortest augmenting parameter `k`. -/
@[expose] def hkPhase (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) (k : ℕ) :
    Vector (Option (Fin m)) r :=
  let es := hkDfsRoots G adj mate dist k (List.finRange m) (Vector.replicate r false) []
  hkApplyEdges mate es

/-- Final state of the phase loop. -/
structure HKLoopResult (m r : ℕ) where
  /-- Final mate table. -/
  mate : Vector (Option (Fin m)) r
  /-- Final (closed) layering. -/
  dist : Vector (Option ℕ) m
  /-- Number of augmenting phases performed. -/
  phases : ℕ

/-- Alternate breadth-first layering and augmenting phases until no augmenting path remains. -/
@[expose] def hkLoop (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) :
    ℕ → ℕ → Vector (Option (Fin m)) r → HKLoopResult m r
  | 0, n, mate => ⟨mate, Vector.replicate m none, n⟩
  | fuel + 1, n, mate =>
    let b := hkBfs G adj mate
    if b.found then
      let mate' := hkPhase G adj mate b.dist b.k
      hkLoop G adj fuel (n + 1) mate'
    else ⟨mate, b.dist, n⟩

/-- Collect the matched edge at the right vertex `v`. -/
@[expose] def hkMatchingStep (mate : Vector (Option (Fin m)) r) (a : Finset (Fin m × Fin r))
    (v : Fin r) : Finset (Fin m × Fin r) :=
  match vget mate v with
  | some u => insert (u, v) a
  | none => a

/-- Collect the left vertex `u` into the cover when it is unreached. -/
@[expose] def hkCoverLeftStep (dist : Vector (Option ℕ) m) (a : Finset (Fin m)) (u : Fin m) :
    Finset (Fin m) :=
  if vget dist u = none then insert u a else a

/-- Collect the right vertex `v` into the cover when its mate is reached. -/
@[expose] def hkCoverRightStep (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m)
    (a : Finset (Fin r)) (v : Fin r) : Finset (Fin r) :=
  match vget mate v with
  | some w => if vget dist w = none then a else insert v a
  | none => a

/-- Output of `hopcroftKarp`. -/
structure HopcroftKarpOutput (m r : ℕ) where
  /-- Maximum-cardinality matching. -/
  matching : Finset (Fin m × Fin r)
  /-- Minimum-cardinality König vertex cover. -/
  cover : VertexCover (Fin m) (Fin r)
  /-- Number of augmenting phases. -/
  phases : ℕ

/-- **Hopcroft–Karp** on `G : Fin m × Fin r → Bool` with candidate neighbour lists `adj`. -/
@[expose] def hopcroftKarp (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r)) :
    HopcroftKarpOutput m r :=
  let st := hkLoop G adj (m + 1) 0 (Vector.replicate r none)
  let matching := (List.finRange r).foldl (hkMatchingStep st.mate) ∅
  let left := (List.finRange m).foldl (hkCoverLeftStep st.dist) ∅
  let right := (List.finRange r).foldl (hkCoverRightStep st.mate st.dist) ∅
  ⟨matching, ⟨left, right⟩, st.phases⟩

/-- Hopcroft–Karp with dense candidate lists `denseBipAdj m r`. -/
@[expose] def hopcroftKarpDense (G : Fin m × Fin r → Bool) : HopcroftKarpOutput m r :=
  hopcroftKarp G (denseBipAdj m r)

/-! ### Potentials for round cost analysis -/

/-- Total cost of the entries of `t` satisfying `p`. -/
@[expose] def vecPotential {α : Type*} {n : ℕ} (p : α → Prop) [DecidablePred p] (c : Fin n → ℕ)
    (t : Vector α n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => p (vget t u)), c u

theorem vecPotential_vset_add {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    {c : Fin n → ℕ} {t : Vector α n} {w : Fin n} {x : α} (hw : p (vget t w)) (hx : ¬ p x) :
    vecPotential p c (vset t w x) + c w = vecPotential p c t := by
  have hset : Finset.univ.filter (fun u => p (vget (vset t w x) u)) =
      (Finset.univ.filter (fun u => p (vget t u))).erase w := by
    ext u
    rcases eq_or_ne u w with rfl | h
    · simp [hx]
    · simp [h, vget_vset_ne _ _ h.symm]
  simpa [vecPotential, hset] using Finset.sum_erase_add _ c (by simp [hw])

private theorem vecPotential_vset_le {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    {c : Fin n → ℕ} (t : Vector α n) (w : Fin n) {x : α} (hx : ¬ p x) :
    vecPotential p c (vset t w x) ≤ vecPotential p c t := by
  refine Finset.sum_le_sum_of_subset fun u hu => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases eq_or_ne u w with rfl | h
  · exact absurd (by simpa using hu) hx
  · rwa [vget_vset_ne t x h.symm] at hu

theorem vecPotential_le_sum {α : Type*} {n : ℕ} {p : α → Prop} [DecidablePred p]
    (c : Fin n → ℕ) (t : Vector α n) : vecPotential p c t ≤ ∑ u, c u :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Cost charged to a right vertex during a DFS phase: the candidate list length of its mate. -/
@[expose] def hkDfsCost (adj : Fin m → List (Fin r)) (mate : Vector (Option (Fin m)) r)
    (v : Fin r) : ℕ :=
  match vget mate v with
  | some w => (adj w).length
  | none => 0

/-- The initial DFS potential is at most `bipAdjSteps adj` whenever `mate` encodes a matching. -/
theorem vecPotential_replicate_le {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
    {mate : Vector (Option (Fin m)) r} (hM : IsMatching G (mateMatching mate)) :
    vecPotential (· = false) (hkDfsCost adj mate) (Vector.replicate r false) ≤ bipAdjSteps adj := by
  refine (vecPotential_le_sum _ _).trans ?_
  have hc : ∀ v, hkDfsCost adj mate v =
      ∑ u, if vget mate v = some u then (adj u).length else 0 := fun v => by
    cases hv : vget mate v <;> simp [hkDfsCost, hv, Finset.sum_ite_eq]
  simp_rw [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun u _ => ?_
  have hcard : (Finset.univ.filter fun v => vget mate v = some u).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => hM.2.1 u a b
      (by simpa [mem_mateMatching] using ha) (by simpa [mem_mateMatching] using hb)
  simpa [← Finset.sum_filter, smul_eq_mul] using Nat.mul_le_mul_right (adj u).length hcard

/-! ### Matched left vertices -/

private theorem matchedLeft_foldl (mate : Vector (Option (Fin m)) r) (l : List (Fin r))
    (b : Vector Bool m) (u : Fin m) :
    vget (l.foldl (hkMarkStep mate) b) u = true ↔
      vget b u = true ∨ ∃ v ∈ l, vget mate v = some u := by
  induction l generalizing b with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih]
    rcases hv : vget mate v with _ | w <;> simp only [hkMarkStep, hv, List.mem_cons,
      exists_eq_or_imp, reduceCtorEq, false_or, Option.some.injEq]
    by_cases h : w = u <;> simp [h, vget_vset_ne]

private theorem hkMatchedLeft_spec (mate : Vector (Option (Fin m)) r) (u : Fin m) :
    vget (hkMatchedLeft mate) u = true ↔ u ∈ matchedLeft (mateMatching mate) := by
  simp [hkMatchedLeft, matchedLeft_foldl, vget_replicate]

/-! ### Layer `0` -/

private theorem bfsInit_foldl (ml : Vector Bool m) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) :
    (∀ u, vget (l.foldl (hkBfsInitStep ml) p).1 u =
      if u ∈ l ∧ vget ml u = false then some 0 else vget p.1 u) ∧
    (∀ u, u ∈ (l.foldl (hkBfsInitStep ml) p).2 ↔ u ∈ p.2 ∨ (u ∈ l ∧ vget ml u = false)) := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := ih (hkBfsInitStep ml p x)
    refine ⟨fun u => ?_, fun u => ?_⟩
    · rw [ih1 u, hkBfsInitStep]
      rcases eq_or_ne u x with rfl | hux
      · by_cases hx : vget ml u = true <;> simp [hx]
      · by_cases hx : vget ml x = true <;> simp [hx, hux, vget_vset_ne _ _ hux.symm]
    · rw [ih2 u, hkBfsInitStep]
      rcases eq_or_ne u x with rfl | hux <;> split_ifs with hx <;> simp [*]

private theorem bfsInit_nodup (ml : Vector Bool m) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) (hl : l.Nodup) (hp : p.2.Nodup)
    (hdisj : ∀ x ∈ l, x ∉ p.2) : (l.foldl (hkBfsInitStep ml) p).2.Nodup := by
  induction l generalizing p with
  | nil => exact hp
  | cons x l ih =>
    obtain ⟨hxl, hl⟩ := List.nodup_cons.mp hl
    simp only [List.foldl_cons, hkBfsInitStep]
    split_ifs with hx
    · exact ih p hl hp fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    · have hp' : (p.2 ++ [x]).Nodup :=
        List.concat_eq_append ▸ hp.concat (hdisj x List.mem_cons_self)
      refine ih _ hl hp' fun y hy h => ?_
      rcases List.mem_append.mp h with h | h
      · exact hdisj y (List.mem_cons_of_mem _ hy) h
      · exact hxl (List.mem_singleton.mp h ▸ hy)

/-! ### Breadth-first search: one layer -/

section BfsLayer

variable {G : Fin m × Fin r → Bool} {mate : Vector (Option (Fin m)) r}

private theorem vget_mate_eq_none_iff {v : Fin r} :
    vget mate v = none ↔ v ∉ matchedRight (mateMatching mate) := by
  simp [Option.eq_none_iff_forall_ne_some]

/-- Invariant while expanding layer `j`. -/
private structure HKStepInv (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (j : ℕ)
    (s : HKBfsState m) : Prop where
  exact : ∀ u i, i ≤ j → (vget s.dist u = some i ↔ IsLayer G M u i)
  bound : ∀ u i, vget s.dist u = some i → i ≤ j + 1
  next_iff : ∀ u, vget s.dist u = some (j + 1) ↔ u ∈ s.next
  next_layer : ∀ u ∈ s.next, IsLayer G M u (j + 1)
  nodup : s.next.Nodup
  found : s.found = true → ∃ t ∈ altRight G M j, t ∉ matchedRight M

private theorem hkBfsStep_inv {j : ℕ} {u : Fin m} (hu : u ∈ altLeft G (mateMatching mate) j)
    {s : HKBfsState m} (hs : HKStepInv G (mateMatching mate) j s) (v : Fin r) :
    HKStepInv G (mateMatching mate) j (hkBfsStep G mate j u s v) := by
  unfold hkBfsStep
  split_ifs with hG
  · cases hm : vget mate v with
    | none =>
      exact ⟨hs.exact, hs.bound, hs.next_iff, hs.next_layer, hs.nodup, fun _ =>
        ⟨v, mem_altRight.mpr ⟨u, hu, hG⟩, vget_mate_eq_none_iff.mp hm⟩⟩
    | some w =>
      dsimp only
      split_ifs with hd
      · have hwl : IsLayer G (mateMatching mate) w (j + 1) := by
          obtain ⟨i, hi, hwi⟩ := exists_isLayer
            (mem_altLeft_succ_of_mem (mem_mateMatching.mpr hm) (mem_altRight.mpr ⟨u, hu, hG⟩))
          rcases Nat.lt_or_eq_of_le hi with hlt | rfl
          · exact absurd ((hs.exact w i (by omega)).mpr hwi) (by simp [hd])
          · exact hwi
        have hw_not_next : w ∉ s.next := fun h => by simpa [hd] using (hs.next_iff w).mpr h
        have hnd' : (s.next ++ [w]).Nodup := List.concat_eq_append ▸ hs.nodup.concat hw_not_next
        refine ⟨fun x i hi => ?_, fun x i hx => ?_, fun x => ?_,
          fun x hx => (List.mem_append.mp hx).elim (hs.next_layer x)
            fun hx => List.mem_singleton.mp hx ▸ hwl,
          hnd', hs.found⟩
        · rcases eq_or_ne x w with rfl | hxw
          · exact ⟨fun h => by simp at h; omega,
              fun h => absurd ((hs.exact x i hi).mpr h) (by simp [hd])⟩
          · simp [vget_vset_ne _ _ hxw.symm, hs.exact x i hi]
        · rcases eq_or_ne x w with rfl | hxw
          · simp at hx; omega
          · exact hs.bound x i (by rwa [vget_vset_ne _ _ hxw.symm] at hx)
        · rcases eq_or_ne x w with rfl | hxw
          · simp
          · simp [vget_vset_ne _ _ hxw.symm, hs.next_iff, hxw]
      · exact hs
  · exact hs

private theorem foldl_hkBfsStep_inv {j : ℕ} {u : Fin m} (hu : u ∈ altLeft G (mateMatching mate) j)
    (l : List (Fin r)) {s : HKBfsState m} (hs : HKStepInv G (mateMatching mate) j s) :
    HKStepInv G (mateMatching mate) j (l.foldl (hkBfsStep G mate j u) s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons v l ih => exact ih (hkBfsStep_inv hu hs v)

/-- Later states keep `found` and all discovered layers. -/
private def HKStateLe (s s' : HKBfsState m) : Prop :=
  (s.found = true → s'.found = true) ∧ ∀ u i, vget s.dist u = some i → vget s'.dist u = some i

private theorem HKStateLe.refl (s : HKBfsState m) : HKStateLe s s := ⟨id, fun _ _ => id⟩

private theorem HKStateLe.trans {s₁ s₂ s₃ : HKBfsState m} (h₁ : HKStateLe s₁ s₂)
    (h₂ : HKStateLe s₂ s₃) : HKStateLe s₁ s₃ :=
  ⟨h₂.1 ∘ h₁.1, fun u i => h₂.2 u i ∘ h₁.2 u i⟩

private theorem hkBfsStep_le (j : ℕ) (u : Fin m) (s : HKBfsState m) (v : Fin r) :
    HKStateLe s (hkBfsStep G mate j u s v) := by
  unfold hkBfsStep
  split_ifs with hG
  · cases vget mate v with
    | none => exact ⟨fun _ => rfl, fun _ _ h => h⟩
    | some w =>
      dsimp only
      split_ifs with hd
      · refine ⟨id, fun x i hx => ?_⟩
        have hxw : x ≠ w := fun h => by rw [h, hd] at hx; exact nomatch hx
        simpa [vget_vset_ne _ _ hxw.symm] using hx
      · exact HKStateLe.refl s
  · exact HKStateLe.refl s

private theorem foldl_hkBfsStep_le (j : ℕ) (u : Fin m) (l : List (Fin r)) (s : HKBfsState m) :
    HKStateLe s (l.foldl (hkBfsStep G mate j u) s) := by
  induction l generalizing s with
  | nil => exact HKStateLe.refl s
  | cons v l ih => exact (hkBfsStep_le j u s v).trans (ih _)

/-- Every candidate edge of `u` has been processed in `s`. -/
private def HKStepDone (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (u : Fin m)
    (s : HKBfsState m) (l : List (Fin r)) : Prop :=
  ∀ v ∈ l, G (u, v) = true → (vget mate v = none → s.found = true) ∧
    ∀ w, vget mate v = some w → vget s.dist w ≠ none

private theorem HKStepDone.mono {u : Fin m} {s s' : HKBfsState m} {l : List (Fin r)}
    (h : HKStepDone G mate u s l) (hle : HKStateLe s s') : HKStepDone G mate u s' l := by
  intro v hv hG
  refine ⟨fun hm => hle.1 ((h v hv hG).1 hm), fun w hw hd => ?_⟩
  cases hs : vget s.dist w with
  | none => exact (h v hv hG).2 w hw hs
  | some i => rw [hle.2 w i hs] at hd; exact nomatch hd

private theorem foldl_hkBfsStep_done (j : ℕ) (u : Fin m) (l : List (Fin r)) (s : HKBfsState m) :
    HKStepDone G mate u (l.foldl (hkBfsStep G mate j u) s) l := by
  induction l generalizing s with
  | nil => intro v hv; simp at hv
  | cons v l ih =>
    intro x hx hG
    rcases List.mem_cons.mp hx with rfl | hx
    · refine HKStepDone.mono (l := [x]) (fun y hy hGy => ?_) (foldl_hkBfsStep_le j u l _) x
        List.mem_cons_self hG
      obtain rfl := List.mem_singleton.mp hy
      refine ⟨fun hm => by simp [hkBfsStep, hGy, hm], fun w hw => ?_⟩
      by_cases hd : vget s.dist w = none <;> simp [hkBfsStep, hGy, hw, hd]
    · exact ih _ x hx hG

end BfsLayer

/-! ### Breadth-first search: correctness -/

section BfsSpec

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)} {mate : Vector (Option (Fin m)) r}

private theorem layerFold_inv {j : ℕ} (us : List (Fin m))
    (hus : ∀ u ∈ us, u ∈ altLeft G (mateMatching mate) j) {s : HKBfsState m}
    (hs : HKStepInv G (mateMatching mate) j s) :
    HKStepInv G (mateMatching mate) j (hkBfsLayer G adj mate j us s) := by
  induction us generalizing s with
  | nil => exact hs
  | cons u us ih =>
    exact ih (fun x hx => hus x (List.mem_cons_of_mem _ hx))
      (foldl_hkBfsStep_inv (hus u List.mem_cons_self) (adj u) hs)

private theorem layerFold_le (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    HKStateLe s (hkBfsLayer G adj mate j us s) := by
  induction us generalizing s with
  | nil => exact HKStateLe.refl s
  | cons u us ih => exact (foldl_hkBfsStep_le j u (adj u) s).trans (ih _)

private theorem layerFold_done (j : ℕ) (us : List (Fin m)) (s : HKBfsState m) :
    ∀ u ∈ us, HKStepDone G mate u (hkBfsLayer G adj mate j us s) (adj u) := by
  induction us generalizing s with
  | nil => intro u hu; simp at hu
  | cons x us ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact (foldl_hkBfsStep_done j u (adj u) s).mono (layerFold_le j us _)
    · exact ih _ u hu

/-- After expanding the full layer-`j` frontier, every vertex of layer `j + 1` is discovered and
a free right vertex adjacent to layer `j` sets `found`. -/
private theorem layer_complete (hadj : BipAdjValid G adj) {j : ℕ} {frontier : List (Fin m)}
    (hfront : ∀ u, u ∈ frontier ↔ IsLayer G (mateMatching mate) u j)
    (hN : NoShortAug G (mateMatching mate) j) {s : HKBfsState m}
    (hs : HKStepInv G (mateMatching mate) j s)
    (hdone : ∀ u ∈ frontier, HKStepDone G mate u s (adj u)) :
    (∀ w, IsLayer G (mateMatching mate) w (j + 1) → w ∈ s.next) ∧
    (∀ t ∈ altRight G (mateMatching mate) j, t ∉ matchedRight (mateMatching mate) →
      s.found = true) := by
  refine ⟨fun w hw => ?_, fun t ht hfree => ?_⟩
  · rcases mem_altLeft_succ.mp hw.1 with h | ⟨v, hwv, hv⟩
    · exact absurd h (hw.2 j (Nat.lt_succ_self j))
    obtain ⟨u, hu, hG⟩ := mem_altRight.mp hv
    obtain ⟨i, hij, hui⟩ := exists_isLayer hu
    have hi : i = j := by_contra fun _ => hw.2 (i + 1) (by omega)
      (mem_altLeft_succ_of_mem hwv (mem_altRight_of_isLayer hui le_rfl hG))
    have hd := (hdone u ((hfront u).mpr (hi ▸ hui)) v (hadj u v hG) hG).2 w
      (mem_mateMatching.mp hwv)
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp hd
    rcases Nat.lt_or_eq_of_le (hs.bound w i' hi') with hlt | rfl
    · have := hw.unique ((hs.exact w i' (by omega)).mp hi')
      omega
    · exact (hs.next_iff w).mp hi'
  · obtain ⟨u, hu, hG⟩ := mem_altRight.mp ht
    obtain ⟨i, hij, hui⟩ := exists_isLayer hu
    have hi : i = j := by_contra fun _ =>
      hfree (hN i (by omega) (mem_altRight_of_isLayer hui le_rfl hG))
    exact (hdone u ((hfront u).mpr (hi ▸ hui)) t (hadj u t hG) hG).1
      (vget_mate_eq_none_iff.mpr hfree)

/-- Specification of a breadth-first layering result. -/
structure HKBfsSpec (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r))
    (b : HKBfsResult m) : Prop where
  noShort : NoShortAug G M b.k
  exact : ∀ u i, i ≤ b.k → (vget b.dist u = some i ↔ IsLayer G M u i)
  found_true : b.found = true → ∃ t ∈ altRight G M b.k, t ∉ matchedRight M
  found_false : b.found = false → altLeft G M (b.k + 1) = altLeft G M b.k ∧
    altRight G M b.k ⊆ matchedRight M ∧ ∀ u, vget b.dist u = none ↔ u ∉ altLeft G M b.k

end BfsSpec

section BfsLoop

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)} {mate : Vector (Option (Fin m)) r}

private theorem hkBfsLoop_spec (hadj : BipAdjValid G adj) (fuel : ℕ) {j : ℕ}
    {dist : Vector (Option ℕ) m} {frontier : List (Fin m)}
    (hex : ∀ u i, i ≤ j → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    (hbd : ∀ u i, vget dist u = some i → i ≤ j)
    (hfront : ∀ u, u ∈ frontier ↔ IsLayer G (mateMatching mate) u j) (hnd : frontier.Nodup)
    (hN : NoShortAug G (mateMatching mate) j)
    (hfuel : m < fuel + (altLeft G (mateMatching mate) j).card) :
    HKBfsSpec G (mateMatching mate) (hkBfsLoop G adj mate fuel j dist frontier) := by
  induction fuel generalizing j dist frontier with
  | zero =>
    have := (Finset.card_le_univ (altLeft G (mateMatching mate) j)).trans_eq (Fintype.card_fin m)
    omega
  | succ fuel ih =>
    have hs0 : HKStepInv G (mateMatching mate) j ⟨dist, [], false⟩ :=
      ⟨hex, fun u i h => Nat.le_succ_of_le (hbd u i h),
        fun u => ⟨fun h => (by have := hbd u _ h; omega), (nomatch ·)⟩,
        fun _ hu => absurd hu List.not_mem_nil, List.nodup_nil, (nomatch ·)⟩
    set s := hkBfsLayer G adj mate j frontier ⟨dist, [], false⟩ with hsdef
    have hs : HKStepInv G (mateMatching mate) j s :=
      layerFold_inv (adj := adj) frontier (fun u hu => ((hfront u).mp hu).1) hs0
    obtain ⟨hcomp, hfound⟩ := layer_complete hadj hfront hN hs
      (hsdef ▸ layerFold_done j frontier _)
    simp only [hkBfsLoop, ← hsdef]
    split_ifs with hf hne
    · exact ⟨hN, hs.exact, fun _ => hs.found hf, fun h => by simp at h⟩
    · have hnil : s.next = [] := List.isEmpty_iff.mp hne
      refine ⟨hN, hs.exact, fun h => by simp at h, fun _ => ⟨?_,
        fun t ht => by_contra fun hfree => hf (hfound t ht hfree), fun u => ⟨fun hd hu => ?_,
          fun hu => ?_⟩⟩⟩
      · refine Finset.Subset.antisymm (fun w hw => ?_) (altLeft_mono (Nat.le_succ j))
        obtain ⟨i, hij, hwi⟩ := exists_isLayer hw
        rcases Nat.lt_or_eq_of_le hij with _ | rfl
        · exact altLeft_mono (by omega) hwi.1
        · exact absurd (hcomp w hwi) (by simp [hnil])
      · obtain ⟨i, hij, hui⟩ := exists_isLayer hu
        simp [(hs.exact u i hij).mpr hui] at hd
      · cases hd : vget s.dist u with
        | none => rfl
        | some i =>
          rcases Nat.lt_or_eq_of_le (hs.bound u i hd) with hlt | rfl
          · exact absurd (altLeft_mono (Nat.lt_succ_iff.mp hlt)
              ((hs.exact u i (Nat.lt_succ_iff.mp hlt)).mp hd).1) hu
          · exact absurd ((hs.next_iff u).mp hd) (by simp [hnil])
    · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil s.next (fun h => hne (by simp [h]))
      have hwl := hs.next_layer w hw
      have hcard := Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr
        ⟨altLeft_mono (Nat.le_add_right j 1), fun h => hwl.2 j (Nat.lt_add_one j) (h ▸ hwl.1)⟩
      refine ih (fun u i hi => ?_) hs.bound (fun u => ⟨hs.next_layer u, hcomp u⟩) hs.nodup
        (fun j' hj' t ht => (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj')).elim
          (fun h => hN j' h ht) (fun h => by_contra fun hf' => hf (hfound t (h ▸ ht) hf')))
        (by omega)
      rcases Nat.lt_or_eq_of_le hi with _ | rfl
      · exact hs.exact u i (by omega)
      · exact ⟨fun h => hs.next_layer u ((hs.next_iff u).mp h),
          fun h => (hs.next_iff u).mpr (hcomp u h)⟩

theorem hkBfs_spec (hadj : BipAdjValid G adj) :
    HKBfsSpec G (mateMatching mate) (hkBfs G adj mate) := by
  unfold hkBfs
  set ml := hkMatchedLeft mate
  obtain ⟨h1, h2⟩ := bfsInit_foldl ml (List.finRange m) (Vector.replicate m none, [])
  have hml : ∀ u, vget ml u = false ↔ IsLayer G (mateMatching mate) u 0 := fun u => by
    rw [isLayer_zero, ← hkMatchedLeft_spec mate u]
    simp [ml]
  refine hkBfsLoop_spec hadj (m + 1)
    (fun u i hi => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; simp [h1 u, ← hml u])
    (fun u i h => by rw [h1 u] at h; split_ifs at h <;> simp_all)
    (fun u => by simp [h2 u, ← hml u])
    (bfsInit_nodup ml _ _ (List.nodup_finRange m) List.nodup_nil (by simp))
    (fun _ hj => absurd hj (Nat.not_lt_zero _)) (by omega)

private theorem hkBfsLoop_k_le (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (fuel j : ℕ) (dist : Vector (Option ℕ) m)
    (frontier : List (Fin m)) :
    (hkBfsLoop G adj mate fuel j dist frontier).k ≤ j + fuel := by
  induction fuel generalizing j dist frontier with
  | zero => simp [hkBfsLoop]
  | succ fuel ih =>
    simp only [hkBfsLoop]
    split_ifs
    exacts [Nat.le_add_right _ _, Nat.le_add_right _ _, (ih (j + 1) _ _).trans (by omega)]

theorem hkBfs_k_le (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) :
    (hkBfs G adj mate).k ≤ m + 1 := by
  simpa [hkBfs] using hkBfsLoop_k_le G adj mate (m + 1) 0 _ _

theorem bfsInit_potential (ml : Vector Bool m) (c : Fin m → ℕ) (l : List (Fin m))
    (p : Vector (Option ℕ) m × List (Fin m)) :
    vecPotential (· = none) c (l.foldl (hkBfsInitStep ml) p).1 +
        ((l.foldl (hkBfsInitStep ml) p).2.map c).sum ≤
      vecPotential (· = none) c p.1 + (p.2.map c).sum + (l.map c).sum := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    refine (ih (hkBfsInitStep ml p x)).trans ?_
    simp only [hkBfsInitStep, List.map_cons, List.sum_cons]
    split_ifs
    · omega
    · have := vecPotential_vset_le (p := (· = none)) (c := c) p.1 x (x := some 0) (by simp)
      simp; omega

private theorem hkBfsStep_potential (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r)
    (c : Fin m → ℕ) (j : ℕ) (u : Fin m) (s : HKBfsState m) (v : Fin r) :
    vecPotential (· = none) c (hkBfsStep G mate j u s v).dist +
        ((hkBfsStep G mate j u s v).next.map c).sum =
      vecPotential (· = none) c s.dist + (s.next.map c).sum := by
  unfold hkBfsStep
  cases vget mate v with
  | none => split_ifs <;> rfl
  | some w =>
    dsimp only
    split_ifs with hG hd
    · have := vecPotential_vset_add (c := c) (p := (· = none)) (t := s.dist)
        (x := some (j + 1)) hd (by simp)
      simp; omega
    all_goals rfl

theorem layerFold_potential (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (c : Fin m → ℕ) (j : ℕ) (us : List (Fin m))
    (s : HKBfsState m) :
    vecPotential (· = none) c (hkBfsLayer G adj mate j us s).dist +
        ((hkBfsLayer G adj mate j us s).next.map c).sum =
      vecPotential (· = none) c s.dist + (s.next.map c).sum := by
  unfold hkBfsLayer
  induction us generalizing s with
  | nil => rfl
  | cons u _ ih =>
    rw [List.foldl_cons, ih]
    induction adj u generalizing s with
    | nil => rfl
    | cons _ _ ihl => rw [List.foldl_cons, ihl, hkBfsStep_potential]

end BfsLoop

/-! ### Depth-first search: correctness -/

section DfsSpec

variable {G : Fin m × Fin r → Bool} {M : Finset (Fin m × Fin r)} {k : ℕ}

/-- A layered path through the candidate edge `(u, v)`. -/
private theorem IsLayeredPath.cons_cases {U : Finset (Fin r)} {u : Fin m} {v : Fin r} {i : ℕ}
    {q : List (Fin m × Fin r)} (h : IsLayeredPath G M U k u i ((u, v) :: q)) :
    G (u, v) = true ∧ v ∉ U ∧ ((i = k ∧ v ∉ matchedRight M) ∨
      ∃ w, (w, v) ∈ M ∧ IsLayeredPath G M U k w (i + 1) q) := by
  cases h with
  | last _ hG hv hU => exact ⟨hG, hU, .inl ⟨rfl, hv⟩⟩
  | cons _ hG hM hU hp => exact ⟨hG, hU, .inr ⟨_, hM, hp⟩⟩

/-- The right vertex `v` is matched to a left vertex from which no layered path avoids `U`. -/
private def HKDead (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (U : Finset (Fin r))
    (k : ℕ) (v : Fin r) : Prop :=
  ∃ w, (w, v) ∈ M ∧ ∀ i q, ¬ IsLayeredPath G M U k w i q

private theorem HKDead.mono {U U' : Finset (Fin r)} (hU : U ⊆ U') {v : Fin r}
    (h : HKDead G M U k v) : HKDead G M U' k v :=
  let ⟨w, hw, h⟩ := h; ⟨w, hw, fun i q hq => h i q (hq.mono hU)⟩

/-- Visited-table invariant of the depth-first search for accumulated paths `acc` and the right
vertices `S` on the current search stack. -/
private structure HKVisInv (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k : ℕ)
    (acc : List (Fin m × Fin r)) (S : Finset (Fin r)) (vis : Vector Bool r) : Prop where
  acc_vis : ∀ v ∈ matchedRight acc.toFinset, vget vis v = true
  vis_cases : ∀ v, vget vis v = true →
    v ∈ matchedRight acc.toFinset ∨ v ∈ S ∨ HKDead G M (matchedRight acc.toFinset) k v

/-- Visited tables only grow. -/
private def HKVisLe (vis vis' : Vector Bool r) : Prop := ∀ v, vget vis v = true → vget vis' v = true

private theorem HKVisLe.vset (vis : Vector Bool r) (v : Fin r) : HKVisLe vis (vset vis v true) :=
  fun x hx => (eq_or_ne x v).elim (· ▸ vget_vset_self vis v true)
    fun h => by rwa [vget_vset_ne vis true h.symm]

/-- A layered path whose first edge ends at a right vertex `v` matched to `w` continues with a
layered path from `w` in the next layer. -/
private theorem IsLayeredPath.of_mate {mate : Vector (Option (Fin m)) r} {U : Finset (Fin r)}
    {u w : Fin m} {v : Fin r} {i : ℕ} {q : List (Fin m × Fin r)} (hw : (w, v) ∈ mateMatching mate)
    (h : IsLayeredPath G (mateMatching mate) U k u i ((u, v) :: q)) :
    IsLayeredPath G (mateMatching mate) U k w (i + 1) q := by
  rcases h.cons_cases.2.2 with ⟨_, hfree⟩ | ⟨w', hw', hp⟩
  · exact absurd (mem_matchedRight.mpr ⟨w, hw⟩) hfree
  · obtain rfl : w = w' := Option.some.inj ((mem_mateMatching.mp hw).symm.trans
      (mem_mateMatching.mp hw'))
    exact hp

/-- Marking `v` visited while pushing it on the search stack preserves the visited invariant. -/
private theorem HKVisInv.push {acc : List (Fin m × Fin r)} {S : Finset (Fin r)}
    {vis : Vector Bool r} (h : HKVisInv G M k acc S vis) (v : Fin r) :
    HKVisInv G M k acc (insert v S) (vset vis v true) := by
  refine ⟨fun x hx => HKVisLe.vset vis v x (h.acc_vis x hx), fun x hx => ?_⟩
  rcases eq_or_ne x v with rfl | hxv
  · exact .inr (.inl (Finset.mem_insert_self _ _))
  · rw [vget_vset_ne vis true hxv.symm] at hx
    exact (h.vis_cases x hx).imp_right (Or.imp_left Finset.mem_insert_of_mem)

/-- Prepending a visited edge `(u, v)` to the accumulated paths moves `v` from the search stack
to the matched vertices. -/
private theorem HKVisInv.cons {acc : List (Fin m × Fin r)} {S : Finset (Fin r)}
    {vis : Vector Bool r} {u : Fin m} {v : Fin r} (h : HKVisInv G M k acc (insert v S) vis)
    (hv : vget vis v = true) : HKVisInv G M k ((u, v) :: acc) S vis := by
  have hsub : matchedRight acc.toFinset ⊆ matchedRight ((u, v) :: acc).toFinset := by
    simp only [matchedRight, List.toFinset_cons]
    exact Finset.image_subset_image (Finset.subset_insert _ _)
  refine ⟨fun x hx => ((by simpa [matchedRight] using hx : x = v ∨ _).elim (· ▸ hv) (h.acc_vis x)),
    fun x hx => (h.vis_cases x hx).elim (fun hx => .inl (hsub hx)) fun hx => hx.elim
      (fun hx => (Finset.mem_insert.mp hx).elim (· ▸ .inl (by simp [matchedRight])) (.inr ∘ .inl))
      fun hx => .inr (.inr (hx.mono hsub))⟩

/-- Popping `v` from the search stack after the scan from its mate `w` in layer `j` found no
layered path preserves the visited invariant: `v` is now dead. -/
private theorem HKVisInv.pop {mate : Vector (Option (Fin m)) r} {acc : List (Fin m × Fin r)}
    {S : Finset (Fin r)} {vis : Vector Bool r} {w : Fin m} {v : Fin r} {j : ℕ}
    (h : HKVisInv G (mateMatching mate) k acc (insert v S) vis) (hw : (w, v) ∈ mateMatching mate)
    (hwl : IsLayer G (mateMatching mate) w j)
    (hblk : ∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k w j q) :
    HKVisInv G (mateMatching mate) k acc S vis :=
  ⟨h.acc_vis, fun x hx => (h.vis_cases x hx).imp_right fun hx => hx.elim
    (fun h => (Finset.mem_insert.mp h).elim
      (fun heq => .inr ⟨w, heq ▸ hw, fun _ q hq => by
        subst heq; cases hwl.unique hq.isLayer; exact hblk q hq⟩) .inl)
    .inr⟩

/-- Postcondition of a depth-first scan from `u` in layer `i`. On success the found path is
prepended to `acc`; on failure `blocked` holds. -/
private structure HKDfsPost (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k : ℕ)
    (u : Fin m) (i : ℕ) (acc : List (Fin m × Fin r)) (S : Finset (Fin r)) (vis : Vector Bool r)
    (blocked : Prop) (res : Vector Bool r × Option (List (Fin m × Fin r))) : Prop where
  le : HKVisLe vis res.1
  found : ∀ p, res.2 = some p → ∃ q, p = q ++ acc ∧
    IsLayeredPath G M (matchedRight acc.toFinset) k u i q ∧ HKVisInv G M k p S res.1
  fail : res.2 = none → HKVisInv G M k acc S res.1 ∧ blocked

/-- Skipping a candidate `v` from which no layered path through `(u, v)` exists, and then
scanning the rest `vs` from a larger visited table, satisfies the postcondition for `v :: vs`. -/
private theorem HKDfsPost.skip {u : Fin m} {i : ℕ} {acc : List (Fin m × Fin r)}
    {S : Finset (Fin r)} {vis vis' : Vector Bool r} {v : Fin r} {vs : List (Fin r)}
    {res : Vector Bool r × Option (List (Fin m × Fin r))}
    (h : HKDfsPost G M k u i acc S vis'
      (∀ v' ∈ vs, ∀ q, ¬ IsLayeredPath G M (matchedRight acc.toFinset) k u i ((u, v') :: q)) res)
    (hle : HKVisLe vis vis')
    (hv : ∀ q, ¬ IsLayeredPath G M (matchedRight acc.toFinset) k u i ((u, v) :: q)) :
    HKDfsPost G M k u i acc S vis
      (∀ v' ∈ v :: vs, ∀ q, ¬ IsLayeredPath G M (matchedRight acc.toFinset) k u i ((u, v') :: q))
      res :=
  ⟨fun x hx => h.le x (hle x hx), h.found, fun hn => ⟨(h.fail hn).1, fun v' hv' =>
    (List.mem_cons.mp hv').elim (· ▸ hv) ((h.fail hn).2 v')⟩⟩

/-- Right vertices on the search stack are matched to left vertices of layers `≤ i`. -/
private def HKStackOK (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (S : Finset (Fin r))
    (i : ℕ) : Prop :=
  ∀ v ∈ S, ∃ w j, (w, v) ∈ M ∧ IsLayer G M w j ∧ j ≤ i

/-- Pushing the right vertex `v`, matched to `w` in layer `i + 1`, keeps the stack invariant one
layer down. -/
private theorem HKStackOK.insert {S : Finset (Fin r)} {i : ℕ} {w : Fin m} {v : Fin r}
    (hS : HKStackOK G M S i) (hw : (w, v) ∈ M) (hwl : IsLayer G M w (i + 1)) :
    HKStackOK G M (insert v S) (i + 1) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨w, i + 1, hw, hwl, le_rfl⟩
  · obtain ⟨w', j, h1, h2, h3⟩ := hS x hx
    exact ⟨w', j, h1, h2, by omega⟩

/-- Specification of a depth-first search procedure from layer `i`. -/
private def HKDfsSpec (G : Fin m × Fin r → Bool) (M : Finset (Fin m × Fin r)) (k i : ℕ)
    (dfs : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))) : Prop :=
  ∀ u vis acc S, IsLayer G M u i → HKStackOK G M S i → HKVisInv G M k acc S vis →
    HKDfsPost G M k u i acc S vis (∀ q, ¬ IsLayeredPath G M (matchedRight acc.toFinset) k u i q)
      (dfs u vis acc)

end DfsSpec

section DfsLevel

variable {G : Fin m × Fin r → Bool} {mate : Vector (Option (Fin m)) r}
  {dist : Vector (Option ℕ) m} {k : ℕ}

private theorem hkDfsLevel_post
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    {accept : Bool} {i : ℕ} (hik : i ≤ k) (hacc : accept = true ↔ i = k)
    {next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))}
    (hnext : accept = false → HKDfsSpec G (mateMatching mate) k (i + 1) next)
    {u : Fin m} (hu : IsLayer G (mateMatching mate) u i) {acc : List (Fin m × Fin r)}
    {S : Finset (Fin r)} (hS : HKStackOK G (mateMatching mate) S i) (vs : List (Fin r)) :
    ∀ vis, HKVisInv G (mateMatching mate) k acc S vis →
    HKDfsPost G (mateMatching mate) k u i acc S vis
      (∀ v ∈ vs, ∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k u i
        ((u, v) :: q))
      (hkDfsLevel G mate dist accept i next u vs vis acc) := by
  induction vs with
  | nil => exact fun vis hinv => ⟨fun _ => id, fun _ hp => (nomatch hp),
      fun _ => ⟨hinv, fun _ hv => nomatch hv⟩⟩
  | cons v vs ih =>
    intro vis hinv
    simp only [hkDfsLevel]
    split
    · next hc =>
      have hvU : v ∉ matchedRight acc.toFinset := fun h =>
        Bool.false_ne_true (hc.2.symm.trans (hinv.acc_vis v h))
      cases hm : vget mate v with
      | none =>
        dsimp only
        split
        · next ha =>
          obtain rfl : i = k := hacc.mp ha
          exact ⟨HKVisLe.vset vis v, fun p hp => Option.some.inj hp ▸
            ⟨[(u, v)], rfl, .last hu hc.1 (vget_mate_eq_none_iff.mp hm) hvU,
              (hinv.push v).cons (vget_vset_self vis _ true)⟩, fun hp => nomatch hp⟩
        · next ha =>
          exact (ih vis hinv).skip (fun _ => id) fun _ hq =>
            hq.cons_cases.2.2.elim (fun h => ha (hacc.mpr h.1)) fun ⟨_, hw, _⟩ => by
              simp [mem_mateMatching, hm] at hw
      | some w =>
        have hwM : (w, v) ∈ mateMatching mate := mem_mateMatching.mpr hm
        dsimp only
        split
        · next hb =>
          have hwl : IsLayer G (mateMatching mate) w (i + 1) := (hex w (i + 1)
            (lt_of_le_of_ne hik fun h => Bool.false_ne_true
              (hb.1.symm.trans (hacc.mpr h)))).mp hb.2
          have hspec := hnext hb.1 w (vset vis v true) acc (insert v S) hwl (hS.insert hwM hwl)
            (hinv.push v)
          generalize next w (vset vis v true) acc = res at hspec ⊢
          rcases res with ⟨vis', _ | p'⟩
          · obtain ⟨hinv1, hblk⟩ := hspec.fail rfl
            exact (ih vis' (hinv1.pop hwM hwl hblk)).skip
              (fun x hx => hspec.le x (HKVisLe.vset vis v x hx))
              fun q hq => hblk q (hq.of_mate hwM)
          · obtain ⟨q, rfl, hqpath, hqinv⟩ := hspec.found p' rfl
            exact ⟨fun x hx => hspec.le x (HKVisLe.vset vis v x hx),
              fun _ hp => Option.some.inj hp ▸ ⟨(u, v) :: q, rfl, .cons hu hc.1 hwM hvU hqpath,
                hqinv.cons (hspec.le _ (vget_vset_self vis _ true))⟩, fun hp => nomatch hp⟩
        · next hb =>
          refine (ih vis hinv).skip (fun _ => id) fun _ hq => ?_
          have hp := hq.of_mate hwM
          exact hb ⟨Bool.eq_false_iff.mpr fun ha => by have := hacc.mp ha; have := hp.le; omega,
            (hex w (i + 1) hp.le).mpr hp.isLayer⟩
    · next hc =>
      refine (ih vis hinv).skip (fun _ => id) fun q hq => ?_
      obtain ⟨hG, hU, -⟩ := hq.cons_cases
      rcases hinv.vis_cases v (Bool.of_not_eq_false fun h => hc ⟨hG, h⟩) with
        h | h | ⟨w, hw, hdead⟩
      · exact hU h
      · obtain ⟨w, j, hw, hwl, _⟩ := hS v h
        have := hwl.unique (hq.of_mate hw).isLayer
        omega
      · exact hdead _ q (hq.of_mate hw)

end DfsLevel

section DfsDriver

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
  {mate : Vector (Option (Fin m)) r} {dist : Vector (Option ℕ) m} {k : ℕ}

private theorem HKDfsPost.weaken {M : Finset (Fin m × Fin r)} {u : Fin m} {i : ℕ}
    {acc : List (Fin m × Fin r)} {S : Finset (Fin r)} {vis : Vector Bool r} {P Q : Prop}
    {res : Vector Bool r × Option (List (Fin m × Fin r))}
    (h : HKDfsPost G M k u i acc S vis P res) (hPQ : P → Q) :
    HKDfsPost G M k u i acc S vis Q res :=
  ⟨h.le, h.found, fun hn => ⟨(h.fail hn).1, hPQ (h.fail hn).2⟩⟩

private theorem hkDfs_spec (hadj : BipAdjValid G adj)
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    ∀ f i, f + i = k → HKDfsSpec G (mateMatching mate) k i (hkDfs G adj mate dist f i) := by
  have blocked : ∀ {u : Fin m} {i : ℕ} {U : Finset (Fin r)},
      (∀ v ∈ adj u, ∀ q, ¬ IsLayeredPath G (mateMatching mate) U k u i ((u, v) :: q)) →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate) U k u i q := by
    intro u i U h q hq
    obtain ⟨v, l, rfl⟩ := hq.head
    exact h v (hadj u v hq.cons_cases.1) l hq
  intro f
  induction f with
  | zero =>
    exact fun i hi u vis acc S hu hS hinv =>
      (hkDfsLevel_post (accept := true) hex (Nat.le_of_eq (Nat.zero_add i ▸ hi))
        (iff_of_true rfl (Nat.zero_add i ▸ hi)) (fun h => nomatch h) hu hS (adj u) vis
        hinv).weaken blocked
  | succ f ih =>
    exact fun i hi u vis acc S hu hS hinv =>
      (hkDfsLevel_post (accept := false) hex (Nat.le_trans (Nat.le_add_left _ _) hi.le)
        (iff_of_false Bool.false_ne_true (by omega))
        (fun _ => ih (i + 1) (by omega)) hu hS (adj u) vis hinv).weaken blocked

private theorem hkDfsRoots_spec (hadj : BipAdjValid G adj)
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i))
    (us : List (Fin m)) (hnd : us.Nodup) :
    ∀ vis acc, IsLayeredFamily G (mateMatching mate) k acc →
    HKVisInv G (mateMatching mate) k acc ∅ vis →
    (∀ y ∈ us, IsLayer G (mateMatching mate) y 0 → y ∉ matchedLeft acc.toFinset) →
    (∀ y, y ∉ us → y ∉ matchedLeft acc.toFinset →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate) (matchedRight acc.toFinset) k y 0 q) →
    IsLayeredFamily G (mateMatching mate) k (hkDfsRoots G adj mate dist k us vis acc) ∧
    ∀ y, y ∉ matchedLeft (hkDfsRoots G adj mate dist k us vis acc).toFinset →
      ∀ q, ¬ IsLayeredPath G (mateMatching mate)
        (matchedRight (hkDfsRoots G adj mate dist k us vis acc).toFinset) k y 0 q := by
  induction us with
  | nil => exact fun _ _ hfam _ _ hmax => ⟨hfam, fun y => hmax y List.not_mem_nil⟩
  | cons x us ih =>
    intro vis acc hfam hinv hroots hmax
    obtain ⟨hxus, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [hkDfsRoots]
    split_ifs with hd
    · have hx0 := (hex x 0 (Nat.zero_le _)).mp hd
      have hspec := hkDfs_spec hadj hex k 0 (by omega) x vis acc ∅ hx0 (by simp [HKStackOK]) hinv
      generalize hkDfs G adj mate dist k 0 x vis acc = res at hspec ⊢
      rcases res with ⟨vis', _ | p⟩
      · obtain ⟨hinv', hblk⟩ := hspec.fail rfl
        exact ih hnd' vis' acc hfam hinv' (fun y hy => hroots y (List.mem_cons_of_mem _ hy))
          fun y hy hyacc => (eq_or_ne y x).elim (· ▸ hblk) fun hyx =>
            hmax y (fun h => (List.mem_cons.mp h).elim hyx hy) hyacc
      · obtain ⟨q, rfl, hq, hinv'⟩ := hspec.found p rfl
        have hsub : acc.toFinset ⊆ (q ++ acc).toFinset := by
          simp only [List.toFinset_append]
          exact Finset.subset_union_right
        have hxacc : x ∉ acc.map Prod.fst := fun h => hroots x List.mem_cons_self hx0
          (by simpa [matchedLeft] using h)
        refine ih hnd' vis' (q ++ acc) (.cons hfam hxacc hq) hinv' (fun y hy hy0 hyacc => ?_)
          fun y hy hyacc => ?_
        · rcases Finset.mem_image.mp hyacc with ⟨e, he, rfl⟩
          rcases List.mem_append.mp (List.mem_toFinset.mp he) with he | he
          · rcases hq.mem_left e he with h | ⟨_, _, hM'⟩
            · exact hxus (h ▸ hy)
            · exact (isLayer_zero.mp hy0) (mem_matchedLeft.mpr ⟨_, hM'⟩)
          · exact hroots e.1 (List.mem_cons_of_mem _ hy) hy0
              (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr he))
        · rcases eq_or_ne y x with rfl | hyx
          · obtain ⟨v, _, rfl⟩ := hq.head
            exact absurd (mem_matchedLeft.mpr ⟨v, by simp⟩) hyacc
          · exact fun p hp => hmax y (fun h => (List.mem_cons.mp h).elim hyx hy)
              (fun h => hyacc (Finset.image_subset_image hsub h)) p
              (hp.mono (Finset.image_subset_image hsub))
    · exact ih hnd' vis acc hfam hinv (fun y hy => hroots y (List.mem_cons_of_mem _ hy))
        fun y hy hyacc => (eq_or_ne y x).elim
          (fun h q hq => hd ((hex x 0 (Nat.zero_le _)).mpr (h ▸ hq.isLayer)))
          fun hyx => hmax y (fun h => (List.mem_cons.mp h).elim hyx hy) hyacc

/-- The edge list found by one phase is a maximal layered augmentation. -/
private theorem hkDfsRoots_maximal (hadj : BipAdjValid G adj)
    (hM : IsMatching G (mateMatching mate))
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    IsLayeredFamily G (mateMatching mate) k
      (hkDfsRoots G adj mate dist k (List.finRange m) (Vector.replicate r false) []) ∧
    IsMaximalLayeredAugmentation G (mateMatching mate)
      (hkDfsRoots G adj mate dist k (List.finRange m) (Vector.replicate r false) []).toFinset
      k := by
  have h := hkDfsRoots_spec hadj hex (List.finRange m) (List.nodup_finRange m)
    (Vector.replicate r false) [] .nil
    ⟨fun _ hv => by simp [matchedRight] at hv, fun _ hv => by
      simp only [vget_replicate] at hv; exact nomatch hv⟩
    (fun _ _ _ => by simp [matchedLeft]) (fun y hy => absurd (List.mem_finRange y) hy)
  exact ⟨h.1, h.1.isMaximalLayeredAugmentation hM h.2⟩

end DfsDriver

section ApplyEdges

/-- Rematching along an edge list with distinct right ends: `v` is matched to `u` afterwards iff
`(u, v)` is in the list, or `v` is not rematched and was matched to `u` before. -/
theorem vget_foldl_apply (mate : Vector (Option (Fin m)) r) (es : List (Fin m × Fin r))
    (hnd : (es.map Prod.snd).Nodup) (u : Fin m) (v : Fin r) :
    vget (es.foldl (fun mt e => vset mt e.2 (some e.1)) mate) v = some u ↔
      (u, v) ∈ es ∨ (v ∉ es.map Prod.snd ∧ vget mate v = some u) := by
  induction es generalizing mate with
  | nil => simp
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    obtain ⟨hb, hnd'⟩ := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    rw [List.foldl_cons, ih _ hnd']
    rcases eq_or_ne v b with rfl | hvb
    · have hne : (u, v) ∉ es := fun h => hb (List.mem_map.mpr ⟨_, h, rfl⟩)
      simp [hb, hne, eq_comm]
    · simp [vget_vset_ne mate _ hvb.symm, hvb]

/-- Two edge lists with distinct right ends and the same edge set induce the same mate table. -/
theorem hkApplyEdges_eq_of_toFinset_eq (mate : Vector (Option (Fin m)) r)
    {es₁ es₂ : List (Fin m × Fin r)}
    (hnd₁ : (es₁.map Prod.snd).Nodup) (hnd₂ : (es₂.map Prod.snd).Nodup)
    (heq : es₁.toFinset = es₂.toFinset) :
    hkApplyEdges mate es₁ = hkApplyEdges mate es₂ := by
  ext j hj u
  let v : Fin r := ⟨j, hj⟩
  change vget (hkApplyEdges mate es₁) v = some u ↔ vget (hkApplyEdges mate es₂) v = some u
  rw [hkApplyEdges, hkApplyEdges, vget_foldl_apply mate es₁ hnd₁, vget_foldl_apply mate es₂ hnd₂]
  have hmem (w : Fin m) : (w, v) ∈ es₁ ↔ (w, v) ∈ es₂ := by
    simpa using Finset.ext_iff.mp heq (w, v)
  simp [Prod.exists, hmem]

/-- Rematching a mate table along a compatible edge list realizes `augment`. -/
theorem mateMatching_applyEdges (mate : Vector (Option (Fin m)) r)
    (es : List (Fin m × Fin r))
    (hnd : (es.map Prod.snd).Nodup)
    (hcompat : ∀ u v, (u, v) ∈ mateMatching mate →
      (u ∈ matchedLeft es.toFinset ↔ v ∈ matchedRight es.toFinset)) :
    mateMatching (es.foldl (fun mt e => vset mt e.2 (some e.1)) mate) =
      augment (mateMatching mate) es.toFinset := by
  ext ⟨u, v⟩
  rw [mem_mateMatching, vget_foldl_apply mate es hnd, mem_augment, List.mem_toFinset,
    mem_mateMatching]
  have hv : v ∈ es.map Prod.snd ↔ v ∈ matchedRight es.toFinset := by simp [matchedRight]
  exact or_congr_right
    ⟨fun ⟨h1, h2⟩ => ⟨h2, fun hu => h1 (hv.mpr ((hcompat u v (mem_mateMatching.mpr h2)).mp hu))⟩,
     fun ⟨h1, h2⟩ => ⟨fun h => h2 ((hcompat u v (mem_mateMatching.mpr h1)).mpr (hv.mp h)), h1⟩⟩

end ApplyEdges

/-! ### One phase and phase loop -/

section Phase

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}
  {mate : Vector (Option (Fin m)) r} {dist : Vector (Option ℕ) m} {k : ℕ}

theorem hkPhase_spec (hadj : BipAdjValid G adj) (hM : IsMatching G (mateMatching mate))
    (hex : ∀ u i, i ≤ k → (vget dist u = some i ↔ IsLayer G (mateMatching mate) u i)) :
    ∃ N, IsMaximalLayeredAugmentation G (mateMatching mate) N k ∧
      mateMatching (hkPhase G adj mate dist k) = augment (mateMatching mate) N := by
  obtain ⟨hfam, hmax⟩ := hkDfsRoots_maximal (dist := dist) hadj hM hex
  exact ⟨_, hmax, mateMatching_applyEdges mate _ (hfam.nodup_right hM) hmax.compat⟩

end Phase

section Loop

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}

/-- Postcondition of the phase loop started with phase counter `n` from `mate`. -/
structure HKLoopPost (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) (n : ℕ)
    (res : HKLoopResult m r) : Prop where
  isMatching : IsMatching G (mateMatching res.mate)
  le_phases : n ≤ res.phases
  run : IsPhaseRun G (mateMatching mate) (res.phases - n)
  closed : ∃ k, altLeft G (mateMatching res.mate) (k + 1) = altLeft G (mateMatching res.mate) k ∧
    altRight G (mateMatching res.mate) k ⊆ matchedRight (mateMatching res.mate) ∧
    ∀ u, vget res.dist u = none ↔ u ∉ altLeft G (mateMatching res.mate) k

theorem hkLoop_spec (hadj : BipAdjValid G adj) :
    ∀ fuel n (mate : Vector (Option (Fin m)) r), IsMatching G (mateMatching mate) →
      m < fuel + (mateMatching mate).card →
      HKLoopPost G mate n (hkLoop G adj fuel n mate) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ mate hM _
    have : (mateMatching mate).card ≤ m := by simpa using hM.card_le_card_left
    omega
  | succ fuel ih =>
    intro n mate hM hfuel
    have hb := hkBfs_spec (G := G) (adj := adj) (mate := mate) hadj
    simp only [hkLoop]
    set b := hkBfs G adj mate
    split_ifs with hf
    · obtain ⟨N, hN, hmate'⟩ := hkPhase_spec (dist := b.dist) hadj hM hb.exact
      obtain ⟨t, ht, hfree⟩ := hb.found_true hf
      have hM' : IsMatching G (mateMatching (hkPhase G adj mate b.dist b.k)) :=
        hmate' ▸ hN.isMatching_augment hM
      have hlt : (mateMatching mate).card <
          (mateMatching (hkPhase G adj mate b.dist b.k)).card :=
        hmate' ▸ hN.card_lt_card_augment_of_mem_altRight hM hb.noShort ht hfree
      have hpost := ih (n + 1) _ hM' (by omega)
      have hle := hpost.le_phases
      refine ⟨hpost.isMatching, by omega, ?_, hpost.closed⟩
      rw [← Nat.sub_add_cancel (Nat.sub_pos_of_lt hle), Nat.sub_sub]
      exact .step hb.noShort ht hfree hN (hmate' ▸ hpost.run)
    · obtain ⟨hstable, hsub, hdist⟩ := hb.found_false (Bool.eq_false_iff.mpr hf)
      exact ⟨hM, le_rfl, Nat.sub_self n ▸ .done, b.k, hstable, hsub, hdist⟩

end Loop

/-! ### Exact filtered adjacency equivalence -/

section ExactAdj

private theorem foldl_filter_of_id {α β : Type*} (step : α → β → α) (p : β → Bool)
    (hid : ∀ s x, p x = false → step s x = s) (xs : List β) (s : α) :
    (xs.filter p).foldl step s = xs.foldl step s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x
    · rw [List.filter_cons_of_neg (by simp [hp]), List.foldl_cons, hid s x hp, ih]
    · rw [List.filter_cons_of_pos hp, List.foldl_cons, List.foldl_cons, ih]

private theorem hkBfs_exactBipAdj (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r) :
    hkBfs G (exactBipAdj G) mate = hkBfs G (denseBipAdj m r) mate := by
  have hlayer (j us s) :
      hkBfsLayer G (exactBipAdj G) mate j us s = hkBfsLayer G (denseBipAdj m r) mate j us s :=
    congrArg (List.foldl · s us) (funext fun _ => funext fun _ =>
      foldl_filter_of_id _ _ (fun _ _ hG => by simp [hkBfsStep, hG]) _ _)
  have hloop (fuel) : ∀ j dist frontier,
      hkBfsLoop G (exactBipAdj G) mate fuel j dist frontier =
        hkBfsLoop G (denseBipAdj m r) mate fuel j dist frontier := by
    induction fuel with
    | zero => exact fun _ _ _ => rfl
    | succ fuel ih =>
      intro j dist frontier
      simp only [hkBfsLoop, hlayer]
      split_ifs <;> [rfl; rfl; exact ih ..]
  simp only [hkBfs, hloop]

private theorem hkDfsLevel_filter (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (accept : Bool) (i : ℕ)
    (next₁ next₂ : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r)))
    (hnext : next₁ = next₂) (u : Fin m) (vs : List (Fin r))
    (vis : Vector Bool r) (acc : List (Fin m × Fin r)) :
    hkDfsLevel G mate dist accept i next₁ u (vs.filter fun v => G (u, v)) vis acc =
      hkDfsLevel G mate dist accept i next₂ u vs vis acc := by
  subst hnext
  induction vs generalizing vis acc with
  | nil => rfl
  | cons v vs ih =>
    cases hG : G (u, v)
    · rw [List.filter_cons_of_neg (by simp [hG])]
      simp [hkDfsLevel, hG, ih]
    · rw [List.filter_cons_of_pos (p := fun v => G (u, v)) hG]
      simp only [hkDfsLevel, hG, true_and, ih]

private theorem hkPhase_exactBipAdj (G : Fin m × Fin r → Bool) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (k : ℕ) :
    hkPhase G (exactBipAdj G) mate dist k = hkPhase G (denseBipAdj m r) mate dist k := by
  have hdfs (f) : ∀ i, hkDfs G (exactBipAdj G) mate dist f i =
      hkDfs G (denseBipAdj m r) mate dist f i := by
    induction f with
    | zero => exact fun i => funext fun u => funext fun vis => funext fun acc =>
        hkDfsLevel_filter G mate dist true i _ _ rfl u (List.finRange r) vis acc
    | succ f ih => exact fun i => funext fun u => funext fun vis => funext fun acc =>
        hkDfsLevel_filter G mate dist false i _ _ (ih (i + 1)) u (List.finRange r) vis acc
  have hroots (us) : ∀ vis acc,
      hkDfsRoots G (exactBipAdj G) mate dist k us vis acc =
        hkDfsRoots G (denseBipAdj m r) mate dist k us vis acc := by
    induction us with
    | nil => exact fun _ _ => rfl
    | cons u us ih =>
      intro vis acc
      simp only [hkDfsRoots, hdfs]
      split_ifs <;> exact ih ..
  simp only [hkPhase, hroots]

/-- Running `hopcroftKarp` on exact filtered neighbour lists `exactBipAdj G` produces the exact
same output as `hopcroftKarpDense G`. -/
theorem hopcroftKarp_exactBipAdj (G : Fin m × Fin r → Bool) :
    hopcroftKarp G (exactBipAdj G) = hopcroftKarpDense G := by
  have hloop (fuel) : ∀ n mate,
      hkLoop G (exactBipAdj G) fuel n mate = hkLoop G (denseBipAdj m r) fuel n mate := by
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro n mate
      simp only [hkLoop, hkBfs_exactBipAdj, hkPhase_exactBipAdj]
      split_ifs <;> [exact ih ..; rfl]
  simp only [hopcroftKarpDense, hopcroftKarp, hloop]

end ExactAdj

/-! ### Extraction and main theorems -/

section Extract

/-- Membership in the matching extracted from a mate table. -/
theorem mem_foldl_hkMatchingStep (mate : Vector (Option (Fin m)) r) (l : List (Fin r))
    (a : Finset (Fin m × Fin r)) (u : Fin m) (v : Fin r) :
    (u, v) ∈ l.foldl (hkMatchingStep mate) a ↔ (u, v) ∈ a ∨ (v ∈ l ∧ vget mate v = some u) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, hkMatchingStep]
    grind

theorem mem_foldl_hkCoverLeftStep (dist : Vector (Option ℕ) m) (l : List (Fin m))
    (a : Finset (Fin m)) (u : Fin m) :
    u ∈ l.foldl (hkCoverLeftStep dist) a ↔ u ∈ a ∨ (u ∈ l ∧ vget dist u = none) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, hkCoverLeftStep]
    grind

theorem mem_foldl_hkCoverRightStep (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (l : List (Fin r)) (a : Finset (Fin r)) (v : Fin r) :
    v ∈ l.foldl (hkCoverRightStep mate dist) a ↔
      v ∈ a ∨ (v ∈ l ∧ ∃ w, vget mate v = some w ∧ vget dist w ≠ none) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, hkCoverRightStep]
    grind

end Extract

section Main

variable {G : Fin m × Fin r → Bool} {adj : Fin m → List (Fin r)}

theorem mateMatching_replicate_none :
    mateMatching (Vector.replicate r (none : Option (Fin m))) = ∅ := by
  ext e
  simp [vget_replicate]

private theorem hkLoop_start (hadj : BipAdjValid G adj) :
    HKLoopPost G (Vector.replicate r none) 0
      (hkLoop G adj (m + 1) 0 (Vector.replicate r none)) := by
  refine hkLoop_spec hadj (m + 1) 0 _ ?_ (by omega)
  rw [mateMatching_replicate_none]
  exact ⟨by simp, by simp, by simp⟩

theorem hopcroftKarp_matching_eq_mateMatching :
    (hopcroftKarp G adj).matching =
      mateMatching (hkLoop G adj (m + 1) 0 (Vector.replicate r none)).mate := by
  ext ⟨u, v⟩
  simp [hopcroftKarp, mem_foldl_hkMatchingStep]

/-- **Correctness of Hopcroft–Karp.** `hopcroftKarp G adj` returns a maximum matching and a
minimum König vertex cover of equal size, after at most `2⌊√ν⌋` augmenting phases, where `ν` is
the maximum matching size. -/
theorem hopcroftKarp_correct (hadj : BipAdjValid G adj) :
    IsMaxMatching G (hopcroftKarp G adj).matching ∧
      IsMinVertexCover G (hopcroftKarp G adj).cover ∧
      (hopcroftKarp G adj).matching.card = (hopcroftKarp G adj).cover.size ∧
      (hopcroftKarp G adj).phases ≤ 2 * Nat.sqrt (hopcroftKarp G adj).matching.card := by
  have hpost := hkLoop_start (G := G) hadj
  obtain ⟨k, hstable, hsub, hdist⟩ := hpost.closed
  have hM := hpost.isMatching
  set out := hkLoop G adj (m + 1) 0 (Vector.replicate r none)
  have hcover : (hopcroftKarp G adj).cover = layerCover G (mateMatching out.mate) k := by
    simp only [hopcroftKarp, layerCover, VertexCover.mk.injEq]
    exact ⟨Finset.ext fun u => by simp [mem_foldl_hkCoverLeftStep, out, hdist],
      Finset.ext fun v => by
        simp [mem_foldl_hkCoverRightStep, mem_altRight_iff_of_stable hM hstable hsub, out, hdist]⟩
  rw [hopcroftKarp_matching_eq_mateMatching, hcover]
  obtain ⟨hmax, hmin⟩ := isMaxMatching_isMinVertexCover_of_stable hM hstable hsub
  exact ⟨hmax, hmin, (size_layerCover_of_stable hM hstable hsub).symm,
    (mateMatching_replicate_none ▸ Nat.sub_zero _ ▸ hpost.run).le_two_mul_sqrt hmax⟩

/-- Correctness of `hopcroftKarpDense`. -/
theorem hopcroftKarpDense_correct (G : Fin m × Fin r → Bool) :
    IsMaxMatching G (hopcroftKarpDense G).matching ∧
      IsMinVertexCover G (hopcroftKarpDense G).cover ∧
      (hopcroftKarpDense G).matching.card = (hopcroftKarpDense G).cover.size ∧
      (hopcroftKarpDense G).phases ≤ 2 * Nat.sqrt (hopcroftKarpDense G).matching.card :=
  hopcroftKarp_correct (bipAdjValid_denseBipAdj G)

/-- Hopcroft–Karp returns a matching of the same cardinality as any maximum matching `M` of `G`. -/
theorem card_hopcroftKarp_matching_eq {M : Finset (Fin m × Fin r)}
    (hadj : BipAdjValid G adj) (hM : IsMaxMatching G M) :
    (hopcroftKarp G adj).matching.card = M.card :=
  le_antisymm (hM.2 _ (hopcroftKarp_correct hadj).1.1) ((hopcroftKarp_correct hadj).1.2 _ hM.1)

end Main

section Perfect

/-- Decide whether `G : Fin n × Fin n → Bool` has a perfect matching using Hopcroft–Karp. -/
@[expose] def decidePerfectMatchingHK {n : ℕ} (G : Fin n × Fin n → Bool)
    (adj : Fin n → List (Fin n)) : Bool :=
  decide ((hopcroftKarp G adj).matching.card = n)

variable {n : ℕ} {G : Fin n × Fin n → Bool} {adj : Fin n → List (Fin n)}

theorem decidePerfectMatchingHK_eq_true_iff (hadj : BipAdjValid G adj) :
    decidePerfectMatchingHK G adj = true ↔
      Cslib.Circuits.BipartiteMatching.HasPerfectMatching G := by
  simp only [decidePerfectMatchingHK, decide_eq_true_iff,
    hasPerfectMatching_iff_exists_matching_card, Fintype.card_fin]
  obtain ⟨hmax, -⟩ := hopcroftKarp_correct hadj
  exact ⟨fun h => ⟨_, hmax.1, h⟩, fun ⟨M, hM, hcard⟩ =>
    le_antisymm (by simpa using hmax.1.card_le_card_left) (hcard.symm.le.trans (hmax.2 M hM))⟩

end Perfect

end Cslib.Algorithms.Lean.MaxFlow
