/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.MaxCut
public import CslibFrontier.Foundations.Combinatorics.PessimisticEstimator
public import CslibFrontier.Foundations.Data.List.EraseDupsBy

/-!
# Deterministic `1/2`-approximation for weighted `MaxCut` via conditional expectations

Under a uniform random cut assigning each vertex independently to `true` or `false`, every
non-loop edge `(u, v, w)` (`u ≠ v`) crosses the cut with probability `1 / 2` (and stays uncut with
probability `1 / 2`), whereas self-loops (`u = v`) never cross any cut. Scaling expected uncut
edge weight by `2` eliminates fractions:

* `edgeScaledUncut s e` equals `2` times the conditional probability that `e` is uncut given the
  partial 2-coloring `s : PartialCut`, multiplied by `e.weight`;
* assigning a fresh vertex `z` to `true` and `false` averages exactly:
  `scaledUncut edges (assignVertex z true s) + scaledUncut edges (assignVertex z false s) =
    2 * scaledUncut edges s` (`scaledUncut_assignVertex_add`);
* greedily choosing the smaller scaled uncut weight over `distinctVertices edges` via
  `Cslib.PessimisticEstimator.greedy` (`derandomizedCut`) produces a cut crossing at least half the
  total non-loop weight (`nonLoopWeight_le_two_mul_cutWeight_derandomizedCutSide`), hence a
  deterministic `1 / 2`-approximation against every cut `σ : ℕ → Bool`
  (`cutWeight_le_two_mul_derandomizedCutSide`).

Plain multi-tape Turing polynomial-time computability (`ComputableInPolyTime`) of `derandomizedCut`
is proved in `CslibFrontier.Computability.Complexity.Problems.MaxCut.Derandomized`, and an explicit
`O(|V| |E| + |V|)` instruction-count word-RAM implementation is certified in
`CslibFrontier.Algorithms.WordRAM.MaxCut`.

## Main definitions

* `Cslib.Algorithms.Lean.MaxCut.PartialCut`: partial 2-coloring storing vertices assigned to
  `true` and `false`.
* `Cslib.Algorithms.Lean.MaxCut.distinctVertices`: deduplicated list of endpoints in an edge list.
* `Cslib.Algorithms.Lean.MaxCut.edgeScaledUncut`, `Cslib.Algorithms.Lean.MaxCut.scaledUncut`:
  twice the conditionally expected uncut weight of an edge / edge list.
* `Cslib.Algorithms.Lean.MaxCut.nonLoopWeight`, `Cslib.Algorithms.Lean.MaxCut.loopWeight`,
  `Cslib.Algorithms.Lean.MaxCut.totalWeight`: total weight of non-loops, self-loops, and all edges.
* `Cslib.Algorithms.Lean.MaxCut.derandomizedCutState`,
  `Cslib.Algorithms.Lean.MaxCut.derandomizedCut`,
  `Cslib.Algorithms.Lean.MaxCut.derandomizedCutSide`: deterministic conditional-expectations cut.

## Main results

* `Cslib.Algorithms.Lean.MaxCut.scaledUncut_assignVertex_add`: exact conditional-expectation
  averaging step for assigning an unfixed vertex.
* `Cslib.Algorithms.Lean.MaxCut.nonLoopWeight_le_two_mul_cutWeight_derandomizedCutSide`: the output
  cut crosses at least half the non-loop edge weight.
* `Cslib.Algorithms.Lean.MaxCut.cutWeight_le_nonLoopWeight`,
  `Cslib.Algorithms.Lean.MaxCut.cutWeight_le_two_mul_derandomizedCutSide`: deterministic
  `1 / 2`-approximation against every cut `σ : ℕ → Bool`.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*,
  Sections 5.1–5.2][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.MaxCut

open Cslib.Complexity Cslib.Complexity.MaxCut Cslib.PessimisticEstimator

/-- Partial 2-coloring of vertices maintained during greedy `MaxCut` derandomization. -/
structure PartialCut where
  /-- Vertices already assigned to side `true`. -/
  trueSide : List ℕ
  /-- Vertices already assigned to side `false`. -/
  falseSide : List ℕ
  deriving DecidableEq, Repr

/-- Empty partial cut before any vertex has been assigned. -/
@[expose] def PartialCut.empty : PartialCut := ⟨[], []⟩

/-- Convert a `PartialCut` to a total cut indicator (`true` iff listed in `trueSide`). -/
@[expose] def PartialCut.toSide (s : PartialCut) (u : ℕ) : Bool :=
  decide (u ∈ s.trueSide)

/-- Assign vertex `v` to Boolean side `b` in partial cut `s`. -/
@[expose] def assignVertex (v : ℕ) (b : Bool) (s : PartialCut) : PartialCut :=
  if b then ⟨v :: s.trueSide, s.falseSide⟩ else ⟨s.trueSide, v :: s.falseSide⟩

/-- Deduplicated list of vertex endpoints occurring in `edges`, in first-appearance order. -/
@[expose] def distinctVertices (edges : List WeightedEdge) : List ℕ :=
  (endpoints edges).eraseDupsBy fun a b => decide (a = b)

theorem nodup_distinctVertices (edges : List WeightedEdge) : (distinctVertices edges).Nodup :=
  List.nodup_eraseDupsBy_eq (endpoints edges)

@[simp] theorem mem_distinctVertices {edges : List WeightedEdge} {v : ℕ} :
    v ∈ distinctVertices edges ↔ v ∈ endpoints edges :=
  List.mem_eraseDupsBy_eq

/-- Twice the expected uncut weight of edge `e` under a uniform random completion of `s`. -/
@[expose] def edgeScaledUncut (s : PartialCut) (e : WeightedEdge) : ℕ :=
  if e.u = e.v then
    2 * e.weight
  else if e.u ∈ s.trueSide then
    if e.v ∈ s.trueSide then 2 * e.weight
    else if e.v ∈ s.falseSide then 0
    else e.weight
  else if e.u ∈ s.falseSide then
    if e.v ∈ s.trueSide then 0
    else if e.v ∈ s.falseSide then 2 * e.weight
    else e.weight
  else
    e.weight

/-- Twice the expected uncut weight of `edges` under a uniform random completion of `s`. -/
@[expose] def scaledUncut (edges : List WeightedEdge) (s : PartialCut) : ℕ :=
  (edges.map (edgeScaledUncut s)).sum

/-- Total weight of all edges in `edges` (including self-loops). -/
@[expose] def totalWeight (edges : List WeightedEdge) : ℕ :=
  (edges.map WeightedEdge.weight).sum

/-- Total weight of non-loop edges (`u ≠ v`) in `edges`. -/
@[expose] def nonLoopWeight (edges : List WeightedEdge) : ℕ :=
  ((edges.filter fun e => decide (e.u ≠ e.v)).map WeightedEdge.weight).sum

/-- Total weight of self-loop edges (`u = v`) in `edges`. -/
@[expose] def loopWeight (edges : List WeightedEdge) : ℕ :=
  ((edges.filter fun e => decide (e.u = e.v)).map WeightedEdge.weight).sum

private theorem loopWeight_cons (e : WeightedEdge) (es : List WeightedEdge) :
    loopWeight (e :: es) = (if e.u = e.v then e.weight else 0) + loopWeight es := by
  by_cases h : e.u = e.v <;> simp [loopWeight, h]

private theorem nonLoopWeight_cons (e : WeightedEdge) (es : List WeightedEdge) :
    nonLoopWeight (e :: es) = (if e.u = e.v then 0 else e.weight) + nonLoopWeight es := by
  by_cases h : e.u = e.v <;> simp [nonLoopWeight, h]

private theorem cutWeight_cons (e : WeightedEdge) (es : List WeightedEdge) (σ : ℕ → Bool) :
    cutWeight (e :: es) σ = (if crosses σ e then e.weight else 0) + cutWeight es σ := by
  cases h : crosses σ e <;> simp [cutWeight, h]

theorem totalWeight_eq_loopWeight_add_nonLoopWeight :
    ∀ edges : List WeightedEdge, totalWeight edges = loopWeight edges + nonLoopWeight edges
  | [] => rfl
  | e :: es => by
    have ih := totalWeight_eq_loopWeight_add_nonLoopWeight es
    have ht : totalWeight (e :: es) = e.weight + totalWeight es := rfl
    rw [ht, loopWeight_cons, nonLoopWeight_cons]
    by_cases h : e.u = e.v <;> (simp only [h, ↓reduceIte]; omega)

private theorem edgeScaledUncut_empty (e : WeightedEdge) :
    edgeScaledUncut PartialCut.empty e = if e.u = e.v then 2 * e.weight else e.weight := by
  by_cases h : e.u = e.v <;> simp [edgeScaledUncut, PartialCut.empty, h]

theorem scaledUncut_empty :
    ∀ edges : List WeightedEdge,
      scaledUncut edges PartialCut.empty = 2 * loopWeight edges + nonLoopWeight edges
  | [] => rfl
  | e :: es => by
    have ih := scaledUncut_empty es
    have hs : scaledUncut (e :: es) PartialCut.empty =
        edgeScaledUncut PartialCut.empty e + scaledUncut es PartialCut.empty := rfl
    rw [hs, edgeScaledUncut_empty, loopWeight_cons, nonLoopWeight_cons]
    by_cases h : e.u = e.v <;> (simp only [h, ↓reduceIte]; omega)

private theorem edgeScaledUncut_assignVertex_add {s : PartialCut} {z : ℕ}
    (hdisj : ∀ u, u ∈ s.trueSide → u ∉ s.falseSide)
    (hzT : z ∉ s.trueSide) (hzF : z ∉ s.falseSide) (e : WeightedEdge) :
    edgeScaledUncut (assignVertex z true s) e + edgeScaledUncut (assignVertex z false s) e =
      2 * edgeScaledUncut s e := by
  have _ := hdisj
  by_cases huv : e.u = e.v
  · simp [edgeScaledUncut, huv]; omega
  by_cases huz : e.u = z
  · subst huz
    have hvz : e.v ≠ e.u := Ne.symm huv
    by_cases hvT : e.v ∈ s.trueSide
    · simp [edgeScaledUncut, assignVertex, huv, hvT, hvz, hzT, hzF]
    · by_cases hvF : e.v ∈ s.falseSide <;>
        simp [edgeScaledUncut, assignVertex, huv, hvT, hvF, hvz, hzT, hzF]
      omega
  by_cases hvz : e.v = z
  · subst hvz
    by_cases huT : e.u ∈ s.trueSide
    · simp [edgeScaledUncut, assignVertex, huv, huT, hzT, hzF]
    · by_cases huF : e.u ∈ s.falseSide <;>
        simp [edgeScaledUncut, assignVertex, huv, huT, huF, hzT, hzF]
      omega
  have hmem (b : Bool) : edgeScaledUncut (assignVertex z b s) e = edgeScaledUncut s e := by
    cases b <;> simp [edgeScaledUncut, assignVertex, huv, huz, hvz]
  rw [hmem true, hmem false]; omega

/-- Exact conditional-expectation averaging law for `scaledUncut`: assigning an unfixed vertex `z`
to `true` and `false` sums to twice `scaledUncut edges s`. -/
theorem scaledUncut_assignVertex_add {s : PartialCut} {z : ℕ}
    (hdisj : ∀ u, u ∈ s.trueSide → u ∉ s.falseSide)
    (hzT : z ∉ s.trueSide) (hzF : z ∉ s.falseSide) (edges : List WeightedEdge) :
    scaledUncut edges (assignVertex z true s) + scaledUncut edges (assignVertex z false s) =
      2 * scaledUncut edges s := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    have he := edgeScaledUncut_assignVertex_add hdisj hzT hzF e
    simp only [scaledUncut, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem edgeScaledUncut_add_crosses {s : PartialCut}
    (hdisj : ∀ u, u ∈ s.trueSide → u ∉ s.falseSide) {e : WeightedEdge}
    (hu : e.u ∈ s.trueSide ∨ e.u ∈ s.falseSide)
    (hv : e.v ∈ s.trueSide ∨ e.v ∈ s.falseSide) :
    edgeScaledUncut s e + (if crosses s.toSide e then 2 * e.weight else 0) = 2 * e.weight := by
  by_cases huv : e.u = e.v
  · simp [edgeScaledUncut, crosses, huv]
  have hnot : ∀ u, u ∈ s.falseSide → u ∉ s.trueSide := fun u hf ht => hdisj u ht hf
  rcases hu with huT | huF <;> rcases hv with hvT | hvF
  · simp [edgeScaledUncut, crosses, PartialCut.toSide, huv, huT, hvT]
  · simp [edgeScaledUncut, crosses, PartialCut.toSide, huv, huT, hvF, hnot _ hvF]
  · simp [edgeScaledUncut, crosses, PartialCut.toSide, huv, huF, hvT, hnot _ huF]
  · simp [edgeScaledUncut, crosses, PartialCut.toSide, huv, huF, hvF, hnot _ huF, hnot _ hvF]

private theorem scaledUncut_add_two_mul_cutWeight :
    ∀ (edges : List WeightedEdge) {s : PartialCut},
      (∀ u, u ∈ s.trueSide → u ∉ s.falseSide) →
      (∀ v ∈ endpoints edges, v ∈ s.trueSide ∨ v ∈ s.falseSide) →
      scaledUncut edges s + 2 * cutWeight edges s.toSide = 2 * totalWeight edges
  | [], _, _, _ => rfl
  | e :: es, s, hdisj, hcov => by
    have hu := hcov e.u (List.mem_flatMap.2 ⟨e, List.mem_cons_self, by simp⟩)
    have hv := hcov e.v (List.mem_flatMap.2 ⟨e, List.mem_cons_self, by simp⟩)
    have hes : ∀ v ∈ endpoints es, v ∈ s.trueSide ∨ v ∈ s.falseSide := fun v hv' =>
      hcov v (by
        rcases List.mem_flatMap.1 hv' with ⟨e', he', hv''⟩
        exact List.mem_flatMap.2 ⟨e', List.mem_cons_of_mem e he', hv''⟩)
    have he := edgeScaledUncut_add_crosses hdisj hu hv
    have hrec := scaledUncut_add_two_mul_cutWeight es hdisj hes
    have hs : scaledUncut (e :: es) s = edgeScaledUncut s e + scaledUncut es s := rfl
    have ht : totalWeight (e :: es) = e.weight + totalWeight es := rfl
    rw [hs, ht, cutWeight_cons]
    cases hc : crosses s.toSide e <;>
      (simp only [hc, Bool.false_eq_true, ↓reduceIte] at he ⊢; omega)

/-! ### Pure greedy conditional-expectations MaxCut -/

/-- Final `PartialCut` produced by running `Cslib.PessimisticEstimator.greedy` over
`distinctVertices edges`. -/
@[expose] def derandomizedCutState (edges : List WeightedEdge) : PartialCut :=
  greedy assignVertex (scaledUncut edges) (distinctVertices edges) PartialCut.empty

/-- Deterministic list of vertices placed on the `true` side by conditional expectations. -/
@[expose] def derandomizedCut (edges : List WeightedEdge) : List ℕ :=
  (derandomizedCutState edges).trueSide

/-- Cut predicate `ℕ → Bool` produced by `derandomizedCut`. -/
@[expose] def derandomizedCutSide (edges : List WeightedEdge) (u : ℕ) : Bool :=
  decide (u ∈ derandomizedCut edges)

private def CutInv (edges : List WeightedEdge) (rem : List ℕ) (s : PartialCut) : Prop :=
  rem.Nodup ∧
    (∀ u, u ∈ s.trueSide → u ∉ s.falseSide) ∧
    (∀ z ∈ rem, z ∉ s.trueSide ∧ z ∉ s.falseSide) ∧
    (∀ v ∈ endpoints edges, v ∈ rem ∨ v ∈ s.trueSide ∨ v ∈ s.falseSide)

private theorem cutInv_init (edges : List WeightedEdge) :
    CutInv edges (distinctVertices edges) PartialCut.empty := by
  refine ⟨nodup_distinctVertices edges, ?_, ?_, ?_⟩
  · intro _ hu
    cases hu
  · intro _ _
    exact ⟨List.not_mem_nil, List.not_mem_nil⟩
  · intro v hv
    exact Or.inl (mem_distinctVertices.2 hv)

private theorem cutInv_branch {edges : List WeightedEdge} (z : ℕ) (rs : List ℕ) (s : PartialCut)
    (b : Bool) (h : CutInv edges (z :: rs) s) :
    CutInv edges rs (assignVertex z b s) := by
  obtain ⟨hnd, hdisj, hfresh, hcov⟩ := h
  obtain ⟨hz_rs, hnd_rs⟩ := List.nodup_cons.1 hnd
  obtain ⟨hzT, hzF⟩ := hfresh z List.mem_cons_self
  cases b <;> refine ⟨hnd_rs, ?_, ?_, ?_⟩
  · intro u huT huF
    exact (List.mem_cons.1 huF).elim (fun h => hzT (h ▸ huT)) (hdisj u huT)
  · intro w hw
    obtain ⟨hwT, hwF⟩ := hfresh w (List.mem_cons_of_mem z hw)
    exact ⟨hwT, fun h => (List.mem_cons.1 h).elim (fun h => hz_rs (h ▸ hw)) hwF⟩
  · intro v hv
    rcases hcov v hv with hv | hv | hv
    · rcases List.mem_cons.1 hv with rfl | hv'
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact Or.inl hv'
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (List.mem_cons_of_mem z hv))
  · intro u huT huF
    exact (List.mem_cons.1 huT).elim (fun h => hzF (h ▸ huF)) (fun huT' => hdisj u huT' huF)
  · intro w hw
    obtain ⟨hwT, hwF⟩ := hfresh w (List.mem_cons_of_mem z hw)
    exact ⟨fun h => (List.mem_cons.1 h).elim (fun h => hz_rs (h ▸ hw)) hwT, hwF⟩
  · intro v hv
    rcases hcov v hv with hv | hv | hv
    · rcases List.mem_cons.1 hv with rfl | hv'
      · exact Or.inr (Or.inl List.mem_cons_self)
      · exact Or.inl hv'
    · exact Or.inr (Or.inl (List.mem_cons_of_mem z hv))
    · exact Or.inr (Or.inr hv)

private theorem cutInv_avg {edges : List WeightedEdge} (z : ℕ) (rs : List ℕ) (s : PartialCut)
    (h : CutInv edges (z :: rs) s) :
    scaledUncut edges (assignVertex z true s) + scaledUncut edges (assignVertex z false s) ≤
      scaledUncut edges s + scaledUncut edges s := by
  obtain ⟨_, hdisj, hfresh, _⟩ := h
  obtain ⟨hzT, hzF⟩ := hfresh z List.mem_cons_self
  rw [scaledUncut_assignVertex_add hdisj hzT hzF edges]
  omega

private theorem nonLoopWeight_le_two_mul_of_terminal {edges : List WeightedEdge} {s : PartialCut}
    (hinv : CutInv edges [] s)
    (hle : scaledUncut edges s ≤ scaledUncut edges PartialCut.empty) :
    nonLoopWeight edges ≤ 2 * cutWeight edges s.toSide := by
  obtain ⟨_, hdisj, _, hcov⟩ := hinv
  have hcov' : ∀ v ∈ endpoints edges, v ∈ s.trueSide ∨ v ∈ s.falseSide := by
    intro v hv
    rcases hcov v hv with hnil | hTF
    · cases hnil
    · exact hTF
  have hsum := scaledUncut_add_two_mul_cutWeight edges hdisj hcov'
  have htot := totalWeight_eq_loopWeight_add_nonLoopWeight edges
  have hemp := scaledUncut_empty edges
  omega

/-- **Deterministic conditional-expectations MaxCut bound**: `derandomizedCutSide edges` cuts at
least half of the total weight of all non-loop edges in `edges`. -/
theorem nonLoopWeight_le_two_mul_cutWeight_derandomizedCutSide (edges : List WeightedEdge) :
    nonLoopWeight edges ≤ 2 * cutWeight edges (derandomizedCutSide edges) := by
  obtain ⟨hinv, hle⟩ :=
    greedy_spec_of_add_le assignVertex (scaledUncut edges) (CutInv edges)
      cutInv_branch cutInv_avg (distinctVertices edges) PartialCut.empty (cutInv_init edges)
  exact nonLoopWeight_le_two_mul_of_terminal hinv hle

/-- Every cut `σ : ℕ → Bool` crosses only non-loop edges, so its weight is at most
`nonLoopWeight edges`. -/
theorem cutWeight_le_nonLoopWeight :
    ∀ (edges : List WeightedEdge) (σ : ℕ → Bool), cutWeight edges σ ≤ nonLoopWeight edges
  | [], _ => le_rfl
  | e :: es, σ => by
    have ih := cutWeight_le_nonLoopWeight es σ
    rw [cutWeight_cons, nonLoopWeight_cons]
    by_cases huv : e.u = e.v
    · simp only [huv, ↓reduceIte, crosses, bne_self_eq_false, Bool.false_eq_true]; omega
    · simp only [huv, ↓reduceIte]
      cases crosses σ e <;> (simp only [Bool.false_eq_true, ↓reduceIte]; omega)

/-- **Deterministic `1 / 2`-approximation for weighted `MaxCut`**: for every cut `σ : ℕ → Bool`,
`cutWeight edges σ ≤ 2 * cutWeight edges (derandomizedCutSide edges)`. -/
theorem cutWeight_le_two_mul_derandomizedCutSide (edges : List WeightedEdge) (σ : ℕ → Bool) :
    cutWeight edges σ ≤ 2 * cutWeight edges (derandomizedCutSide edges) :=
  (cutWeight_le_nonLoopWeight edges σ).trans
    (nonLoopWeight_le_two_mul_cutWeight_derandomizedCutSide edges)

end Cslib.Algorithms.Lean.MaxCut
