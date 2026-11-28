/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.ReducedLaplacian
public import CslibFrontier.Foundations.Combinatorics.Digraph.MatrixTree
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Arborescence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Polynomial-time spanning in-arborescence counting

Polynomial-time evaluation of spanning in-arborescence counts for both simple digraphs
(`Digraph`) and multidigraphs (`Multidigraph`) via Tutte's directed matrix-tree theorem and
`Cslib.Circuits.Rational.detRows_polytime`.

## Main definitions

* `Cslib.Complexity.Graph.toDigraph`: simple digraph induced by `G` on `{v // v ∈ G.vertices}`.
* `Cslib.Complexity.Graph.digraphInArborescenceCount`: reduced Laplacian determinant counting
  simple-digraph spanning in-arborescences rooted at `r` (`0` if `r ∉ G.vertices`).
* `Cslib.Complexity.Graph.validArcs`, `.arcSrc`, `.arcTgt`: list of pairs in `G.edges` whose
  endpoints both lie in `G.vertices`, giving a finite multidigraph on `{v // v ∈ G.vertices}`.
* `Cslib.Complexity.Graph.multiLaplacianCount`: reduced multidigraph Laplacian determinant over an
  arbitrary duplicate-free vertex list `vs` and arc list `arcs`.
* `Cslib.Complexity.Graph.multiInArborescenceCount`: reduced Laplacian determinant counting
  multidigraph spanning in-arborescences rooted at `r` (`0` if `r ∉ G.vertices`).

## Main results

* `Cslib.Complexity.Graph.digraphInArborescenceCount_eq_natCard`: exact count equality for
  `G.toDigraph` (`Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence`).
* `Cslib.Complexity.Graph.computableInPolyTime_digraphInArborescenceCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_digraphIsInArborescence`: polynomial-time
  computability on `encPair encGraph encNat`.
* `Cslib.Complexity.Graph.multiLaplacianCount_eq_natCard`: exact multidigraph arborescence count
  formula over any closed duplicate-free vertex list `vs` (`Multidigraph.Arborescence`), shared
  with BEST-theorem Eulerian-circuit counting.
* `Cslib.Complexity.Graph.multiInArborescenceCount_eq_natCard`,
  `Cslib.Complexity.Graph.computableInPolyTime_multiInArborescenceCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_multiIsInArborescence`: exact count and
  polynomial-time computability for multidigraph spanning in-arborescences.
-/

public section

namespace Cslib.Complexity.Graph

open Turing MultiTapeTM

private theorem ite_any_distinctVertices_eq_dite {α : Type*} (G : Graph) (r : ℕ)
    (t : α) (f : r ∈ G.vertices → α) (z : α)
    (ht : ∀ hr : r ∈ G.vertices, r ∈ G.distinctVertices → t = f hr) :
    (if (G.distinctVertices.any fun v => decide (v = r)) then t else z) =
      if hr : r ∈ G.vertices then f hr else z := by
  by_cases hr : r ∈ G.vertices
  · have hr' : r ∈ G.distinctVertices := Graph.mem_distinctVertices.2 hr
    rw [ite_eq_left (List.any_eq_true.2 ⟨r, hr', decide_eq_true rfl⟩), dite_eq_left hr]
    exact ht hr hr'
  · have hany : ¬ (G.distinctVertices.any fun v => decide (v = r)) = true := by
      simp [Graph.mem_distinctVertices, hr]
    rw [ite_eq_right hany, dite_eq_right hr]

/-! ### Simple-digraph spanning in-arborescences -/

/-- The simple digraph induced by `G` on its declared vertices: `u → v` holds iff `(u.1, v.1)`
appears in `G.edges`. -/
@[expose]
def toDigraph (G : Graph) : Digraph {v // v ∈ G.vertices} where
  Adj u v := (u.1, v.1) ∈ G.edges

/-- Entry `(u, v)` of the out-degree integer Laplacian of `G.toDigraph`. -/
@[expose]
def digraphLaplacianEntry (G : Graph) (u v : ℕ) : ℤ :=
  if u = v then
    (G.distinctVertices.countP fun w =>
      decide (w ≠ u) && G.edges.any fun e => decide (e.1 = u ∧ e.2 = w) : ℤ)
  else if G.edges.any fun e => decide (e.1 = u ∧ e.2 = v) then -1 else 0

/-- Number of spanning in-arborescences of `G.toDigraph` rooted at `r` (`0` if `r ∉ G.vertices`),
computed via the reduced out-degree Laplacian determinant. -/
@[expose]
def digraphInArborescenceCount (G : Graph) (r : ℕ) : ℕ :=
  if G.distinctVertices.any fun v => decide (v = r) then
    let rest := G.distinctVertices.filter fun v => decide (v ≠ r)
    (Cslib.Circuits.Rational.detRows
      (rest.map fun u => rest.map fun v => G.digraphLaplacianEntry u v)).toNat
  else 0

private lemma any_eq_decide_mem (arcs : List (ℕ × ℕ)) (u v : ℕ) :
    (arcs.any fun e => decide (e.1 = u ∧ e.2 = v)) = decide ((u, v) ∈ arcs) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists]
  exact ⟨fun ⟨a, b, hab, ha, hb⟩ => ha ▸ hb ▸ hab,
    fun h => ⟨u, v, h, rfl, rfl⟩⟩

open Classical in
private lemma digraphLaplacianEntry_eq (G : Graph) (u v : {v // v ∈ G.vertices}) :
    G.digraphLaplacianEntry u.1 v.1 = ((G.toDigraph.adjMatrix ℤ).laplacian u v) := by
  classical
  rw [Matrix.laplacian_apply]
  by_cases huv : u = v
  · subst huv
    have hdiag :
        G.distinctVertices.countP (fun w =>
            decide (w ≠ u.1) && G.edges.any fun e => decide (e.1 = u.1 ∧ e.2 = w)) =
          (Finset.univ.filter fun w : {v // v ∈ G.vertices} =>
            G.toDigraph.Adj u w ∧ w ≠ u).card := by
      rw [List.countP_eq_card_filter_getElem, ← Fintype.card_subtype, ← Fintype.card_subtype]
      refine Fintype.card_congr (Equiv.subtypeEquiv G.vertexEquiv fun i => ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq, any_eq_decide_mem, toDigraph, ne_eq,
        Subtype.ext_iff, Graph.vertexEquiv_getElem, and_comm]
    simp only [digraphLaplacianEntry, ↓reduceIte, hdiag,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ u), add_sub_cancel_left,
      Digraph.adjMatrix_apply, Finset.sum_boole, Nat.cast_inj]
    congr 1
    ext w
    simp [and_comm]
  · simp only [digraphLaplacianEntry, mt Subtype.ext huv, ↓reduceIte, huv, any_eq_decide_mem,
      Digraph.adjMatrix_apply, zero_sub, decide_eq_true_eq]
    dsimp only [toDigraph]
    by_cases hadj : (u.1, v.1) ∈ G.edges <;> simp [hadj]

/-- `G.digraphInArborescenceCount r` equals the number of spanning in-arborescences of
`G.toDigraph` rooted at `r` (and `0` when `r ∉ G.vertices`). -/
theorem digraphInArborescenceCount_eq_natCard (G : Graph) (r : ℕ) :
    G.digraphInArborescenceCount r =
      if hr : r ∈ G.vertices then
        Nat.card {T : Digraph {v // v ∈ G.vertices} // T ≤ G.toDigraph ∧ T.IsInArborescence ⟨r, hr⟩}
      else 0 := by
  classical
  refine ite_any_distinctVertices_eq_dite G r _ _ 0 fun _ hr_dist => ?_
  dsimp only
  rw [detRows_filter_ne_equiv_eq G.nodup_distinctVertices
      (Equiv.subtypeEquivRight fun _ => Graph.mem_distinctVertices) hr_dist
      (G.toDigraph.adjMatrix ℤ).laplacian G.digraphLaplacianEntry
      fun u v _ _ => G.digraphLaplacianEntry_eq ⟨u.1, Graph.mem_distinctVertices.1 u.2⟩
        ⟨v.1, Graph.mem_distinctVertices.1 v.2⟩,
    Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence]
  exact Int.toNat_natCast _

/-! ### Multidigraph spanning in-arborescences -/

/-- Directed pairs `(u, v)` listed in `G.edges` whose both endpoints lie in `G.vertices`, preserving
multiplicity. -/
@[expose]
def validArcs (G : Graph) : List (ℕ × ℕ) :=
  G.edges.filter fun e =>
    G.vertices.any (fun v => decide (v = e.1)) && G.vertices.any fun v => decide (v = e.2)

theorem mem_validArcs {G : Graph} {e : ℕ × ℕ} :
    e ∈ G.validArcs ↔ e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices := by
  simp [validArcs]

theorem mem_validArcs_fst {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.1 ∈ G.vertices :=
  (mem_validArcs.1 he).2.1

theorem mem_validArcs_snd {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.2 ∈ G.vertices :=
  (mem_validArcs.1 he).2.2

/-- Source vertex of an arc in `G.validArcs`. -/
@[expose]
def arcSrc (G : Graph) (e : Fin G.validArcs.length) : {v // v ∈ G.vertices} :=
  ⟨G.validArcs[e].1, mem_validArcs_fst (List.getElem_mem e.isLt)⟩

/-- Target vertex of an arc in `G.validArcs`. -/
@[expose]
def arcTgt (G : Graph) (e : Fin G.validArcs.length) : {v // v ∈ G.vertices} :=
  ⟨G.validArcs[e].2, mem_validArcs_snd (List.getElem_mem e.isLt)⟩

/-- Entry `(u, v)` of the out-degree integer Laplacian of the multidigraph with arc list `arcs`. -/
@[expose]
def multiLaplacianEntry (arcs : List (ℕ × ℕ)) (u v : ℕ) : ℤ :=
  if u = v then (arcs.countP fun e => decide (e.1 = u ∧ e.2 ≠ u) : ℤ)
  else -(arcs.countP fun e => decide (e.1 = u ∧ e.2 = v) : ℤ)

/-- Determinant of the reduced multidigraph Laplacian on duplicate-free vertex list `vs` after
deleting vertex `r`, converted to `ℕ`. -/
@[expose]
def multiLaplacianCount (vs : List ℕ) (arcs : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  let rest := vs.filter fun v => decide (v ≠ r)
  (Cslib.Circuits.Rational.detRows
    (rest.map fun u => rest.map fun v => multiLaplacianEntry arcs u v)).toNat

/-- Number of spanning in-arborescences of the multidigraph `(G.arcSrc, G.arcTgt)` rooted at `r`
(`0` if `r ∉ G.vertices`). -/
@[expose]
def multiInArborescenceCount (G : Graph) (r : ℕ) : ℕ :=
  if G.distinctVertices.any fun v => decide (v = r) then
    multiLaplacianCount G.distinctVertices G.validArcs r
  else 0

private lemma multiLaplacianEntry_eq {mem : ℕ → Prop} [Fintype {v // mem v}]
    (arcs : List (ℕ × ℕ)) (harcs : ∀ e ∈ arcs, mem e.1 ∧ mem e.2) (u v : {v // mem v}) :
    let src : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
    let tgt : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
    multiLaplacianEntry arcs u.1 v.1 = ((Multidigraph.arcMatrix src tgt ℤ).laplacian u v) := by
  classical
  intro src tgt
  rw [Matrix.laplacian_apply]
  by_cases huv : u = v
  · subst huv
    simp only [multiLaplacianEntry, ↓reduceIte, ← Finset.add_sum_erase _ _ (Finset.mem_univ u),
      add_sub_cancel_left, Multidigraph.arcMatrix_apply, ← Nat.cast_sum, Nat.cast_inj,
      List.countP_eq_card_filter_getElem]
    have hfib :
        ∑ w ∈ Finset.univ.erase u, (Finset.univ.filter fun e => src e = u ∧ tgt e = w).card =
          (Finset.univ.filter fun e => src e = u ∧ tgt e ≠ u).card := by
      simpa only [Finset.filter_filter, Finset.mem_erase, Finset.mem_univ, and_true] using
        Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ.filter fun e => src e = u) (Finset.univ.erase u) tgt
    rw [hfib]
    congr 1
    ext i
    simp [src, tgt, Subtype.ext_iff]
  · simp only [multiLaplacianEntry, mt Subtype.ext huv, ↓reduceIte, huv,
      Multidigraph.arcMatrix_apply, zero_sub, neg_inj, Nat.cast_inj,
      List.countP_eq_card_filter_getElem]
    congr 1
    ext i
    simp [src, tgt, Subtype.ext_iff]

/-- General directed matrix-tree reduction for `multiLaplacianCount`: for any duplicate-free list
`vs` (characterizing `mem : ℕ → Prop`) closed under both endpoints of every arc in `arcs`, and any
root `r ∈ vs`, `multiLaplacianCount vs arcs r` equals the number of spanning in-arborescences
rooted at `⟨r, _⟩`. -/
theorem multiLaplacianCount_eq_natCard {vs : List ℕ} (hnd : vs.Nodup) {mem : ℕ → Prop}
    (hmem : ∀ v, v ∈ vs ↔ mem v) (arcs : List (ℕ × ℕ))
    (harcs : ∀ e ∈ arcs, mem e.1 ∧ mem e.2) {r : ℕ} (hr : r ∈ vs) :
    let src : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
    let tgt : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
    multiLaplacianCount vs arcs r =
      Nat.card {f : {v : {v // mem v} // v ≠ ⟨r, (hmem r).1 hr⟩} → Fin arcs.length //
        Multidigraph.IsInArborescence src tgt ⟨r, (hmem r).1 hr⟩ f} := by
  classical
  intro src tgt
  let e : {v // v ∈ vs} ≃ {v // mem v} := Equiv.subtypeEquivRight hmem
  let : Fintype {v // mem v} := Fintype.ofEquiv {v // v ∈ vs} e
  change (Cslib.Circuits.Rational.detRows _).toNat = _
  rw [detRows_filter_ne_equiv_eq hnd e hr (Multidigraph.arcMatrix src tgt ℤ).laplacian
      (multiLaplacianEntry arcs) fun u v _ _ => multiLaplacianEntry_eq arcs harcs (e u) (e v),
    Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence]
  exact Int.toNat_natCast _

/-- `G.multiInArborescenceCount r` equals the number of multidigraph spanning in-arborescences
of `(G.arcSrc, G.arcTgt)` rooted at `r` (and `0` if `r ∉ G.vertices`). -/
theorem multiInArborescenceCount_eq_natCard (G : Graph) (r : ℕ) :
    G.multiInArborescenceCount r =
      if hr : r ∈ G.vertices then
        Nat.card {f : {v : {v // v ∈ G.vertices} // v ≠ ⟨r, hr⟩} → Fin G.validArcs.length //
          Multidigraph.IsInArborescence G.arcSrc G.arcTgt ⟨r, hr⟩ f}
      else 0 := by
  classical
  exact ite_any_distinctVertices_eq_dite G r _ _ 0 fun _ hr_dist =>
    multiLaplacianCount_eq_natCard G.nodup_distinctVertices
      (fun _ => Graph.mem_distinctVertices) G.validArcs
      (fun _ he => (mem_validArcs.1 he).2) hr_dist

/-! ### Polynomial-time computability -/

@[local fun_prop]
private theorem computableInPolyTime_intBin_countP {α γ : Type}
    {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {test : γ → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2) (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => ((list x).countP (test x) : ℤ)) encIn encIntBin :=
  ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp (.countPWithInput hlist htest))

@[fun_prop]
theorem computableInPolyTime_digraphLaplacianEntry :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.digraphLaplacianEntry p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encIntBin := by
  unfold digraphLaplacianEntry
  fun_prop

/-- `Graph.digraphInArborescenceCount` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_digraphInArborescenceCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.digraphInArborescenceCount p.2)
      (encPair encGraph encNat) encNat := by
  dsimp only [digraphInArborescenceCount]
  exact ComputableInPolyTime.ite' (by fun_prop)
    (ComputableInPolyTime.intBin_toNat.comp (computableInPolyTime_detRows_map (by fun_prop)
      (computableInPolyTime_digraphLaplacianEntry.comp
        (g := fun q : ((Graph × ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2)) (by fun_prop))))
    (ComputableInPolyTime.const 0)

/-- The number of spanning in-arborescences of a simple digraph `G.toDigraph` rooted at `r` is
computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_digraphIsInArborescence :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.vertices then
          Nat.card {T : Digraph {v // v ∈ p.1.vertices} //
            T ≤ p.1.toDigraph ∧ T.IsInArborescence ⟨p.2, hr⟩}
        else 0)
      (encPair encGraph encNat) encNat :=
  computableInPolyTime_digraphInArborescenceCount.of_enc_eq fun p =>
    congrArg encNat (p.1.digraphInArborescenceCount_eq_natCard p.2).symm

/-- Binary encoding of a list of directed arcs `(ℕ × ℕ)`. -/
abbrev encArcList : List (ℕ × ℕ) ↪ List Bool :=
  encList (encPair encNat encNat)

@[fun_prop]
theorem computableInPolyTime_validArcs :
    ComputableInPolyTime validArcs encGraph encArcList := by
  unfold validArcs
  fun_prop

@[fun_prop]
theorem computableInPolyTime_multiLaplacianEntry {γ : Type} {encIn : γ ↪ List Bool}
    {arcs : γ → List (ℕ × ℕ)}
    (harcs : ComputableInPolyTime arcs encIn encArcList) :
    ComputableInPolyTime
      (fun p : (γ × ℕ) × ℕ => multiLaplacianEntry (arcs p.1.1) p.1.2 p.2)
      (encPair (encPair encIn encNat) encNat) encIntBin := by
  unfold multiLaplacianEntry
  fun_prop

/-- `multiLaplacianCount` is computable in polynomial time whenever its vertex list, arc list,
and root vertex are. -/
@[fun_prop]
theorem computableInPolyTime_multiLaplacianCount {γ : Type} {encIn : γ ↪ List Bool}
    {vs : γ → List ℕ} {arcs : γ → List (ℕ × ℕ)} {r : γ → ℕ}
    (hvs : ComputableInPolyTime vs encIn (encList encNat))
    (harcs : ComputableInPolyTime arcs encIn encArcList)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => multiLaplacianCount (vs x) (arcs x) (r x)) encIn encNat :=
  ComputableInPolyTime.intBin_toNat.comp
    (computableInPolyTime_detRows_map (computableInPolyTime_filter_ne hvs hr)
      (computableInPolyTime_multiLaplacianEntry harcs))

/-- `Graph.multiInArborescenceCount` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_multiInArborescenceCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.multiInArborescenceCount p.2)
      (encPair encGraph encNat) encNat := by
  unfold multiInArborescenceCount
  fun_prop

/-- The number of spanning in-arborescences of the multidigraph `(G.arcSrc, G.arcTgt)` rooted at
`r` is computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_multiIsInArborescence :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.vertices then
          Nat.card {f : {v : {v // v ∈ p.1.vertices} // v ≠ ⟨p.2, hr⟩} → Fin p.1.validArcs.length //
            Multidigraph.IsInArborescence p.1.arcSrc p.1.arcTgt ⟨p.2, hr⟩ f}
        else 0)
      (encPair encGraph encNat) encNat :=
  computableInPolyTime_multiInArborescenceCount.of_enc_eq fun p =>
    congrArg encNat (p.1.multiInArborescenceCount_eq_natCard p.2).symm

end Cslib.Complexity.Graph
