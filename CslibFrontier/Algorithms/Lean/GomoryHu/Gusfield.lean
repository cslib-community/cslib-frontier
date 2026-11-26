/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Basic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic

/-!
# Gusfield's algorithm for Gomory–Hu trees

Gusfield ([Gusfield1990]) showed that a Gomory–Hu tree can be computed with `n - 1` minimum cut
computations in the original graph, without the contractions of Gomory and Hu's construction
([GomoryHu1961]). The tree is kept as a parent function `p` with root `r`. Initially every vertex
hangs from `r`. The other vertices `s` are processed once each: with `t = p s` and a minimum
`s`–`t` cut `X`, every other vertex whose parent is `t` and which lies in `X` is re-hung below `s`,
and if the parent of `t` lies in `X`, then `s` takes the place of `t` (`p s := p t`, `p t := s`).

This module states the algorithm for an arbitrary cut oracle and an arbitrary processing order,
and proves it correct for every symmetric submodular set function: if the oracle returns minimum
cuts, the final parent graph is a Gomory–Hu tree. The oracle may return any minimum cut. The
executable version over `Fin n` with Edmonds–Karp as the oracle is
`CslibFrontier.Algorithms.Lean.GomoryHu.Construction`, and its Word-RAM running time is
`CslibFrontier.Algorithms.WordRAM.GomoryHu`.

## Proof

After processing a set `P ∋ r` of vertices, the invariant is: the parent of every vertex is in
`P`; every `i ∈ P` other than `r` carries a minimum `i`–`p i` cut `S i` that no other parent pointer
crosses (`z ∈ S i ↔ p z ∈ S i` for `z ≠ i`); and every vertex is joined to `r` by parent pointers.
To process `s ∉ P` with parent `t`, the cut `X` returned by the oracle is uncrossed with the sides,
away from `t`, of the parent edges at `t` (`IsMinCutBetween.union`, `IsMinCutBetween.sdiff`). This
gives a minimum `s`–`t` cut `U` that agrees with `X` on the vertices the algorithm inspects and
that no other parent pointer crosses. A re-hung vertex `i` keeps its label: a minimum `i`–`t` cut
missing `s` is a minimum `i`–`s` cut when some minimum `s`–`t` cut contains `i`. In the swap case,
`s` inherits the label of `t` and `t` gets `Uᶜ`; otherwise `s` gets `U`. Once every vertex is
processed, the parent graph is connected with `n - 1` edges, hence a tree, and by
`edgeSide_eq_of_forall_adj` the side of each parent edge `(u, p u)` containing `u` is `S u`.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.gusfieldStep`, `Cslib.Algorithms.Lean.GomoryHu.gusfieldLoop`,
  `Cslib.Algorithms.Lean.GomoryHu.gusfieldParent`: Gusfield's algorithm on parent functions, with
  a cut oracle `C : V → V → Finset V`.
* `Cslib.Algorithms.Lean.GomoryHu.gusfieldStepWeight`,
  `Cslib.Algorithms.Lean.GomoryHu.gusfieldWeightLoop`,
  `Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights`: the same algorithm tracking the cut value
  `w u = f (S u)` alongside the parent function, given a value oracle `val : V → V → β`.

The tree of the output is its parent graph `SimpleGraph.parentGraph`
(`CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic`).

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gusfieldParent`: for a symmetric submodular `f`
  and an oracle returning minimum cuts, Gusfield's algorithm computes a Gomory–Hu tree of `f`.
* `Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights_spec`,
  `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gusfieldWithWeights`,
  `Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights_weight_eq`,
  `Cslib.Algorithms.Lean.GomoryHu.isMinCutBetween_gusfieldWithWeights_edgeSide`:
  `gusfieldWithWeights` computes the same Gomory–Hu tree together with
  `w u = f (edgeSide (parentGraph p) u (p u))` for every non-root `u`.

## References

* [GomoryHu1961]
* [Gusfield1990]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean.Submodular
open SimpleGraph (parentGraph parentGraph_adj edgeSide edgeSide_eq_of_forall_adj edgeSide_swap)

variable {V : Type*} {β : Type*}

/-! ### Iterated uncrossing -/

section IteratedUncross

variable [DecidableEq V] {ι : Type*}

/-- Uncross `X` successively with the sets `A k`, `k ∈ ks`: add `A k` when `a k ∈ X`, remove it
otherwise. -/
private def uncrossList (X : Finset V) (a : ι → V) (A : ι → Finset V) :
    List ι → Finset V
  | [] => X
  | k :: ks => if a k ∈ X then uncrossList X a A ks ∪ A k else uncrossList X a A ks \ A k

private theorem mem_uncrossList_of_mem {X : Finset V} {a : ι → V} {A : ι → Finset V} {ks : List ι}
    (hdisj : ks.Pairwise fun i j => Disjoint (A i) (A j)) {k : ι} (hk : k ∈ ks) {z : V}
    (hz : z ∈ A k) : z ∈ uncrossList X a A ks ↔ a k ∈ X := by
  induction ks with
  | nil => simp at hk
  | cons k' ks ih =>
    rw [List.pairwise_cons] at hdisj
    rcases List.mem_cons.mp hk with rfl | hk
    · unfold uncrossList
      split_ifs with h
      · exact iff_of_true (Finset.mem_union_right _ hz) h
      · exact iff_of_false (fun h' => (Finset.mem_sdiff.mp h').2 hz) h
    · have hz' : z ∉ A k' := fun h => Finset.disjoint_left.mp (hdisj.1 k hk) h hz
      unfold uncrossList
      split_ifs <;> simp [ih hdisj.2 hk, hz']

private theorem mem_uncrossList_of_forall_notMem {X : Finset V} {a : ι → V} {A : ι → Finset V}
    {ks : List ι} {z : V} (hz : ∀ k ∈ ks, z ∉ A k) : z ∈ uncrossList X a A ks ↔ z ∈ X := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hzk : z ∉ A k := hz k (by simp)
    unfold uncrossList
    split_ifs <;> simp [ih fun j hj => hz j (by simp [hj]), hzk]

private theorem isMinCutBetween_uncrossList [Fintype V] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {s t : V} {X : Finset V} (hX : IsMinCutBetween f s t X) {a : ι → V}
    {A : ι → Finset V} {ks : List ι} (hA : ∀ k ∈ ks, IsMinCutBetween f (a k) t (A k))
    (hsA : ∀ k ∈ ks, s ∉ A k) (hdisj : ks.Pairwise fun i j => Disjoint (A i) (A j)) :
    IsMinCutBetween f s t (uncrossList X a A ks) := by
  induction ks with
  | nil => exact hX
  | cons k ks ih =>
    rw [List.pairwise_cons] at hdisj
    have ih' := ih (fun j hj => hA j (by simp [hj])) (fun j hj => hsA j (by simp [hj])) hdisj.2
    have hak : a k ∈ uncrossList X a A ks ↔ a k ∈ X := by
      refine mem_uncrossList_of_forall_notMem fun j hj h => ?_
      exact Finset.disjoint_left.mp (hdisj.1 j hj) (hA k (by simp)).left_mem h
    unfold uncrossList
    split_ifs with h
    · exact ih'.union hsub (hA k (by simp)) (hak.mpr h)
    · exact ih'.sdiff hsym hsub (hA k (by simp)) (fun h' => h (hak.mp h')) (hsA k (by simp))

end IteratedUncross

/-! ### Gusfield's algorithm -/

section Algorithm

variable [DecidableEq V]

/-- One step of Gusfield's algorithm ([Gusfield1990]) on the parent function `p`: given the
vertex `s` with current parent `t = p s` and an `s`–`t` cut `X ∋ s`, every other vertex with
parent `t` on the `s`-side of `X` is re-hung below `s`; if moreover the parent of `t` lies on the
`s`-side, `s` takes the place of `t` (`p s := p t`, `p t := s`). -/
@[expose] def gusfieldStep (p : V → V) (s : V) (X : Finset V) : V → V := fun z =>
  if z = s then (if p (p s) ∈ X then p (p s) else p s)
  else if z = p s then (if p (p s) ∈ X then s else p (p s))
  else if p z = p s ∧ z ∈ X then s else p z

/-- Gusfield's algorithm: process the vertices of `l` in order (skipping the root `r`), each
with one call `C s (p s)` of the cut oracle. -/
@[expose] def gusfieldLoop (C : V → V → Finset V) (r : V) : List V → (V → V) → V → V
  | [], p => p
  | s :: l, p => gusfieldLoop C r l (if s = r then p else gusfieldStep p s (C s (p s)))

/-- The parent function computed by Gusfield's algorithm with cut oracle `C`, root `r` and vertex
order `l`, starting from the star centred at `r`. -/
@[expose] def gusfieldParent (C : V → V → Finset V) (r : V) (l : List V) : V → V :=
  gusfieldLoop C r l fun _ => r

/-- One step of Gusfield's algorithm on the edge-weight function `w`, updating edge weights from the
cut value `v` for `(s, p s)`. On a swap (`p (p s) ∈ X`), `s` inherits `w (p s)` and `p s` receives
`v`; otherwise `s` receives `v`. -/
@[expose] def gusfieldStepWeight (p : V → V) (w : V → β) (s : V) (X : Finset V) (v : β) :
    V → β := fun z =>
  if p (p s) ∈ X then
    if z = s then w (p s) else if z = p s then v else w z
  else
    if z = s then v else w z

/-- Gusfield's loop tracking both the parent function `p` and edge-weight function `w`, using cut
oracle `C` and cut-value oracle `val`. -/
@[expose] def gusfieldWeightLoop (C : V → V → Finset V) (val : V → V → β) (r : V) :
    List V → (V → V) → (V → β) → (V → V) × (V → β)
  | [], p, w => (p, w)
  | s :: l, p, w =>
    if s = r then gusfieldWeightLoop C val r l p w
    else
      let X := C s (p s)
      gusfieldWeightLoop C val r l (gusfieldStep p s X)
        (gusfieldStepWeight p w s X (val s (p s)))

/-- The parent and weight functions computed by Gusfield's algorithm with cut oracle `C`, value
oracle `val`, root `r`, initial weight `w₀`, and vertex order `l`. -/
@[expose] def gusfieldWithWeights (C : V → V → Finset V) (val : V → V → β) (r : V) (w₀ : β)
    (l : List V) : (V → V) × (V → β) :=
  gusfieldWeightLoop C val r l (fun _ => r) (fun _ => w₀)

/-- Ignoring edge weights, `gusfieldWeightLoop` computes the same parent function as
`gusfieldLoop`. -/
theorem fst_gusfieldWeightLoop (C : V → V → Finset V) (val : V → V → β) (r : V) :
    ∀ (l : List V) (p : V → V) (w : V → β),
      (gusfieldWeightLoop C val r l p w).1 = gusfieldLoop C r l p
  | [], _, _ => rfl
  | s :: l, p, w => by
    by_cases hsr : s = r <;>
      simp only [gusfieldWeightLoop, gusfieldLoop, hsr, ↓reduceIte, fst_gusfieldWeightLoop]

/-- The first component of `gusfieldWithWeights` equals `gusfieldParent`. -/
theorem fst_gusfieldWithWeights (C : V → V → Finset V) (val : V → V → β) (r : V) (w₀ : β)
    (l : List V) :
    (gusfieldWithWeights C val r w₀ l).1 = gusfieldParent C r l :=
  fst_gusfieldWeightLoop C val r l (fun _ => r) (fun _ => w₀)

end Algorithm

/-! ### The invariant -/

section Invariant

/-- `x` and `y` are joined by a parent pointer. -/
private def TAdj (p : V → V) (x y : V) : Prop := p x = y ∨ p y = x

private theorem reflTransGen_tAdj_symm {p : V → V} {x y : V}
    (h : Relation.ReflTransGen (TAdj p) x y) : Relation.ReflTransGen (TAdj p) y x := by
  rw [← Relation.reflTransGen_swap]
  exact Relation.ReflTransGen.mono (fun _ _ h => Or.symm h) _ _ h

/-- Membership in a set closed under the parent pointers is constant along `TAdj` chains. -/
private theorem mem_iff_of_reflTransGen_tAdj {p : V → V} {Y : Finset V} (hY : ∀ z, z ∈ Y ↔ p z ∈ Y)
    {x y : V} (h : Relation.ReflTransGen (TAdj p) x y) : x ∈ Y ↔ y ∈ Y := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rcases hbc with h | h
    · rw [ih, hY, h]
    · rw [ih, ← h, ← hY]

variable [Fintype V] [DecidableEq V] [Preorder β]

/-- Invariant of Gusfield's algorithm after processing the vertex set `P ∋ r`: every processed
vertex `i ≠ r` has a parent `p i ∈ P`, a minimum `i`–`p i` cut `S i` that no other parent pointer
crosses, recorded weight `w i = f (S i)`, and all vertices are joined to `r` by parent pointers. -/
private structure GInv (f : Finset V → β) (r : V) (P : Finset V) (p : V → V) (S : V → Finset V)
    (w : V → β) : Prop where
  root_mem : r ∈ P
  parent_root : p r = r
  parent_mem : ∀ z, p z ∈ P
  cut : ∀ i ∈ P, i ≠ r → IsMinCutBetween f i (p i) (S i)
  lam : ∀ i ∈ P, i ≠ r → ∀ z, z ≠ i → (z ∈ S i ↔ p z ∈ S i)
  weight : ∀ i ∈ P, i ≠ r → w i = f (S i)
  conn : ∀ z, Relation.ReflTransGen (TAdj p) z r

omit [Fintype V] [DecidableEq V] in
private theorem gInv_init (f : Finset V → β) (r : V) (S : V → Finset V) (w : V → β) :
    GInv f r {r} (fun _ => r) S w where
  root_mem := Finset.mem_singleton_self r
  parent_root := rfl
  parent_mem _ := Finset.mem_singleton_self r
  cut _ hi hir := absurd (Finset.mem_singleton.mp hi) hir
  lam _ hi hir := absurd (Finset.mem_singleton.mp hi) hir
  weight _ hi hir := absurd (Finset.mem_singleton.mp hi) hir
  conn _ := Relation.ReflTransGen.single (Or.inl rfl)

/-- Re-hanging a subtree: if `Si` is a minimum `i`–`t` cut missing `s` and `X` is a minimum
`s`–`t` cut containing `i`, then `Si` is a minimum `i`–`s` cut. -/
private theorem isMinCutBetween_rehang {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X) {i s t : V}
    {Si X : Finset V} (hSi : IsMinCutBetween f i t Si) (hX : IsMinCutBetween f s t X)
    (hsSi : s ∉ Si) (hiX : i ∈ X) : IsMinCutBetween f i s Si := by
  refine ⟨hSi.left_mem, hsSi, fun Y hi hs => ?_⟩
  by_cases htY : t ∈ Y
  · exact (hSi.le_of_separates hsym ⟨fun _ => hX.right_notMem, fun _ => hiX⟩).trans
      (hX.le_of_separates hsym ⟨fun h => absurd h hs, fun h => absurd htY h⟩)
  · exact hSi.le hi htY

/-- Swapping a vertex into the place of its parent: if `St` is a minimum `t`–`u` cut containing
`s`, and `X` is a minimum `s`–`t` cut containing `u`, then `St` is a minimum `s`–`u` cut. -/
private theorem isMinCutBetween_swap {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X) {s t u : V}
    {St X : Finset V} (hSt : IsMinCutBetween f t u St) (hX : IsMinCutBetween f s t X)
    (hsSt : s ∈ St) (huX : u ∈ X) : IsMinCutBetween f s u St := by
  refine ⟨hsSt, hSt.right_notMem, fun Y hs hu => ?_⟩
  by_cases htY : t ∈ Y
  · exact hSt.le htY hu
  · exact (hSt.le_of_separates hsym ⟨fun h => absurd h hX.right_notMem,
      fun h => absurd huX h⟩).trans (hX.le_of_separates hsym ⟨fun _ => htY, fun _ => hs⟩)

omit [Fintype V] [DecidableEq V] in
/-- Connectivity transfers along a change of parent function when every old parent pointer is
replaced by a chain of new ones. -/
private theorem reflTransGen_tAdj_of_step {p q : V → V} {r : V}
    (hp : ∀ z, Relation.ReflTransGen (TAdj p) z r)
    (h : ∀ z, Relation.ReflTransGen (TAdj q) z (p z)) (z : V) :
    Relation.ReflTransGen (TAdj q) z r := by
  have key : ∀ x y, TAdj p x y → Relation.ReflTransGen (TAdj q) x y := by
    rintro x y (hxy | hxy)
    · rw [← hxy]; exact h x
    · rw [← hxy]; exact reflTransGen_tAdj_symm (h y)
  exact Relation.reflTransGen_closed key _ _ (hp z)

end Invariant

/-! ### The step -/

section Step

variable [Fintype V] [DecidableEq V]

/-- The endpoint of the tree edge `(k, p k)` on the far side from `t`. -/
private def farEnd (p : V → V) (S : V → Finset V) (t k : V) : V := if t ∈ S k then p k else k

/-- The side of the tree edge `(k, p k)` away from `t`. -/
private def farSide (S : V → Finset V) (t k : V) : Finset V := if t ∈ S k then (S k)ᶜ else S k

/-! #### The processed tree edges at `t` -/

section EdgesAt

variable [Preorder β] {f : Finset V → β}

/-- The processed tree edges `(k, p k)` incident to `t`, named by their child endpoint `k`: the
children of `t` in `P` and, unless `t = r`, the edge from `t` to its parent. -/
private def edgesAt (r : V) (P : Finset V) (p : V → V) (t : V) : Finset V :=
  P.filter fun i => i ≠ r ∧ (p i = t ∨ i = t)

omit [Fintype V] in
private theorem mem_edgesAt {r : V} {P : Finset V} {p : V → V} {t k : V} :
    k ∈ edgesAt r P p t ↔ k ∈ P ∧ k ≠ r ∧ (p k = t ∨ k = t) := by
  simp [edgesAt]

omit [Fintype V] in
/-- The two kinds of tree edges at `t`: a child edge `(k, t)` with `t ∉ S k`, or the parent edge
`(t, p t)` with `t ∈ S t`. -/
private theorem GInv.edgesAt_cases {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    {w : V → β} (I : GInv f r P p S w) {t k : V} (hk : k ∈ edgesAt r P p t) :
    (t ∉ S k ∧ p k = t) ∨ (t ∈ S k ∧ k = t) := by
  obtain ⟨hkP, hkr, hkt⟩ := mem_edgesAt.mp hk
  have hc := I.cut k hkP hkr
  rcases hkt with h | h
  · exact .inl ⟨fun htk => hc.right_notMem (h ▸ htk), h⟩
  · exact .inr ⟨h ▸ hc.left_mem, h⟩

/-- The far side of a tree edge at `t` is a minimum cut between its far endpoint and `t`. -/
private theorem GInv.isMinCutBetween_farSide (hsym : ∀ X, f Xᶜ = f X) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} {w : V → β} (I : GInv f r P p S w) {t k : V}
    (hk : k ∈ edgesAt r P p t) :
    IsMinCutBetween f (farEnd p S t k) t (farSide S t k) := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  rcases I.edgesAt_cases hk with ⟨htk, rfl⟩ | ⟨htk, rfl⟩
  · simpa only [farEnd, farSide, htk, ↓reduceIte] using I.cut k hkP hkr
  · simpa only [farEnd, farSide, htk, ↓reduceIte] using (I.cut k hkP hkr).compl hsym

/-- Far sides are closed under the parent pointers other than their own edge. -/
private theorem GInv.mem_farSide_iff {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    {w : V → β} (I : GInv f r P p S w) {t k : V} (hk : k ∈ edgesAt r P p t) {z : V}
    (hzk : z ≠ k) :
    z ∈ farSide S t k ↔ p z ∈ farSide S t k := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  have hl := I.lam k hkP hkr z hzk
  unfold farSide
  split_ifs
  · rw [Finset.mem_compl, Finset.mem_compl, hl]
  · exact hl

/-- The child endpoint of a child edge `(k, t)` lies on its far side. -/
private theorem GInv.self_mem_farSide {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    {w : V → β} (I : GInv f r P p S w) {t k : V} (hk : k ∈ edgesAt r P p t) (htk : t ∉ S k) :
    k ∈ farSide S t k := by
  obtain ⟨hkP, hkr, -⟩ := mem_edgesAt.mp hk
  simp only [farSide, htk, ↓reduceIte]
  exact (I.cut k hkP hkr).left_mem

/-- The parent of `t` lies on the far side of the parent edge `(t, p t)`. -/
private theorem GInv.parent_mem_farSide {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    {w : V → β} (I : GInv f r P p S w) {t : V} (htP : t ∈ P) (htr : t ≠ r) :
    p t ∈ farSide S t t := by
  have hc := I.cut t htP htr
  simp only [farSide, hc.left_mem, ↓reduceIte, Finset.mem_compl]
  exact hc.right_notMem

/-- The far sides of distinct tree edges at `t` are disjoint: a vertex on both would be joined to
`t` by parent pointers inside both, but `t` lies on neither. -/
private theorem GInv.disjoint_farSide (hsym : ∀ X, f Xᶜ = f X) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} {w : V → β} (I : GInv f r P p S w) {t k k' : V}
    (hk : k ∈ edgesAt r P p t) (hk' : k' ∈ edgesAt r P p t) (hne : k ≠ k') :
    Disjoint (farSide S t k) (farSide S t k') := by
  have htA : ∀ {j}, j ∈ edgesAt r P p t → t ∉ farSide S t j := fun hj =>
    (I.isMinCutBetween_farSide hsym hj).right_notMem
  -- The child endpoint of one edge is not on the far side of another.
  have hnot : ∀ {j j'}, j ∈ edgesAt r P p t → j' ∈ edgesAt r P p t → j ≠ j' →
      j ∉ farSide S t j' := by
    intro j j' hj hj' hjj' hmem
    rcases I.edgesAt_cases hj with ⟨-, hpj⟩ | ⟨-, hjt⟩
    · exact htA hj' (hpj ▸ (I.mem_farSide_iff hj' hjj').mp hmem)
    · exact htA hj' (hjt ▸ hmem)
  rw [Finset.disjoint_left]
  intro z hz hz'
  let Y := farSide S t k ∩ farSide S t k'
  have hY : ∀ x, x ∈ Y ↔ p x ∈ Y := by
    intro x
    simp only [Y, Finset.mem_inter]
    obtain rfl | hxk := eq_or_ne x k
    · simp only [← I.mem_farSide_iff hk' hne, hnot hk hk' hne, and_false]
    obtain rfl | hxk' := eq_or_ne x k'
    · simp only [← I.mem_farSide_iff hk hne.symm, hnot hk' hk hne.symm, false_and]
    rw [I.mem_farSide_iff hk hxk, I.mem_farSide_iff hk' hxk']
  have hzt := mem_iff_of_reflTransGen_tAdj hY
    ((I.conn z).trans (reflTransGen_tAdj_symm (I.conn t)))
  exact htA hk (Finset.mem_inter.mp (hzt.mp (Finset.mem_inter.mpr ⟨hz, hz'⟩))).1

/-- **Coverage.** A vertex joined to `t` by parent pointers is `t`, an unprocessed child of `t`, or
on the far side of some tree edge at `t`. -/
private theorem GInv.cover {r : V} {P : Finset V} {p : V → V} {S : V → Finset V}
    {w₀ : V → β} (I : GInv f r P p S w₀) {t : V} (htP : t ∈ P) {w : V}
    (hw : Relation.ReflTransGen (TAdj p) w t) :
    (∃ k ∈ edgesAt r P p t, w ∈ farSide S t k) ∨ w = t ∨ (w ∉ P ∧ p w = t) := by
  induction hw using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inr (.inl rfl)
  | @head w c hwc _ ih =>
    rcases ih with ⟨k, hk, hck⟩ | hct | ⟨hcP, hpc⟩
    · -- `c` is on the far side of `(k, p k)`; so is `w` unless the step crosses that edge.
      obtain rfl | hwk := eq_or_ne w k
      · rcases I.edgesAt_cases hk with ⟨htk, -⟩ | ⟨-, hkt⟩
        · exact .inl ⟨w, hk, I.self_mem_farSide hk htk⟩
        · exact .inr (.inl hkt)
      rcases hwc with h | h
      · exact .inl ⟨k, hk, (I.mem_farSide_iff hk hwk).mpr (h ▸ hck)⟩
      · obtain rfl | hck' := eq_or_ne c k
        · rcases I.edgesAt_cases hk with ⟨-, hpk⟩ | ⟨htk, -⟩
          · exact .inr (.inl (h.symm.trans hpk))
          · obtain ⟨hcP, hcr, -⟩ := mem_edgesAt.mp hk
            simp only [farSide, htk, ↓reduceIte, Finset.mem_compl] at hck
            exact absurd (I.cut c hcP hcr).left_mem hck
        · exact .inl ⟨k, hk, h ▸ (I.mem_farSide_iff hk hck').mp hck⟩
    · -- `c = t`: `w` is a child of `t` or its parent.
      subst hct
      rcases hwc with h | h
      · by_cases hwP : w ∈ P
        · obtain rfl | hwr := eq_or_ne w r
          · exact .inr (.inl (h.symm.trans I.parent_root).symm)
          have hwK : w ∈ edgesAt r P p c := mem_edgesAt.mpr ⟨hwP, hwr, .inl h⟩
          rcases I.edgesAt_cases hwK with ⟨htw, -⟩ | ⟨-, hwc'⟩
          · exact .inl ⟨w, hwK, I.self_mem_farSide hwK htw⟩
          · exact .inr (.inl hwc')
        · exact .inr (.inr ⟨hwP, h⟩)
      · obtain rfl | hwt := eq_or_ne w c
        · exact .inr (.inl rfl)
        have htr : c ≠ r := fun htr => hwt (by rw [← h, htr, I.parent_root])
        exact .inl ⟨c, mem_edgesAt.mpr ⟨htP, htr, .inr rfl⟩, h ▸ I.parent_mem_farSide htP htr⟩
    · -- `c` is an unprocessed child of `t`, hence a leaf: `w` is its parent `t`.
      rcases hwc with h | h
      · exact absurd (h ▸ I.parent_mem w) hcP
      · exact .inr (.inl (h ▸ hpc))

end EdgesAt

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β}

/-- **Uncrossing step of Gusfield's algorithm.** Given the invariant, an unprocessed vertex `s`
with parent `t = p s` and a minimum `s`–`t` cut `X`, there is a minimum `s`–`t` cut `U` that agrees
with `X` on the vertices whose parent is `t` and on the parent of `t`, and that no other parent
pointer crosses. -/
private theorem exists_uncrossed (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) {r : V}
    {P : Finset V} {p : V → V} {S : V → Finset V} {w : V → β} (I : GInv f r P p S w) {s t : V}
    (hsP : s ∉ P) (ht : p s = t) {X : Finset V} (hX : IsMinCutBetween f s t X) :
    ∃ U, IsMinCutBetween f s t U ∧ (∀ z, p z = t → (z ∈ U ↔ z ∈ X)) ∧
      (p t ∈ U ↔ p t ∈ X) ∧ (∀ z, z ≠ t → p z ≠ t → (z ∈ U ↔ p z ∈ U)) := by
  have htP : t ∈ P := ht ▸ I.parent_mem s
  let K := edgesAt r P p t
  let a := farEnd p S t
  let A := farSide S t
  have htA : ∀ k ∈ K, t ∉ A k := fun k hk => (I.isMinCutBetween_farSide hsym hk).right_notMem
  -- `s` is on no far side: it hangs from `t`, which is on none.
  have hsA : ∀ k ∈ K, s ∉ A k := by
    intro k hk hs
    have hsk : s ≠ k := fun h => hsP (h ▸ (mem_edgesAt.mp hk).1)
    exact htA k hk (ht ▸ (I.mem_farSide_iff hk hsk).mp hs)
  -- The uncrossed cut.
  let ks := K.toList
  have hks : ∀ k, k ∈ ks ↔ k ∈ K := fun k => Finset.mem_toList
  have hpw : ks.Pairwise fun i j => Disjoint (A i) (A j) :=
    (Finset.nodup_toList K).pairwise_of_forall_ne fun i hi j hj hij =>
      I.disjoint_farSide hsym ((hks i).mp hi) ((hks j).mp hj) hij
  let U := uncrossList X a A ks
  have U0 : IsMinCutBetween f s t U :=
    isMinCutBetween_uncrossList hsym hsub hX
      (fun k hk => I.isMinCutBetween_farSide hsym ((hks k).mp hk))
      (fun k hk => hsA k ((hks k).mp hk)) hpw
  have M1 : ∀ k ∈ K, ∀ z ∈ A k, (z ∈ U ↔ a k ∈ X) := fun k hk z hz =>
    mem_uncrossList_of_mem hpw ((hks k).mpr hk) hz
  have M2 : ∀ z, (∀ k ∈ K, z ∉ A k) → (z ∈ U ↔ z ∈ X) := fun z hz =>
    mem_uncrossList_of_forall_notMem fun k hk => hz k ((hks k).mp hk)
  refine ⟨U, U0, ?_, ?_, ?_⟩
  · -- A processed child `z` of `t` lies on its own far side, whose far end is `z`; an unprocessed
    -- one lies on no far side.
    intro z hz
    obtain rfl | hzt := eq_or_ne z t
    · exact iff_of_false U0.right_notMem hX.right_notMem
    by_cases hzP : z ∈ P
    · have hzr : z ≠ r := fun hzr => hzt (by rw [← hz, hzr, I.parent_root])
      have hzK : z ∈ K := mem_edgesAt.mpr ⟨hzP, hzr, .inl hz⟩
      rcases I.edgesAt_cases hzK with ⟨htz, -⟩ | ⟨-, hzt'⟩
      · simpa only [a, farEnd, htz, ↓reduceIte] using M1 z hzK z (I.self_mem_farSide hzK htz)
      · exact absurd hzt' hzt
    · refine M2 z fun k hk hzA => ?_
      have hzk : z ≠ k := fun h => hzP (h ▸ (mem_edgesAt.mp hk).1)
      exact htA k hk (hz ▸ (I.mem_farSide_iff hk hzk).mp hzA)
  · -- The parent of `t` lies on the far side of `(t, p t)`, whose far end is `p t`.
    obtain rfl | htr := eq_or_ne t r
    · rw [I.parent_root]
      exact iff_of_false U0.right_notMem hX.right_notMem
    have htK : t ∈ K := mem_edgesAt.mpr ⟨htP, htr, .inr rfl⟩
    have htt : t ∈ S t := (I.cut t htP htr).left_mem
    simpa only [a, farEnd, htt, ↓reduceIte] using M1 t htK (p t) (I.parent_mem_farSide htP htr)
  · -- Any other `z` lies on the same far side as `p z`.
    intro z hzt hpz
    rcases I.cover htP ((I.conn z).trans (reflTransGen_tAdj_symm (I.conn t))) with
      ⟨k, hk, hzk⟩ | h | ⟨-, h⟩
    · have hzk' : z ≠ k := fun h =>
        (mem_edgesAt.mp hk).2.2.elim (fun h' => hpz (h ▸ h')) fun h' => hzt (h.trans h')
      rw [M1 k hk z hzk, M1 k hk (p z) ((I.mem_farSide_iff hk hzk').mp hzk)]
    · exact absurd h hzt
    · exact absurd h hpz

/-- **Gusfield's step preserves the invariant.** -/
private theorem gInv_step (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f) {r : V} {P : Finset V}
    {p : V → V} {S : V → Finset V} {w : V → β} (I : GInv f r P p S w) {s : V} (hsP : s ∉ P)
    {X : Finset V} (hX : IsMinCutBetween f s (p s) X) {v : β} (hval : v = f X) :
    ∃ S', GInv f r (insert s P) (gusfieldStep p s X) S' (gusfieldStepWeight p w s X v) ∧
      gusfieldStepWeight p w s X v r = w r := by
  set t := p s
  have ht : p s = t := rfl
  obtain ⟨U, U0, U1, U2, U3⟩ := exists_uncrossed hsym hsub I hsP ht hX
  have htP : t ∈ P := I.parent_mem s
  have hst : s ≠ t := hX.ne
  have hsr : s ≠ r := fun h => hsP (h ▸ I.root_mem)
  have hsS : ∀ i ∈ P, i ≠ r → (s ∈ S i ↔ t ∈ S i) := fun i hi hir =>
    I.lam i hi hir s fun h => hsP (h ▸ hi)
  set q := gusfieldStep p s X with hq
  have qs : q s = if p t ∈ X then p t else t := by simp [hq, gusfieldStep, ht]
  have qt : q t = if p t ∈ X then s else p t := by simp [hq, gusfieldStep, Ne.symm hst, ht]
  have qz (z : V) (hzs : z ≠ s) (hzt : z ≠ t) : q z = if p z = t ∧ z ∈ X then s else p z := by
    simp [hq, gusfieldStep, hzs, ht, hzt]
  -- Vertices other than `s, t` keep their side of every set that `s, t` do not separate.
  have hgen (Y : Finset V) (hY : s ∈ Y ↔ t ∈ Y) (z : V) (hzs : z ≠ s) (hzt : z ≠ t)
      (hz : z ∈ Y ↔ p z ∈ Y) : z ∈ Y ↔ q z ∈ Y := by
    rw [qz z hzs hzt]
    split_ifs with h
    · rw [hz, h.1, ← hY]
    · exact hz
  have hgenU (z : V) (hzs : z ≠ s) (hzt : z ≠ t) : z ∈ U ↔ q z ∈ U := by
    rw [qz z hzs hzt]
    split_ifs with h
    · exact iff_of_true ((U1 z h.1).mpr h.2) U0.left_mem
    · by_cases hpz : p z = t
      · rw [hpz]
        exact iff_of_false (fun hzU => h ⟨hpz, (U1 z hpz).mp hzU⟩) U0.right_notMem
      · exact U3 z hzt hpz
  -- Facts shared by both cases.
  have hmem : ∀ z, q z ∈ insert s P := fun z => by
    simp only [hq, gusfieldStep]
    split_ifs <;> simp [I.parent_mem]
  have hqr : q r = r := by
    by_cases htr : r = t
    · have hpt : p t = t := htr ▸ I.parent_root
      rw [htr, qt, hpt, ite_eq_right hX.right_notMem]
    · rw [qz r (Ne.symm hsr) htr, ite_eq_right fun h => htr (I.parent_root ▸ h.1), I.parent_root]
  have hcut_other (i : V) (hiP : i ∈ P) (hir : i ≠ r) (his : i ≠ s) (hit : i ≠ t) :
      IsMinCutBetween f i (q i) (S i) := by
    rw [qz i his hit]
    split_ifs with h
    · -- `i` is re-hung below `s`.
      have hc : IsMinCutBetween f i t (S i) := h.1 ▸ I.cut i hiP hir
      exact isMinCutBetween_rehang hsym hc U0 ((hsS i hiP hir).not.mpr hc.right_notMem)
        ((U1 i h.1).mpr h.2)
    · exact I.cut i hiP hir
  have hconn_other (z : V) (hzs : z ≠ s) (hzt : z ≠ t) (hst' : TAdj q s t) :
      Relation.ReflTransGen (TAdj q) z (p z) := by
    have hqz := qz z hzs hzt
    split_ifs at hqz with h
    · exact h.1.symm ▸ (Relation.ReflTransGen.single (show TAdj q z s from Or.inl hqz)).tail hst'
    · exact Relation.ReflTransGen.single (Or.inl hqz)
  have hfUX : f U = f X :=
    le_antisymm (U0.le hX.left_mem hX.right_notMem) (hX.le U0.left_mem U0.right_notMem)
  have hne_s : ∀ {i}, i ∈ P → i ≠ s := fun hi h => hsP (h ▸ hi)
  by_cases hswap : p t ∈ X
  · -- `s` takes the place of `t`.
    have htr : t ≠ r := fun htr => hX.right_notMem (by rwa [htr, ← I.parent_root, ← htr])
    have hct := I.cut t htP htr
    have qs' : q s = p t := by rw [qs, ite_eq_left hswap]
    have qt' : q t = s := by rw [qt, ite_eq_left hswap]
    refine ⟨Function.update (Function.update S s (S t)) t Uᶜ,
      ⟨Finset.mem_insert_of_mem I.root_mem, hqr, hmem, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro i hi hir
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · rw [qs', Function.update_of_ne hst, Function.update_self]
        exact isMinCutBetween_swap hsym hct U0 ((hsS t htP htr).mpr hct.left_mem) (U2.mpr hswap)
      rcases eq_or_ne i t with rfl | hit
      · simpa only [qt', Function.update_self] using U0.compl hsym
      simpa only [Function.update_of_ne hit, Function.update_of_ne (hne_s hiP)] using
        hcut_other i hiP hir (hne_s hiP) hit
    · rintro i hi hir z hzi
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · rw [Function.update_of_ne hst, Function.update_self]
        rcases eq_or_ne z t with rfl | hzt
        · simp only [qt', hct.left_mem, (hsS t htP htr).mpr hct.left_mem]
        · exact hgen (S t) (hsS t htP htr) z hzi hzt (I.lam t htP htr z hzt)
      rcases eq_or_ne i t with rfl | hit
      · rw [Function.update_self]
        rcases eq_or_ne z s with rfl | hzs
        · simp only [qs', Finset.mem_compl, U0.left_mem, U2.mpr hswap]
        · simpa only [Finset.mem_compl] using not_congr (hgenU z hzs hzi)
      rw [Function.update_of_ne hit, Function.update_of_ne (hne_s hiP)]
      rcases eq_or_ne z s with rfl | hzs
      · simpa only [qs', hsS i hiP hir] using I.lam i hiP hir t hit.symm
      rcases eq_or_ne z t with rfl | hzt
      · rw [qt', hsS i hiP hir]
      exact hgen (S i) (hsS i hiP hir) z hzs hzt (I.lam i hiP hir z hzi)
    · rintro i hi hir
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · simp only [Function.update_of_ne hst, Function.update_self, gusfieldStepWeight, ht,
          hswap, ↓reduceIte, I.weight t htP htr]
      rcases eq_or_ne i t with rfl | hit
      · simp only [Function.update_self, gusfieldStepWeight, ht, hswap, hst.symm, ↓reduceIte,
          hval, ← hfUX, hsym U]
      simp only [Function.update_of_ne hit, Function.update_of_ne (hne_s hiP), gusfieldStepWeight,
        ht, hswap, hne_s hiP, hit, ↓reduceIte, I.weight i hiP hir]
    · refine reflTransGen_tAdj_of_step I.conn fun z => ?_
      rcases eq_or_ne z s with rfl | hzs
      · exact ht ▸ Relation.ReflTransGen.single (Or.inr qt')
      rcases eq_or_ne z t with rfl | hzt
      · exact (Relation.ReflTransGen.single (show TAdj q _ s from Or.inl qt')).tail
          (show TAdj q s _ from Or.inl qs')
      exact hconn_other z hzs hzt (Or.inr qt')
    · rw [gusfieldStepWeight, ht, ite_eq_left hswap, ite_eq_right (Ne.symm hsr),
        ite_eq_right (Ne.symm htr)]
  · -- `s` is hung below `t`.
    have qs' : q s = t := by rw [qs, ite_eq_right hswap]
    have qt' : q t = p t := by rw [qt, ite_eq_right hswap]
    refine ⟨Function.update S s U,
      ⟨Finset.mem_insert_of_mem I.root_mem, hqr, hmem, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro i hi hir
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · simpa only [qs', Function.update_self] using U0
      rw [Function.update_of_ne (hne_s hiP)]
      rcases eq_or_ne i t with rfl | hit
      · exact qt' ▸ I.cut t hiP hir
      exact hcut_other i hiP hir (hne_s hiP) hit
    · rintro i hi hir z hzi
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · rw [Function.update_self]
        rcases eq_or_ne z t with rfl | hzt
        · simp only [qt', U0.right_notMem, mt U2.mp hswap]
        · exact hgenU z hzi hzt
      rw [Function.update_of_ne (hne_s hiP)]
      rcases eq_or_ne z s with rfl | hzs
      · exact qs' ▸ hsS i hiP hir
      rcases eq_or_ne z t with rfl | hzt
      · exact qt' ▸ I.lam i hiP hir _ hzi
      exact hgen (S i) (hsS i hiP hir) z hzs hzt (I.lam i hiP hir z hzi)
    · rintro i hi hir
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · rw [Function.update_self, gusfieldStepWeight, ht, ite_eq_right hswap,
          ite_eq_left rfl, hval, ← hfUX]
      rw [Function.update_of_ne (hne_s hiP), gusfieldStepWeight, ht, ite_eq_right hswap,
        ite_eq_right (hne_s hiP)]
      exact I.weight i hiP hir
    · refine reflTransGen_tAdj_of_step I.conn fun z => ?_
      rcases eq_or_ne z s with rfl | hzs
      · exact ht ▸ Relation.ReflTransGen.single (Or.inl qs')
      rcases eq_or_ne z t with rfl | hzt
      · exact Relation.ReflTransGen.single (Or.inl qt')
      exact hconn_other z hzs hzt (Or.inl qs')
    · rw [gusfieldStepWeight, ht, ite_eq_right hswap, ite_eq_right (Ne.symm hsr)]

/-- Gusfield's loop preserves the invariant. -/
private theorem gInv_loop (hsym : ∀ X, f Xᶜ = f X) (hsub : IsSubmodular f)
    {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) {r : V} :
    ∀ (l : List V) {P : Finset V} {p : V → V} {S : V → Finset V} {w : V → β},
      GInv f r P p S w → l.Nodup → (∀ x ∈ l, x ∉ P ∨ x = r) →
      ∃ S', GInv f r (P ∪ l.toFinset) (gusfieldWeightLoop C val r l p w).1 S'
        (gusfieldWeightLoop C val r l p w).2 ∧
        (gusfieldWeightLoop C val r l p w).2 r = w r
  | [], P, p, S, w, I, _, _ =>
    ⟨S, by rw [gusfieldWeightLoop, List.toFinset_nil, Finset.union_empty]; exact I, rfl⟩
  | s :: l, P, p, S, w, I, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have hset : P ∪ (s :: l).toFinset = insert s P ∪ l.toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    by_cases hsr : s = r
    · have hl' : ∀ x ∈ l, x ∉ P ∨ x = r := fun x hx => hl x (List.mem_cons_of_mem s hx)
      obtain ⟨S', I', hwr⟩ := gInv_loop hsym hsub hC hval l I hnd.2 hl'
      have hins : insert s P = P := Finset.insert_eq_of_mem (hsr ▸ I.root_mem)
      refine ⟨S', ?_, ?_⟩ <;> rw [gusfieldWeightLoop, ite_eq_left hsr]
      exacts [by rwa [hset, hins], hwr]
    · have hsP : s ∉ P := (hl s (List.mem_cons_self)).resolve_right hsr
      have hsp : s ≠ p s := fun h => hsP (h ▸ I.parent_mem s)
      obtain ⟨S₁, I₁, hw1⟩ :=
        gInv_step hsym hsub I hsP (hC s (p s) hsp) (hval s (p s) hsp)
      have hl' : ∀ x ∈ l, x ∉ insert s P ∨ x = r := fun x hx =>
        (hl x (List.mem_cons_of_mem s hx)).imp_left fun h hm =>
          (Finset.mem_insert.mp hm).elim (fun hxs => hnd.1 (hxs ▸ hx)) h
      obtain ⟨S', I', hwr⟩ := gInv_loop hsym hsub hC hval l I₁ hnd.2 hl'
      refine ⟨S', ?_, ?_⟩ <;> rw [gusfieldWeightLoop, ite_eq_right hsr]
      exacts [hset ▸ I', hwr.trans hw1]

end Step

/-! ### Correctness -/

section Correct

variable [Fintype V] [DecidableEq V] [Preorder β] {f : Finset V → β}

omit [DecidableEq V] in
/-- The side of a parent edge `(u, p u)` of the final tree is the label `S u`. -/
private theorem gInv_edgeSide_eq {r : V} {p : V → V} {S : V → Finset V} {w : V → β}
    (I : GInv f r Finset.univ p S w) (hT : (parentGraph p).IsTree) {u : V} (hur : u ≠ r)
    (hadj : (parentGraph p).Adj u (p u)) : edgeSide (parentGraph p) u (p u) = S u := by
  have hc := I.cut u (Finset.mem_univ u) hur
  refine edgeSide_eq_of_forall_adj hT hadj hc.left_mem hc.right_notMem fun x y hxy hne => ?_
  rcases (parentGraph_adj.mp hxy).2 with rfl | rfl
  · exact I.lam u (Finset.mem_univ u) hur x fun h => hne (h ▸ rfl)
  · exact (I.lam u (Finset.mem_univ u) hur y fun h => hne (h ▸ Sym2.eq_swap)).symm

/-- **The final invariant yields a Gomory–Hu tree** whose parent edges carry the cuts `S u` and
weights `w u = f (edgeSide (parentGraph p) u (p u))`. -/
private theorem gInv_isGomoryHuTree (hsym : ∀ X, f Xᶜ = f X) {r : V} {p : V → V} {S : V → Finset V}
    {w : V → β} (I : GInv f r Finset.univ p S w) :
    IsGomoryHuTree f (parentGraph p) ∧
      (∀ u, u ≠ r → IsMinCutBetween f u (p u) (edgeSide (parentGraph p) u (p u)) ∧
        w u = f (edgeSide (parentGraph p) u (p u))) := by
  classical
  have hne : ∀ x, x ≠ r → p x ≠ x := fun x hx h =>
    (I.cut x (Finset.mem_univ x) hx).ne h.symm
  have hreach (x : V) : (parentGraph p).Reachable x r := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine Relation.reflTransGen_closed (fun a b hab => ?_) _ _ (I.conn x)
    rcases eq_or_ne a b with rfl | heq
    exacts [.refl, .single (parentGraph_adj.mpr ⟨heq, hab⟩)]
  have hconn : (parentGraph p).Connected :=
    { preconnected := fun x y => (hreach x).trans (hreach y).symm
      nonempty := ⟨r⟩ }
  have hedge : (parentGraph p).edgeFinset =
      (Finset.univ.erase r).image fun i => s(i, p i) := by
    ext e
    induction e using Sym2.ind with | _ x y => ?_
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parentGraph_adj, Finset.mem_image]
    constructor
    · rintro ⟨hxy, rfl | rfl⟩
      · exact ⟨x, Finset.mem_erase.mpr ⟨fun hxr => hxy (hxr ▸ I.parent_root).symm,
          Finset.mem_univ x⟩, rfl⟩
      · exact ⟨y, Finset.mem_erase.mpr ⟨fun hyr => hxy (hyr ▸ I.parent_root),
          Finset.mem_univ y⟩, Sym2.eq_swap⟩
    · rintro ⟨i, hi, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(hne i (Finset.mem_erase.mp hi).1).symm, Or.inl rfl⟩
      · exact ⟨hne i (Finset.mem_erase.mp hi).1, Or.inr rfl⟩
  have hinj : Set.InjOn (fun i => s(i, p i)) ↑(Finset.univ.erase r) := by
    intro i hi j _ hij
    replace hi := (Finset.mem_erase.mp (Finset.mem_coe.mp hi)).1
    rcases Sym2.eq_iff.mp hij with ⟨h, -⟩ | ⟨h1, rfl⟩
    · exact h
    · have hc := I.cut i (Finset.mem_univ i) hi
      exact absurd ((I.lam i (Finset.mem_univ i) hi (p i) (hne i hi)).mpr (h1 ▸ hc.left_mem))
        hc.right_notMem
  have htree : (parentGraph p).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
      ← SimpleGraph.edgeFinset_card, hedge, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Nat.card_eq_fintype_card]
    have := Fintype.card_pos_iff.mpr ⟨r⟩
    exact ⟨hconn, by omega⟩
  refine ⟨⟨htree, fun u v huv => ?_⟩, fun u hur => ?_⟩
  · rcases (parentGraph_adj.mp huv).2 with rfl | rfl
    · have hur : u ≠ r := fun hur => (parentGraph_adj.mp huv).1 (by rw [hur, I.parent_root])
      rw [gInv_edgeSide_eq I htree hur huv]
      exact I.cut u (Finset.mem_univ u) hur
    · have hvr : v ≠ r := fun hvr => (parentGraph_adj.mp huv).1 (by rw [hvr, I.parent_root])
      rw [edgeSide_swap htree huv.symm, gInv_edgeSide_eq I htree hvr huv.symm]
      exact (I.cut v (Finset.mem_univ v) hvr).compl hsym
  · rw [gInv_edgeSide_eq I htree hur (parentGraph_adj.mpr ⟨(hne u hur).symm, Or.inl rfl⟩)]
    exact ⟨I.cut u (Finset.mem_univ u) hur, I.weight u (Finset.mem_univ u) hur⟩

end Correct

private theorem gInv_gusfieldWithWeights [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) (r : V) (w₀ : β) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) :
    let res := gusfieldWithWeights C val r w₀ l
    ∃ S, GInv f r Finset.univ res.1 S res.2 ∧ res.2 r = w₀ := by
  obtain ⟨S, I, hwr⟩ := gInv_loop hsym hsub hC hval l (gInv_init f r (fun _ => ∅) fun _ => w₀)
    hnd fun x _ => if hx : x = r then Or.inr hx else Or.inl (hx ∘ Finset.mem_singleton.mp)
  have huniv : ({r} : Finset V) ∪ l.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => by
      by_cases hx : x = r <;> simp [hx, hl]
  exact ⟨S, huniv ▸ I, hwr⟩

/-- **Correctness of Gusfield's algorithm** ([Gusfield1990]). For a symmetric submodular `f`, a
cut oracle `C` returning a minimum `s`–`t` cut for all `s ≠ t`, a root `r` and a duplicate-free
list `l` containing every vertex other than `r`, the parent function computed by Gusfield's
algorithm is a Gomory–Hu tree of `f`. -/
theorem isGomoryHuTree_gusfieldParent [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) (r : V) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) : IsGomoryHuTree f (parentGraph (gusfieldParent C r l)) := by
  rw [← fst_gusfieldWithWeights C (fun s t => f (C s t)) r (f ∅) l]
  obtain ⟨_, I, -⟩ :=
    gInv_gusfieldWithWeights hsym hsub hC (fun _ _ _ => rfl) r (f ∅) hnd hl
  exact (gInv_isGomoryHuTree hsym I).1

/-- The root `r` remains its own parent in `gusfieldParent`. -/
private theorem gusfieldParent_root [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) (r : V) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) :
    gusfieldParent C r l r = r := by
  rw [← fst_gusfieldWithWeights C (fun s t => f (C s t)) r (f ∅) l]
  obtain ⟨_, I, -⟩ :=
    gInv_gusfieldWithWeights hsym hsub hC (fun _ _ _ => rfl) r (f ∅) hnd hl
  exact I.parent_root

/-- **Bundled correctness of Gusfield's algorithm with edge weights** ([Gusfield1990]): for a
symmetric submodular `f`, cut oracle `C`, consistent value oracle `val s t = f (C s t)`, root `r`,
initial weight `w₀` and duplicate-free list `l` covering `V \ {r}`, `gusfieldWithWeights` produces
a Gomory–Hu parent graph with fixed root `r`, root weight `w₀`, and non-root weights equal to `f`
on each tree-edge side. -/
theorem gusfieldWithWeights_spec [Fintype V] [DecidableEq V] [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) (r : V) (w₀ : β) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) :
    let res := gusfieldWithWeights C val r w₀ l
    IsGomoryHuTree f (parentGraph res.1) ∧ res.1 r = r ∧ res.2 r = w₀ ∧
      ∀ u, u ≠ r →
        IsMinCutBetween f u (res.1 u) (edgeSide (parentGraph res.1) u (res.1 u)) ∧
          res.2 u = f (edgeSide (parentGraph res.1) u (res.1 u)) := by
  obtain ⟨S, I, hwr⟩ := gInv_gusfieldWithWeights hsym hsub hC hval r w₀ hnd hl
  obtain ⟨htree, hside⟩ := gInv_isGomoryHuTree hsym I
  exact ⟨htree, I.parent_root, hwr, fun u hur => hside u hur⟩

/-- **Correctness of Gusfield's algorithm with edge weights** ([Gusfield1990]): for a symmetric
submodular `f`, a cut oracle `C` returning minimum cuts, a root `r` and a duplicate-free list `l`
covering `V \ {r}`, the parent component of `gusfieldWithWeights` is a Gomory–Hu tree of `f`. -/
theorem isGomoryHuTree_gusfieldWithWeights [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) (r : V) (w₀ : β) {l : List V}
    (hnd : l.Nodup) (hl : ∀ x, x ≠ r → x ∈ l) :
    IsGomoryHuTree f (parentGraph (gusfieldWithWeights C val r w₀ l).1) := by
  rw [fst_gusfieldWithWeights]
  exact isGomoryHuTree_gusfieldParent hsym hsub hC r hnd hl

/-- For every non-root vertex `u`, the tree-edge side containing `u` in `gusfieldWithWeights` is a
minimum `u`–`p u` cut of `f`. -/
theorem isMinCutBetween_gusfieldWithWeights_edgeSide [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) (r : V) (w₀ : β) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) {u : V} (hur : u ≠ r) :
    let res := gusfieldWithWeights C val r w₀ l
    IsMinCutBetween f u (res.1 u) (edgeSide (parentGraph res.1) u (res.1 u)) :=
  ((gusfieldWithWeights_spec hsym hsub hC hval r w₀ hnd hl).2.2.2 u hur).1

/-- **Edge-weight correctness of Gusfield's algorithm** ([Gusfield1990]): for every non-root vertex
`u`, the weight recorded by `gusfieldWithWeights` equals `f` on the tree-edge side containing
`u`. -/
theorem gusfieldWithWeights_weight_eq [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) (r : V) (w₀ : β) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) {u : V} (hur : u ≠ r) :
    let res := gusfieldWithWeights C val r w₀ l
    res.2 u = f (edgeSide (parentGraph res.1) u (res.1 u)) :=
  ((gusfieldWithWeights_spec hsym hsub hC hval r w₀ hnd hl).2.2.2 u hur).2

/-- The root `r` remains its own parent in `gusfieldWithWeights`. -/
theorem gusfieldWithWeights_parent_root [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t)) (r : V) (w₀ : β) {l : List V}
    (hnd : l.Nodup) (hl : ∀ x, x ≠ r → x ∈ l) :
    (gusfieldWithWeights C val r w₀ l).1 r = r := by
  rw [fst_gusfieldWithWeights]
  exact gusfieldParent_root hsym hsub hC r hnd hl

/-- The weight recorded at the root `r` in `gusfieldWithWeights` equals the initial weight `w₀`. -/
theorem gusfieldWithWeights_weight_root [Fintype V] [DecidableEq V] [AddCommMonoid β]
    [LinearOrder β] [IsOrderedCancelAddMonoid β] {f : Finset V → β} (hsym : ∀ X, f Xᶜ = f X)
    (hsub : IsSubmodular f) {C : V → V → Finset V} {val : V → V → β}
    (hC : ∀ s t, s ≠ t → IsMinCutBetween f s t (C s t))
    (hval : ∀ s t, s ≠ t → val s t = f (C s t)) (r : V) (w₀ : β) {l : List V} (hnd : l.Nodup)
    (hl : ∀ x, x ≠ r → x ∈ l) :
    (gusfieldWithWeights C val r w₀ l).2 r = w₀ :=
  (gusfieldWithWeights_spec hsym hsub hC hval r w₀ hnd hl).2.2.1

end Cslib.Algorithms.Lean.GomoryHu
