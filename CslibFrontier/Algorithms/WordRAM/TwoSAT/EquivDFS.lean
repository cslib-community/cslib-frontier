/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.CSR
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Defs

/-!
# Literal-index bijection and `DFS` / `CSR` transport lemmas

Transports `dfs`, `topologicalSort`, `transposeAdj`, `sccs`, `indexComponents`, and
`addClauseEdges` across `litEquiv n : Literal (Fin n) ≃ Fin (2 * n)`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL
open Cslib.Algorithms.Lean.DFS Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode Cslib.Algorithms.WordRAM.DFS

theorem litCodeBy_fin_lt {n : ℕ} (ℓ : Literal (Fin n)) :
    litCodeBy Fin.val ℓ < 2 * n := by
  have hv := ℓ.1.isLt
  have hb := Bool.toNat_le ℓ.2
  unfold litCodeBy
  omega

/-- Bijection identifying `Literal (Fin n)` with `Fin (2 * n)` via `2 * v.val + b.toNat`. -/
@[expose] def litEquiv (n : ℕ) : Literal (Fin n) ≃ Fin (2 * n) where
  toFun ℓ := ⟨litCodeBy Fin.val ℓ, litCodeBy_fin_lt ℓ⟩
  invFun u := (⟨u.val / 2, by omega⟩, decide (u.val % 2 = 1))
  left_inv := by
    rintro ⟨⟨v, hv⟩, b⟩
    have hdiv1 : (2 * v + 1) / 2 = v := by omega
    have hmod1 : (2 * v + 1) % 2 = 1 := by omega
    cases b with
    | false => simp [litCodeBy]
    | true => simp [litCodeBy, hdiv1, hmod1]
  right_inv := by
    rintro ⟨u, hu⟩
    simp only [litCodeBy, Fin.mk.injEq]
    by_cases hmod : u % 2 = 1
    · simp only [hmod, decide_true, Bool.toNat_true]
      omega
    · simp only [hmod, decide_false, Bool.toNat_false]
      omega

private theorem getElem_literalList {V : Type*} :
    ∀ (vs : List V) (k : ℕ) (hk : k < (literalList vs).length),
      (literalList vs)[k] =
        (vs[k / 2]'(by rw [length_literalList] at hk; omega), decide (k % 2 = 1))
  | [], k, hk => by simp [literalList] at hk
  | v :: vs, 0, _ => rfl
  | v :: vs, 1, _ => rfl
  | v :: vs, k + 2, hk => by
    simp only [literalList, List.length_cons] at hk
    have hk' : k < (literalList vs).length := by omega
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    have hmod : (k + 2) % 2 = k % 2 := by omega
    change (literalList vs)[k] = _
    rw [getElem_literalList vs k hk']
    simp only [hmod, Prod.mk.injEq, and_true]
    simp [hdiv]

private theorem map_litEquiv_literalList_finRange (n : ℕ) :
    (literalList (List.finRange n)).map (litEquiv n) = List.finRange (2 * n) := by
  refine List.ext_getElem ?_ fun k hk₁ hk₂ => ?_
  · simp [length_literalList]
  · simp only [List.getElem_map, List.getElem_finRange]
    rw [getElem_literalList]
    simp only [List.getElem_finRange]
    exact (litEquiv n).apply_symm_apply ⟨k, by simpa using hk₂⟩

section EquivDFS

/-- Push an adjacency list function forward along an equivalence `e`. -/
@[expose] def mapAdj {α β : Type*} (e : α ≃ β) (g : α → List α) : β → List β :=
  fun u => (g (e.symm u)).map e

theorem mapAdj_apply {α β : Type*} (e : α ≃ β) (g : α → List α) (x : α) :
    mapAdj e g (e x) = (g x).map e := by
  simp [mapAdj]

private theorem foldl_visit_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) {k : ℕ}
    (hstep : ∀ u (s : Cslib.Algorithms.Lean.DFS.State α),
      visit (mapAdj e g) k (e u) ⟨s.visited.map e.toEmbedding, s.finished.map e⟩ =
        ⟨(visit g k u s).visited.map e.toEmbedding, (visit g k u s).finished.map e⟩) :
    ∀ (l : List α) (s : Cslib.Algorithms.Lean.DFS.State α),
      (l.map e).foldl (fun st w => visit (mapAdj e g) k w st)
          ⟨s.visited.map e.toEmbedding, s.finished.map e⟩ =
        ⟨(l.foldl (fun st v => visit g k v st) s).visited.map e.toEmbedding,
          (l.foldl (fun st v => visit g k v st) s).finished.map e⟩
  | [], _ => rfl
  | v :: l, s => by
    simp only [List.map_cons, List.foldl_cons, hstep v s]
    exact foldl_visit_mapAdj e g hstep l (visit g k v s)

private theorem visit_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) :
    ∀ (k : ℕ) (u : α) (s : Cslib.Algorithms.Lean.DFS.State α),
      visit (mapAdj e g) k (e u) ⟨s.visited.map e.toEmbedding, s.finished.map e⟩ =
        ⟨(visit g k u s).visited.map e.toEmbedding, (visit g k u s).finished.map e⟩
  | 0, _, _ => rfl
  | k + 1, u, s => by
    by_cases hu : u ∈ s.visited
    · have heu : e u ∈ s.visited.map e.toEmbedding := Finset.mem_map_of_mem e.toEmbedding hu
      simp only [visit, hu, heu, ↓reduceIte]
    · have heu : e u ∉ s.visited.map e.toEmbedding := by
        simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hu
      have hins : insert (e u) (s.visited.map e.toEmbedding) =
          (insert u s.visited).map e.toEmbedding :=
        (Finset.map_insert e.toEmbedding u s.visited).symm
      have hstep := foldl_visit_mapAdj e g (visit_mapAdj e g k) (g u)
        ⟨insert u s.visited, s.finished⟩
      simp only [visit, hu, heu, ↓reduceIte, mapAdj_apply, hins]
      rw [hstep]
      rfl

private theorem dfs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (k : ℕ) (rs : List α) :
    dfs (mapAdj e g) k (rs.map e) =
      ⟨(dfs g k rs).visited.map e.toEmbedding, (dfs g k rs).finished.map e⟩ := by
  simpa only [dfs, Finset.map_empty, List.map_nil] using
    foldl_visit_mapAdj e g (visit_mapAdj e g k) rs ⟨∅, []⟩

private theorem topologicalSort_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    topologicalSort (mapAdj e g) (vs.map e) = (topologicalSort g vs).map e := by
  simp [topologicalSort, dfs_mapAdj]

theorem mapAdj_update_cons {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (rev : α → List α) (v u : α) :
    Function.update (mapAdj e rev) (e v) (e u :: mapAdj e rev (e v)) =
      mapAdj e (Function.update rev v (u :: rev v)) := by
  funext w
  by_cases hw : w = e v
  · subst hw
    simp [mapAdj]
  · have hsym : e.symm w ≠ v := fun h => hw (by rw [← h, e.apply_symm_apply])
    simp [mapAdj, Function.update_of_ne hw, Function.update_of_ne hsym]

private theorem transposeAdj_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    transposeAdj (mapAdj e g) (vs.map e) = mapAdj e (transposeAdj g vs) := by
  unfold transposeAdj
  have hinner (u : α) (l : List α) : ∀ rev : α → List α,
      (l.map e).foldl (fun r w => Function.update r w (e u :: r w)) (mapAdj e rev) =
        mapAdj e (l.foldl (fun r v => Function.update r v (u :: r v)) rev) := by
    induction l with
    | nil => exact fun _ => rfl
    | cons v l ih => exact fun rev => by simp [mapAdj_update_cons, ih]
  have houter (l : List α) : ∀ rev : α → List α,
      (l.map e).foldl
          (fun r u => (mapAdj e g u).foldl (fun r w => Function.update r w (u :: r w)) r)
          (mapAdj e rev) =
        mapAdj e (l.foldl
          (fun r u => (g u).foldl (fun r v => Function.update r v (u :: r v)) r) rev) := by
    induction l with
    | nil => exact fun _ => rfl
    | cons u l ih => exact fun rev => by simp [mapAdj_apply, hinner, ih]
  exact houter vs (fun _ => [])

private theorem peelSCCs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (rev : α → List α) (k : ℕ) :
    ∀ (vis : Finset α) (rs : List α),
      peelSCCs (mapAdj e rev) k (vis.map e.toEmbedding) (rs.map e) =
        (peelSCCs rev k vis rs).map (List.map e)
  | _, [] => rfl
  | vis, r :: rs => by
    have hv := visit_mapAdj e rev k r ⟨vis, []⟩
    change (let s := visit (mapAdj e rev) k (e r) ⟨vis.map e.toEmbedding, ([] : List α).map e⟩
        if s.finished.isEmpty then peelSCCs (mapAdj e rev) k s.visited (rs.map e)
        else s.finished :: peelSCCs (mapAdj e rev) k s.visited (rs.map e)) = _
    rw [hv]
    dsimp only [peelSCCs]
    rw [List.isEmpty_map]
    split_ifs <;> simp [peelSCCs_mapAdj e rev k (visit rev k r ⟨vis, []⟩).visited rs]

private theorem sccs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    sccs (mapAdj e g) (vs.map e) = (sccs g vs).map (List.map e) := by
  simp only [sccs, List.length_map, transposeAdj_mapAdj, topologicalSort_mapAdj]
  simpa using peelSCCs_mapAdj e (transposeAdj g vs) vs.length ∅ (topologicalSort g vs)

private theorem indexComponentsAux_map {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    ∀ (idx : ℕ) (cs : List (List α)) (f : α → ℕ) (x : α),
      indexComponentsAux idx (cs.map (List.map e)) (f ∘ e.symm) (e x) =
        indexComponentsAux idx cs f x
  | _, [], f, x => by simp [indexComponentsAux]
  | idx, c :: cs, f, x => by
    have hfold : ((c.map e).foldl (fun g w => Function.update g w idx) (f ∘ e.symm)) =
        (c.foldl (fun g v => Function.update g v idx) f) ∘ e.symm := by
      induction c generalizing f with
      | nil => rfl
      | cons v c ih =>
        simp only [List.map_cons, List.foldl_cons]
        have hstep : Function.update (f ∘ e.symm) (e v) idx =
            Function.update f v idx ∘ e.symm := by
          funext w
          by_cases hw : w = e v
          · subst hw; simp
          · have hsym : e.symm w ≠ v := fun h => hw (by rw [← h, e.apply_symm_apply])
            simp [Function.update_of_ne hw, Function.update_of_ne hsym]
        rw [hstep]
        exact ih _
    simp only [List.map_cons, indexComponentsAux, hfold]
    exact indexComponentsAux_map e (idx + 1) cs _ x

private theorem indexComponents_sccs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (g : α → List α) (vs : List α) (x : α) :
    indexComponents (sccs (mapAdj e g) (vs.map e)) (e x) = indexComponents (sccs g vs) x := by
  rw [sccs_mapAdj]
  exact indexComponentsAux_map e 0 (sccs g vs) (fun _ => 0) x

end EquivDFS

/-- Implication graph of `G` pushed forward along `litEquiv G.n` to `Fin (2 * G.n)`. -/
@[expose] def Instance.adjFin (G : Instance) : Fin (2 * G.n) → List (Fin (2 * G.n)) :=
  mapAdj (litEquiv G.n) (implicationAdj G.φ)

theorem Instance.indexComponents_adjFin (G : Instance) (ℓ : Literal (Fin G.n)) :
    indexComponents (sccs G.adjFin (List.finRange (2 * G.n))) (litEquiv G.n ℓ) =
      indexComponents (sccs (implicationAdj G.φ) (literalList (List.finRange G.n))) ℓ := by
  rw [← map_litEquiv_literalList_finRange]
  exact indexComponents_sccs_mapAdj (litEquiv G.n) (implicationAdj G.φ)
    (literalList (List.finRange G.n)) ℓ


theorem length_le_foldl_addClauseEdges {V : Type*} [DecidableEq V] :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)) (w : Literal V),
      (adj w).length ≤ (cs.foldl addClauseEdges adj w).length
  | [], _, _ => le_rfl
  | c :: cs, adj, w => by
    have hcons : ∀ (f : Literal V → List (Literal V)) (u v : Literal V),
        (f w).length ≤ (Function.update f u (v :: f u) w).length := fun f u v => by
      by_cases h : w = u <;> simp [h]
    have h1 : (adj w).length ≤ (addClauseEdges adj c w).length := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · exact le_rfl
      · exact hcons adj a.negate a
      · exact (hcons adj a.negate b).trans (hcons _ b.negate a)
      · exact le_rfl
    exact h1.trans (length_le_foldl_addClauseEdges cs (addClauseEdges adj c) w)

theorem csrOffset_adjFin_le (G : Instance) :
    csrOffset G.adjFin (2 * G.n) ≤ 2 * G.φ.length := by
  rw [csrOffset_eq_outDegreeSum, outDegreeSum, ← Fin.sum_univ_def]
  have heq : (∑ u : Fin (2 * G.n), (G.adjFin u).length) =
      ∑ ℓ : Literal (Fin G.n), (implicationAdj G.φ ℓ).length := by
    refine Fintype.sum_equiv (litEquiv G.n).symm _ _ fun u => ?_
    simp [Instance.adjFin, mapAdj]
  rw [heq]
  exact sum_length_implicationAdj_le G.φ

theorem mapAdj_addClauseEdges_one {n : ℕ} (g : Literal (Fin n) → List (Literal (Fin n)))
    (a : Literal (Fin n)) :
    mapAdj (litEquiv n) (addClauseEdges g [a]) =
      Function.update (mapAdj (litEquiv n) g) (litEquiv n a.negate)
        (litEquiv n a :: mapAdj (litEquiv n) g (litEquiv n a.negate)) :=
  (mapAdj_update_cons (litEquiv n) g a.negate a).symm

theorem mapAdj_addClauseEdges_two {n : ℕ} (g : Literal (Fin n) → List (Literal (Fin n)))
    (a b : Literal (Fin n)) :
    mapAdj (litEquiv n) (addClauseEdges g [a, b]) =
      let p₁ := Function.update (mapAdj (litEquiv n) g) (litEquiv n a.negate)
        (litEquiv n b :: mapAdj (litEquiv n) g (litEquiv n a.negate))
      Function.update p₁ (litEquiv n b.negate) (litEquiv n a :: p₁ (litEquiv n b.negate)) := by
  dsimp only [addClauseEdges]
  rw [← mapAdj_update_cons, ← mapAdj_update_cons]


end Cslib.Algorithms.WordRAM.TwoSAT
