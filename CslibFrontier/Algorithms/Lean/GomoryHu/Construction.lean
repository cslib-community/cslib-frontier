/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield
public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp

/-!
# Gomory–Hu trees with `n - 1` maximum flow computations

An executable construction of a Gomory–Hu tree of a weighted multigraph `W : Fin n → Fin n → ℕ`,
following Gusfield's contraction-free algorithm ([Gusfield1990]): one Edmonds–Karp maximum flow
computation ([EdmondsKarp1972]) per non-root vertex, so `n - 1` in total, all on the original
graph, plus a re-hanging scan of a parent array and an update of an edge-weight array per vertex.
Correctness is transferred from the abstract algorithm
`Cslib.Algorithms.Lean.GomoryHu.gusfieldWithWeights` of
`CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield`, with the Edmonds–Karp minimum cut and maximum
flow value as the oracle.

This module states no running time. The Word-RAM program of
`CslibFrontier.Algorithms.WordRAM.GomoryHu` runs Gusfield's algorithm in `O(n ^ 6)` instructions
on an `n × n` capacity matrix.

## Main definitions

* `Cslib.Algorithms.Lean.GomoryHu.Output`: parent array `parent` and edge-weight array `weight`
  returned by Gusfield's algorithm.
* `Cslib.Algorithms.Lean.GomoryHu.ekCut`, `Cslib.Algorithms.Lean.GomoryHu.ekValue`: the minimum
  cut and maximum flow value returned by the Edmonds–Karp solver.
* `Cslib.Algorithms.Lean.GomoryHu.rehang`, `Cslib.Algorithms.Lean.GomoryHu.gomoryHuStep`,
  `Cslib.Algorithms.Lean.GomoryHu.gomoryHuLoop`: one re-hanging scan, one step and the loop of
  Gusfield's algorithm on vectors.
* `Cslib.Algorithms.Lean.GomoryHu.gomoryHu`: Gusfield's algorithm over `Fin n`, returning the parent
  array and edge weights of the tree.

## Main results

* `Cslib.Algorithms.Lean.GomoryHu.isGomoryHuTree_gomoryHu`: the parent graph of the output is a
  Gomory–Hu tree of `cutWeight W` (cut-equivalent: the side of each tree edge `uv` containing `u`
  is a minimum `u`–`v` cut of `W`).
* `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHu_weight_eq_minCutBetween`: for every vertex
  `u : Fin n`, the recorded weight `vget (gomoryHu W adj r).weight u` equals
  `minCutBetween W u (vget (gomoryHu W adj r).parent u)` (`0` at the root `r`,
  `vget_gomoryHu_weight_root`).
* `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHu`,
  `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHu_parent`,
  `Cslib.Algorithms.Lean.GomoryHu.vget_gomoryHu_weight`: the output agrees with the abstract
  `gusfieldParent` and `gusfieldWithWeights` run with `ekCut` and `ekValue`.

## Limitations

The weights of `W` are natural numbers, and only Edmonds–Karp is instantiated as the maximum flow
oracle.

## References

* [EdmondsKarp1972]
* [GomoryHu1961]
* [Gusfield1990]
-/

public section

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.MaxFlow Cslib.WeightedCut
open SimpleGraph (parentGraph)

variable {n : ℕ}

/-- Output of Gusfield's Gomory–Hu tree construction on `Fin n`: the parent array `parent` rooted
at `r` and the edge-weight array `weight` storing `λ(u, parent[u])` for every non-root `u` (`0` at
the root `r`). -/
structure Output (n : ℕ) where
  /-- Parent array of the tree (`vget parent r = r`). -/
  parent : Vector (Fin n) n
  /-- Edge weight `λ(u, vget parent u)` for every non-root vertex `u` (`0` at `r`). -/
  weight : Vector ℕ n

instance instDecidableEqOutput {n : ℕ} : DecidableEq (Output n) :=
  fun a b => decidable_of_iff (a.parent = b.parent ∧ a.weight = b.weight)
    (by cases a; cases b; simp)

/-- Re-hang below `s` every vertex `z ∈ zs` whose parent in `p` is `t` and which lies in `X`,
writing into `acc`. -/
@[expose] def rehang (p : Vector (Fin n) n) (s t : Fin n) (X : Finset (Fin n)) :
    List (Fin n) → Vector (Fin n) n → Vector (Fin n) n
  | [], acc => acc
  | z :: zs, acc => rehang p s t X zs (if vget p z = t ∧ z ∈ X then vset acc z s else acc)

theorem vget_rehang (p : Vector (Fin n) n) (s t : Fin n) (X : Finset (Fin n)) :
    ∀ (zs : List (Fin n)) (acc : Vector (Fin n) n) (z : Fin n),
      vget (rehang p s t X zs acc) z =
        if z ∈ zs ∧ vget p z = t ∧ z ∈ X then s else vget acc z
  | [], acc, z => by simp [rehang]
  | x :: zs, acc, z => by
    simp only [rehang, vget_rehang p s t X zs, List.mem_cons]
    by_cases hzx : z = x
    · subst hzx
      split_ifs <;> simp_all
    · split_ifs <;> simp_all [vget_vset_ne _ _ (Ne.symm hzx)]

/-- The minimum cut returned by the Edmonds–Karp solver on the network with capacities `W`,
source `s` and sink `t`. -/
@[expose] def ekCut (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (s t : Fin n) :
    Finset (Fin n) :=
  (edmondsKarp (Network.mk W s t) adj).cut

/-- The maximum flow value returned by the Edmonds–Karp solver on the network with capacities `W`,
source `s` and sink `t`. -/
@[expose] def ekValue (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (s t : Fin n) : ℕ :=
  (edmondsKarp (Network.mk W s t) adj).flow.value.toNat

/-- The Edmonds–Karp cut is a minimum `s`–`t` cut of the cut function of `W`, for adjacency lists
covering the edges of `W`. -/
theorem isMinCutBetween_ekCut {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) {s t : Fin n} (hst : s ≠ t) :
    IsMinCutBetween (cutWeight W) s t (ekCut W adj s t) := by
  obtain ⟨-, hmin, -⟩ := edmondsKarp_correct (N := Network.mk W s t) (adj := adj) hadj hst
  exact hmin.isMinCutBetween

/-- The Edmonds–Karp maximum flow value equals the weight of `ekCut W adj s t`, for adjacency lists
covering the edges of `W`. -/
theorem ekValue_eq_cutWeight {W : Fin n → Fin n → ℕ} {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u) {s t : Fin n} (hst : s ≠ t) :
    ekValue W adj s t = cutWeight W (ekCut W adj s t) := by
  obtain ⟨-, -, hval, -⟩ := edmondsKarp_correct (N := Network.mk W s t) (adj := adj) hadj hst
  unfold ekValue ekCut
  rw [hval]
  rfl

/-- One step of Gusfield's algorithm on the parent array `p` and weight array `fl` for vertex `s`:
one Edmonds–Karp computation between `s` and its parent `t`, a scan re-hanging the vertices on the
`s`-side below `s`, the swap of `s` and `t` when the parent of `t` is on the `s`-side, and the
weight update from the maximum flow value (`fl[s] := val`, or on a swap `fl[s] := fl[t]` and
`fl[t] := val`). -/
@[expose] def gomoryHuStep (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) : Output n :=
  let t := vget p s
  let X := ekCut W adj s t
  let q := rehang p s t X (List.finRange n) p
  let val := ekValue W adj s t
  if vget p t ∈ X then
    { parent := vset (vset q t s) s (vget p t), weight := vset (vset fl t val) s (vget fl t) }
  else
    { parent := vset (vset q t (vget p t)) s t, weight := vset fl s val }

theorem vget_gomoryHuStep_parent (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) (z : Fin n) :
    vget (gomoryHuStep W adj p fl s).parent z =
      gusfieldStep (vget p) s (ekCut W adj s (vget p s)) z := by
  simp only [gomoryHuStep, gusfieldStep]
  generalize ekCut W adj s (vget p s) = X
  have hq : ∀ z, vget (rehang p s (vget p s) X (List.finRange n) p) z =
      if vget p z = vget p s ∧ z ∈ X then s else vget p z := fun z => by
    simp only [vget_rehang, List.mem_finRange, true_and]
  generalize rehang p s (vget p s) X (List.finRange n) p = q at hq ⊢
  by_cases hzs : z = s
  · subst hzs
    by_cases hX : vget p (vget p z) ∈ X <;> simp only [hX, ↓reduceIte, vget_vset_self]
  by_cases hzt : z = vget p s
  · subst hzt
    by_cases hX : vget p (vget p s) ∈ X <;>
      simp only [hX, hzs, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs), vget_vset_self]
  by_cases hX : vget p (vget p s) ∈ X <;>
    simp only [hX, hzs, hzt, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs),
      vget_vset_ne _ _ (Ne.symm hzt), hq]

/-- The weight array computed by `gomoryHuStep` agrees pointwise with `gusfieldStepWeight`. -/
theorem vget_gomoryHuStep_weight (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (p : Vector (Fin n) n) (fl : Vector ℕ n) (s : Fin n) (z : Fin n) :
    vget (gomoryHuStep W adj p fl s).weight z =
      gusfieldStepWeight (vget p) (vget fl) s (ekCut W adj s (vget p s))
        (ekValue W adj s (vget p s)) z := by
  simp only [gomoryHuStep, gusfieldStepWeight]
  generalize ekCut W adj s (vget p s) = X
  generalize ekValue W adj s (vget p s) = val
  by_cases hX : vget p (vget p s) ∈ X
  · simp only [hX, ↓reduceIte]
    by_cases hzs : z = s
    · subst hzs
      simp only [vget_vset_self, ↓reduceIte]
    · simp only [hzs, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs)]
      by_cases hzt : z = vget p s
      · subst hzt
        simp only [vget_vset_self, ↓reduceIte]
      · simp only [hzt, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzt)]
  · simp only [hX, ↓reduceIte]
    by_cases hzs : z = s
    · subst hzs
      simp only [vget_vset_self, ↓reduceIte]
    · simp only [hzs, ↓reduceIte, vget_vset_ne _ _ (Ne.symm hzs)]

/-- Gusfield's loop over the vertices `l`, skipping the root `r` and tracking both parent and
edge-weight arrays. -/
@[expose] def gomoryHuLoop (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    List (Fin n) → Vector (Fin n) n → Vector ℕ n → Output n
  | [], p, fl => { parent := p, weight := fl }
  | s :: l, p, fl =>
    if s = r then gomoryHuLoop W adj r l p fl
    else
      let step := gomoryHuStep W adj p fl s
      gomoryHuLoop W adj r l step.parent step.weight

theorem vget_gomoryHuLoop (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    ∀ (l : List (Fin n)) (p : Vector (Fin n) n) (fl : Vector ℕ n),
      vget (gomoryHuLoop W adj r l p fl).parent =
          (gusfieldWeightLoop (ekCut W adj) (ekValue W adj) r l (vget p) (vget fl)).1 ∧
        vget (gomoryHuLoop W adj r l p fl).weight =
          (gusfieldWeightLoop (ekCut W adj) (ekValue W adj) r l (vget p) (vget fl)).2
  | [], p, fl => ⟨rfl, rfl⟩
  | s :: l, p, fl => by
    by_cases hsr : s = r
    · simp only [gomoryHuLoop, hsr, ↓reduceIte, gusfieldWeightLoop]
      exact vget_gomoryHuLoop W adj r l p fl
    · simp only [gomoryHuLoop, hsr, ↓reduceIte, gusfieldWeightLoop]
      obtain ⟨hpar, hwt⟩ := vget_gomoryHuLoop W adj r l (gomoryHuStep W adj p fl s).parent
        (gomoryHuStep W adj p fl s).weight
      have hp : vget (gomoryHuStep W adj p fl s).parent =
          gusfieldStep (vget p) s (ekCut W adj s (vget p s)) :=
        funext (vget_gomoryHuStep_parent W adj p fl s)
      have hw : vget (gomoryHuStep W adj p fl s).weight =
          gusfieldStepWeight (vget p) (vget fl) s (ekCut W adj s (vget p s))
            (ekValue W adj s (vget p s)) :=
        funext (vget_gomoryHuStep_weight W adj p fl s)
      rw [hp, hw] at hpar hwt
      exact ⟨hpar, hwt⟩

/-- **Gusfield's Gomory–Hu tree algorithm** ([Gusfield1990]) over `Fin n`: start from the star
centred at the root `r` with `0` initial weights, and process the other vertices in order with one
Edmonds–Karp computation each. Returns both the parent array `parent` and the tree edge weights
`weight`. -/
@[expose] def gomoryHu (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    Output n :=
  gomoryHuLoop W adj r (List.finRange n) (Vector.replicate n r) (Vector.replicate n 0)

private theorem vget_gomoryHu_spec (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n))
    (r : Fin n) :
    vget (gomoryHu W adj r).parent =
        (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).1 ∧
      vget (gomoryHu W adj r).weight =
        (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).2 := by
  obtain ⟨hpar, hwt⟩ :=
    vget_gomoryHuLoop W adj r (List.finRange n) (Vector.replicate n r) (Vector.replicate n 0)
  have hp : vget (Vector.replicate n r) = fun _ => r := funext (vget_replicate r)
  have hw : vget (Vector.replicate n 0) = fun _ => 0 := funext (vget_replicate 0)
  rw [hp, hw] at hpar hwt
  exact ⟨hpar, hwt⟩

/-- The parent array returned by `gomoryHu` agrees pointwise with the first component of
`gusfieldWithWeights`. -/
theorem vget_gomoryHu_parent (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHu W adj r).parent =
      (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).1 :=
  (vget_gomoryHu_spec W adj r).1

/-- The parent array returned by `gomoryHu` agrees pointwise with `gusfieldParent`. -/
theorem vget_gomoryHu (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHu W adj r).parent = gusfieldParent (ekCut W adj) r (List.finRange n) := by
  rw [vget_gomoryHu_parent, fst_gusfieldWithWeights]

/-- The weight array returned by `gomoryHu` agrees pointwise with the second component of
`gusfieldWithWeights`. -/
theorem vget_gomoryHu_weight (W : Fin n → Fin n → ℕ) (adj : Fin n → List (Fin n)) (r : Fin n) :
    vget (gomoryHu W adj r).weight =
      (gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)).2 :=
  (vget_gomoryHu_spec W adj r).2

private theorem gomoryHu_pure_spec {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    let res := gusfieldWithWeights (ekCut W adj) (ekValue W adj) r 0 (List.finRange n)
    IsGomoryHuTree (cutWeight W) (parentGraph res.1) ∧ res.1 r = r ∧ res.2 r = 0 ∧
      ∀ u, u ≠ r →
        IsMinCutBetween (cutWeight W) u (res.1 u)
            (SimpleGraph.edgeSide (parentGraph res.1) u (res.1 u)) ∧
          res.2 u = cutWeight W (SimpleGraph.edgeSide (parentGraph res.1) u (res.1 u)) :=
  gusfieldWithWeights_spec (cutWeight_compl' hW) (isSubmodular_cutWeight W)
    (fun _ _ hst => isMinCutBetween_ekCut hadj hst)
    (fun _ _ hst => ekValue_eq_cutWeight hadj hst) r 0 (List.nodup_finRange n)
    fun x _ => List.mem_finRange x

/-- **Correctness of Gusfield's algorithm with Edmonds–Karp** ([Gusfield1990]): for a weighted
multigraph `W` on `Fin n` and adjacency lists `adj` covering its edges, the parent array computed
by `gomoryHu` is a Gomory–Hu tree of `W`: for every tree edge `uv`, the side of `T - uv`
containing `u` is a minimum `u`–`v` cut of `W`. -/
theorem isGomoryHuTree_gomoryHu {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    IsGomoryHuTree (cutWeight W) (parentGraph (vget (gomoryHu W adj r).parent)) := by
  rw [vget_gomoryHu_parent]
  exact (gomoryHu_pure_spec hW hadj r).1

/-- The recorded root weight is `0`. -/
theorem vget_gomoryHu_weight_root {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r : Fin n) :
    vget (gomoryHu W adj r).weight r = 0 := by
  rw [vget_gomoryHu_weight]
  exact (gomoryHu_pure_spec hW hadj r).2.2.1

/-- **Correctness of the edge weights returned by `gomoryHu`** ([Gusfield1990]): for every vertex
`u : Fin n`, the weight `vget (gomoryHu W adj r).weight u` equals the minimum cut weight
`minCutBetween W u (vget (gomoryHu W adj r).parent u)` between `u` and its parent (`0` at the
root `r`). -/
theorem vget_gomoryHu_weight_eq_minCutBetween {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W)
    {adj : Fin n → List (Fin n)} (hadj : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adj u)
    (r u : Fin n) :
    vget (gomoryHu W adj r).weight u = minCutBetween W u (vget (gomoryHu W adj r).parent u) := by
  have hspec := gomoryHu_pure_spec hW hadj r
  rw [vget_gomoryHu_weight, vget_gomoryHu_parent]
  by_cases hur : u = r
  · subst hur
    rw [hspec.2.1, hspec.2.2.1, minCutBetween_self]
  · obtain ⟨hcut, hw⟩ := hspec.2.2.2 u hur
    exact hw.trans ((isMinCutBetween_cutWeight_iff W).mp hcut).2.2

end Cslib.Algorithms.Lean.GomoryHu
