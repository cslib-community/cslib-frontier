/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Dilworth
public import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp

/-!
# Minimum chain cover by Hopcroft–Karp

`minChainCover e` computes a minimum chain cover and a maximum antichain of a finite poset `α`,
given as an enumeration `e : Fin n ≃ α` with decidable `<`. It runs Fulkerson's reduction
(`CslibFrontier.Algorithms.Lean.MaxFlow.Dilworth`) on the output of Hopcroft–Karp:

1. `hopcroftKarpDense (enumLtGraph e)` returns a maximum matching `M` and a minimum König cover
   `C` of the bipartite graph joining index `i` to index `j` when `e i < e j`.
2. Starting from the labels `i ↦ i`, `chainLabels` scans every pair of indices and, for each pair
   `(i, j) ∈ M`, relabels `j`'s chain with `i`'s label (`mergeChains`). The resulting label
   fibres are chains, and there are `n - |M|` labels.
3. The indices missed by `C` on both sides form an antichain of at least `n - |C| = n - |M|`
   elements (`uncoveredStep`).

`minChainCover_correct` proves that the label fibres are chains, the returned index set is an
antichain, and the number of labels equals the size of the antichain, `n - |M|`. With weak
duality this certifies both as optimal (`card_le_card_antichain_of_isAntichain`,
`card_antichain_le_of_isChain_fibre`), which is the algorithmic content of Dilworth's theorem.

Machine-checked `O(n^{5/2})` word-RAM running-time bounds for minimum chain cover and maximum
antichain live in `CslibFrontier.Algorithms.WordRAM.HopcroftKarp`.

## Main definitions

* `enumLtGraph`: Fulkerson's graph `ltGraph` read through an enumeration.
* `ChainCoverOutput`, `ChainCoverOutput.label`, `ChainCoverOutput.numChains`: chain labels,
  antichain, matching, and chain count.
* `mergeChains`, `chainLabels`, `uncoveredStep`: the steps of the algorithm.
* `minChainCover`: the pure algorithm.

## Main results

* `minChainCover_correct`: chain fibres, an antichain, and equal sizes `n - |M|`.
* `card_le_card_antichain_of_isAntichain`, `card_antichain_le_of_isChain_fibre`: the output is a
  maximum antichain and the labels form a minimum chain cover.
* `chainLabels_eq_foldl_rowMate`: row-mate fold characterization of `chainLabels` for matchings
  (used by the word-RAM realization).

## References

* [D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered
  sets*][Fulkerson1956]
* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 7.3
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.Algorithms.Lean

variable {α : Type*} {n : ℕ}

/-- Fulkerson's graph `ltGraph` read through an enumeration `e : Fin n ≃ α`: index `i` is joined
to index `j` when `e i < e j`. -/
@[expose] def enumLtGraph [LT α] [DecidableLT α] (e : Fin n ≃ α) : Fin n × Fin n → Bool :=
  fun p => ltGraph (e p.1, e p.2)

/-- Output of `minChainCover`. -/
structure ChainCoverOutput (n : ℕ) where
  /-- Chain label of each index; indices with equal labels lie on one chain. -/
  labels : Vector (Fin n) n
  /-- A maximum antichain, as a set of indices. -/
  antichain : Finset (Fin n)
  /-- The maximum matching of `enumLtGraph e` found by Hopcroft–Karp. -/
  matching : Finset (Fin n × Fin n)

/-- Merge the chain of index `j` into the chain of index `i`, for `p = (i, j)`: every label equal
to `j`'s becomes `i`'s. -/
@[expose] def mergeChains (labels : Vector (Fin n) n) (p : Fin n × Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun i =>
    if vget labels i = vget labels p.2 then vget labels p.1 else vget labels i

/-- Scan the candidate pairs `ps` and merge along those in `M`. -/
@[expose] def chainLabels (M : Finset (Fin n × Fin n)) :
    List (Fin n × Fin n) → Vector (Fin n) n → Vector (Fin n) n
  | [], labels => labels
  | p :: ps, labels =>
    let labels' := if p ∈ M then mergeChains labels p else labels
    chainLabels M ps labels'

/-- Insert index `i` into the antichain when the König cover `C` misses it on both sides. -/
@[expose] def uncoveredStep (C : VertexCover (Fin n) (Fin n)) (A : Finset (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  if i ∉ C.left ∧ i ∉ C.right then insert i A else A

/-- **Minimum chain cover** of a finite poset enumerated by `e : Fin n ≃ α`, by Fulkerson's
reduction: a maximum matching of `enumLtGraph e` from `hopcroftKarpDense`, chains obtained by
merging along its edges, and a maximum antichain read off the König cover. -/
@[expose] def minChainCover [LT α] [DecidableLT α] (e : Fin n ≃ α) : ChainCoverOutput n :=
  let hk := hopcroftKarpDense (enumLtGraph e)
  let labels := chainLabels hk.matching (List.finRange n ×ˢ List.finRange n) (Vector.ofFn id)
  let antichain := (List.finRange n).foldl (uncoveredStep hk.cover) ∅
  ⟨labels, antichain, hk.matching⟩

/-- The chain label of `x : α` in an output `out` for the enumeration `e`. -/
@[expose] def ChainCoverOutput.label (e : Fin n ≃ α) (out : ChainCoverOutput n) (x : α) : Fin n :=
  vget out.labels (e.symm x)

/-- The number of chains of an output: the number of distinct labels in the table. -/
@[expose] def ChainCoverOutput.numChains (out : ChainCoverOutput n) : ℕ :=
  (Finset.univ.image (vget out.labels)).card

/-! ### Correctness -/

section Proofs

private theorem mem_foldl_uncoveredStep (C : VertexCover (Fin n) (Fin n)) (l : List (Fin n))
    (A : Finset (Fin n)) (i : Fin n) :
    i ∈ l.foldl (uncoveredStep C) A ↔ i ∈ A ∨ (i ∈ l ∧ i ∉ C.left ∧ i ∉ C.right) := by
  induction l generalizing A with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    unfold uncoveredStep
    split_ifs with h <;> grind

theorem foldl_uncoveredStep (C : VertexCover (Fin n) (Fin n)) :
    (List.finRange n).foldl (uncoveredStep C) ∅ = C.uncovered := by
  ext i
  rw [mem_foldl_uncoveredStep, mem_uncovered]
  simp

private theorem chainLabels_append (M : Finset (Fin n × Fin n))
    (ps₁ ps₂ : List (Fin n × Fin n)) (labels : Vector (Fin n) n) :
    chainLabels M (ps₁ ++ ps₂) labels = chainLabels M ps₂ (chainLabels M ps₁ labels) := by
  induction ps₁ generalizing labels with
  | nil => rfl
  | cons p ps₁ ih =>
    simp only [List.cons_append, chainLabels]
    exact ih _

/-- When `rm i` is the unique right mate of `i` (`rm i = some j ↔ (i, j) ∈ M`), scanning
`List.finRange n ×ˢ List.finRange n` in `chainLabels` equals a single `O(n)`-outer-step fold over
`i ∈ List.finRange n`. -/
theorem chainLabels_eq_foldl_rowMate {M : Finset (Fin n × Fin n)}
    (rm : Fin n → Option (Fin n)) (hrm : ∀ i j, rm i = some j ↔ (i, j) ∈ M)
    (labels₀ : Vector (Fin n) n) :
    chainLabels M (List.finRange n ×ˢ List.finRange n) labels₀ =
      (List.finRange n).foldl
        (fun lab i => match rm i with | some j => mergeChains lab (i, j) | none => lab)
        labels₀ := by
  have hrow : ∀ (i : Fin n) (js : List (Fin n)) (hnd : js.Nodup) (lab : Vector (Fin n) n),
      chainLabels M (js.map fun j => (i, j)) lab =
        match rm i with
        | some j => if j ∈ js then mergeChains lab (i, j) else lab
        | none => lab := by
    intro i js hnd lab
    induction js generalizing lab with
    | nil =>
      cases rm i <;> rfl
    | cons j₀ js ih =>
      obtain ⟨hj₀, hnd'⟩ := List.nodup_cons.mp hnd
      simp only [List.map_cons, chainLabels]
      cases hrmi : rm i with
      | none =>
        have hnot : (i, j₀) ∉ M := fun hm => by simpa [hrmi] using (hrm i j₀).mpr hm
        rw [ite_eq_right hnot]
        simpa [hrmi] using ih hnd' lab
      | some j₁ =>
        by_cases heq : j₀ = j₁
        · subst heq
          have hin : (i, j₀) ∈ M := (hrm i j₀).mp hrmi
          rw [ite_eq_left hin, ih hnd']
          simp [hrmi, hj₀]
        · have hnot : (i, j₀) ∉ M := fun hm =>
            heq (Option.some.inj (((hrm i j₀).mpr hm).symm.trans hrmi))
          rw [ite_eq_right hnot, ih hnd']
          simp [hrmi, Ne.symm heq]
  have houter : ∀ (is : List (Fin n)) (lab : Vector (Fin n) n),
      chainLabels M (is.flatMap fun i => (List.finRange n).map fun j => (i, j)) lab =
        is.foldl (fun lab i => match rm i with | some j => mergeChains lab (i, j) | none => lab)
          lab := by
    intro is
    induction is with
    | nil => intro _; rfl
    | cons i is ih =>
      intro lab
      rw [List.flatMap_cons, chainLabels_append, List.foldl_cons,
        hrow i (List.finRange n) (List.nodup_finRange n) lab, ih]
      cases rm i <;> simp [List.mem_finRange]
  exact houter (List.finRange n) labels₀

/-- One merge step on the label table is `mergeLabel` on the label function. -/
private theorem vget_mergeChains (e : Fin n ≃ α) (labels : Vector (Fin n) n)
    (p : Fin n × Fin n) :
    (fun x => vget (mergeChains labels p) (e.symm x)) =
      mergeLabel (fun x => vget labels (e.symm x)) (e p.1, e p.2) := by
  funext x
  simp only [mergeChains, mergeLabel, vget, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  rfl

private theorem chainLabels_spec (e : Fin n ≃ α) (M : Finset (Fin n × Fin n))
    (ps : List (Fin n × Fin n)) (labels : Vector (Fin n) n) :
    (fun x => vget (chainLabels M ps labels) (e.symm x)) =
      ((ps.filter (· ∈ M)).map (Prod.map e e)).foldl (mergeLabel ·)
        (fun x => vget labels (e.symm x)) := by
  induction ps generalizing labels with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : p ∈ M
    · rw [List.filter_cons_of_pos (by simpa using hp), List.map_cons, List.foldl_cons]
      simp only [chainLabels, hp, ite_true, ih]
      rw [vget_mergeChains]
      rfl
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      simp only [chainLabels, hp, ite_false, ih]

/-- Scanning all pairs of indices visits each element of `M` exactly once. -/
private theorem nodup_filter_pairs (M : Finset (Fin n × Fin n)) :
    ((List.finRange n ×ˢ List.finRange n).filter (· ∈ M)).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

private theorem mem_filter_pairs {M : Finset (Fin n × Fin n)} {p : Fin n × Fin n} :
    p ∈ (List.finRange n ×ˢ List.finRange n).filter (· ∈ M) ↔ p ∈ M := by
  obtain ⟨i, j⟩ := p
  simp

private theorem length_filter_pairs (M : Finset (Fin n × Fin n)) :
    ((List.finRange n ×ˢ List.finRange n).filter (· ∈ M)).length = M.card := by
  rw [← List.toFinset_card_of_nodup (nodup_filter_pairs M)]
  congr 1
  ext p
  rw [List.mem_toFinset, mem_filter_pairs]

private theorem minChainCover_eq [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    minChainCover e =
      ⟨chainLabels (hopcroftKarpDense (enumLtGraph e)).matching
          (List.finRange n ×ˢ List.finRange n) (Vector.ofFn id),
        (hopcroftKarpDense (enumLtGraph e)).cover.uncovered,
        (hopcroftKarpDense (enumLtGraph e)).matching⟩ := by
  simp [minChainCover, foldl_uncoveredStep]

variable [PartialOrder α] [DecidableLT α]

/-- **Correctness of `minChainCover`.** The label fibres are chains, the returned indices form an
antichain, and the number of labels equals the size of the antichain, namely `n - |M|` for the
maximum matching `M` found by Hopcroft–Karp. By weak duality the antichain is maximum and the
chain cover minimum (`card_le_card_antichain_of_isAntichain`,
`card_antichain_le_of_isChain_fibre`). -/
theorem minChainCover_correct (e : Fin n ≃ α) :
    (∀ c, IsChain (· ≤ ·) ((minChainCover e).label e ⁻¹' {c})) ∧
      IsAntichain (· ≤ ·) (e '' (minChainCover e).antichain) ∧
      (minChainCover e).numChains = (minChainCover e).antichain.card ∧
      (minChainCover e).antichain.card + (minChainCover e).matching.card = n := by
  classical
  let _ : Fintype α := Fintype.ofEquiv _ e
  obtain ⟨hmax, hmin, hcard, -⟩ := hopcroftKarpDense_correct (enumLtGraph e)
  rw [minChainCover_eq]
  generalize hopcroftKarpDense (enumLtGraph e) = hk at hmax hmin hcard
  set M := hk.matching
  set C := hk.cover
  set ps := (List.finRange n ×ˢ List.finRange n).filter (· ∈ M)
  set L := ps.map (Prod.map e e)
  have hlabel : ChainCoverOutput.label e ⟨chainLabels M (List.finRange n ×ˢ List.finRange n)
      (Vector.ofFn id), C.uncovered, M⟩ =
      L.foldl (mergeLabel ·) (fun x => vget (Vector.ofFn id : Vector (Fin n) n) (e.symm x)) :=
    chainLabels_spec e M _ _
  have hinj : Function.Injective fun x => vget (Vector.ofFn id : Vector (Fin n) n) (e.symm x) :=
    fun x y h => e.symm.injective (by simpa [vget] using h)
  have hemb : Function.Injective (Prod.map e e) := e.injective.prodMap e.injective
  have hL : L.Nodup := (nodup_filter_pairs M).map hemb
  have hmemL : ∀ a b : α, (a, b) ∈ L ↔ (e.symm a, e.symm b) ∈ M := by
    intro a b
    simp only [L, ps, List.mem_map, mem_filter_pairs, Prod.exists, Prod.map, Prod.mk.injEq]
    exact ⟨fun ⟨i, j, h, hi, hj⟩ => by simpa [← hi, ← hj] using h,
      fun h => ⟨_, _, h, by simp, by simp⟩⟩
  have hmatch : IsMatching (ltGraph (α := α)) L.toFinset := by
    refine ⟨fun ⟨a, b⟩ h => ?_, fun a b₁ b₂ h₁ h₂ => ?_, fun a₁ a₂ b h₁ h₂ => ?_⟩
    · rw [List.mem_toFinset, hmemL] at h
      simpa [enumLtGraph] using hmax.1.1 _ h
    · rw [List.mem_toFinset, hmemL] at h₁ h₂
      exact e.symm.injective (hmax.1.2.1 _ _ _ h₁ h₂)
    · rw [List.mem_toFinset, hmemL] at h₁ h₂
      exact e.symm.injective (hmax.1.2.2 _ _ _ h₁ h₂)
  obtain ⟨hchain, hnum⟩ := foldl_mergeLabel_spec hinj hL hmatch
  rw [← hlabel] at hchain hnum
  set lab := ChainCoverOutput.label e ⟨chainLabels M (List.finRange n ×ˢ List.finRange n)
      (Vector.ofFn id), C.uncovered, M⟩
  have hcardα : Fintype.card α = n := (Fintype.card_congr e.symm).trans (Fintype.card_fin n)
  have hLlen : L.length = M.card := by rw [List.length_map, length_filter_pairs]
  have hrange : (Finset.univ.image lab) = Finset.univ.image (vget (chainLabels M
      (List.finRange n ×ˢ List.finRange n) (Vector.ofFn id))) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, hx⟩,
      fun ⟨i, hi⟩ => ⟨e i, by simp [← hi, lab, ChainCoverOutput.label]⟩⟩
  have hanti : IsAntichain (· ≤ ·) (e '' C.uncovered) := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hij hle
    rw [Finset.mem_coe, mem_uncovered] at hi hj
    exact (hmin.1 i j (by simpa [enumLtGraph] using lt_of_le_of_ne hle hij)).elim hi.1 hj.2
  have hle : n - M.card ≤ C.uncovered.card := by
    have := card_sub_size_le_card_uncovered C
    rwa [Fintype.card_fin, ← hcard] at this
  have hge : C.uncovered.card ≤ (Finset.univ.image lab).card := by
    have hinjOn : Set.InjOn lab (e '' C.uncovered) :=
      hanti.injOn_of_isChain_fibre hchain
    calc C.uncovered.card = (C.uncovered.map e.toEmbedding).card := (Finset.card_map _).symm
      _ ≤ (Finset.univ.image lab).card :=
        Finset.card_le_card_of_injOn lab (fun x _ => Finset.mem_coe.mpr
          (Finset.mem_image_of_mem lab (Finset.mem_univ x)))
          (by rwa [Finset.coe_map, Equiv.coe_toEmbedding])
  rw [hrange] at hnum hge
  refine ⟨hchain, hanti, ?_, ?_⟩ <;> simp only [ChainCoverOutput.numChains] <;> omega

variable (e : Fin n ≃ α)

/-- The antichain returned by `minChainCover` is maximum. -/
theorem card_le_card_antichain_of_isAntichain {A : Finset α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) : A.card ≤ (minChainCover e).antichain.card := by
  obtain ⟨hchain, -, hnum, -⟩ := minChainCover_correct e
  rw [← hnum]
  calc A.card = (A.image ((minChainCover e).label e)).card :=
        (Finset.card_image_of_injOn (hA.injOn_of_isChain_fibre hchain)).symm
    _ ≤ (minChainCover e).numChains := Finset.card_le_card fun c hc => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- The chain cover returned by `minChainCover` is minimum: every covering of `α` by `k` chains
has `k` at least the number of its labels. -/
theorem card_antichain_le_of_isChain_fibre {k : ℕ} {f : α → Fin k}
    (hf : ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) : (minChainCover e).antichain.card ≤ k := by
  obtain ⟨-, hanti, -, -⟩ := minChainCover_correct e
  have h := IsAntichain.card_le_of_isChain_fibre (t := (minChainCover e).antichain.map
    e.toEmbedding) (by rwa [Finset.coe_map, Equiv.coe_toEmbedding]) hf
  rwa [Finset.card_map, Fintype.card_fin] at h

end Proofs

end Cslib.Algorithms.Lean.MaxFlow
