/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Order.Fin.Basic

/-!
# Undirected Compressed Sparse Row (CSR) Graph Construction on the Word RAM

Constructs an undirected CSR adjacency representation (`UndirCSR`, `HoldsUndirCSR`) from a stride-4
`IndexedEdge` array in `O(m + n)` Word-RAM operations via `buildUndirCSR`, reusing
`Memory.allocBlock`, `Memory.allocBlockDirty`, `prefixSumProg`, `Memory.copy`,
`Memory.FramedTriple`, and `LoopFrame.iterate_potential_spec`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.UndirCSR`: two-word CSR offset and adjacency
  buffer handles encoded faithfully via `word_enc_structure`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.HoldsUndirCSR`: specification of an undirected CSR
  layout (`off[0] = 0`, monotone `off`, `off[n] = 2 * m`, per-vertex adjacency slice permutations).
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.buildUndirCSR`: linear-time `O(m + n)` undirected
  CSR builder on `GraphSlice`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.HoldsUndirCSR.offset_le_end`,
  `HoldsUndirCSR.congr`, `HoldsUndirCSR.mem_slice_iff`
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_buildUndirCSR`, `buildUndirCSR_spec`
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal

/-! ## `UndirCSR` Handle and Layout Predicate -/

/-- Offset and adjacency buffer base addresses for an undirected CSR representation. -/
structure UndirCSR where
  /-- Base address of the `(n + 1)`-word vertex offset array `off`. -/
  offBase : ℕ
  /-- Base address of the `(4 * m)`-word undirected half-edge array `adj`. -/
  adjBase : ℕ

/-- Faithful two-word encoding of `UndirCSR` as `[offBase, adjBase]`. -/
word_enc_structure encUndirCSR : UndirCSR where
  offBase : wordWords,
  adjBase : wordWords

instance : WordEncoding UndirCSR := ⟨2, encUndirCSR⟩

/-- Undirected CSR adjacency specification for `es : List (IndexedEdge n)` stored in
`offBase[0..n]` and half-edge pairs `(neighbor, edgeIdx)` in `adjBase[0..4 * es.length)`. -/
structure HoldsUndirCSR {n : ℕ} (offBase adjBase : ℕ) (es : List (IndexedEdge n))
    (mem : ℕ → ℕ) : Prop where
  /-- Initial offset is zero. -/
  off_zero : mem offBase = 0
  /-- Offsets are nondecreasing across vertices. -/
  off_mono : ∀ u : Fin n, mem (offBase + u.val) ≤ mem (offBase + u.val + 1)
  /-- Final offset equals twice the edge count `2 * es.length`. -/
  off_end : mem (offBase + n) = 2 * es.length
  /-- Each vertex's adjacency slice is a permutation of its incident half-edges. -/
  adj_perm : ∀ u : Fin n,
    ((List.range (mem (offBase + u.val + 1) - mem (offBase + u.val))).map (fun k =>
      let p := mem (offBase + u.val) + k
      (mem (adjBase + 2 * p), mem (adjBase + 2 * p + 1)))).Perm
      (((List.finRange es.length).filter (fun i => decide (es[i.val].u = u))).map
        (fun i => (es[i.val].v.val, i.val)) ++
       ((List.finRange es.length).filter (fun i => decide (es[i.val].v = u))).map
        (fun i => (es[i.val].u.val, i.val)))

/-- In `HoldsUndirCSR`, every offset `k ≤ n` is bounded by `2 * es.length`. -/
theorem HoldsUndirCSR.offset_le_end {n : ℕ} {offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (h : HoldsUndirCSR offBase adjBase es mem) (k : ℕ) (hk : k ≤ n) :
    mem (offBase + k) ≤ 2 * es.length := by
  have hmono : Monotone (fun i : Fin (n + 1) => mem (offBase + i.val)) :=
    Fin.monotone_iff_le_succ.mpr fun i => by
      simpa only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using h.off_mono i
  exact (hmono (show (⟨k, by omega⟩ : Fin (n + 1)) ≤ ⟨n, Nat.lt_succ_self n⟩ from hk)).trans
    h.off_end.le

/-- Framing lemma for `HoldsUndirCSR`. -/
theorem HoldsUndirCSR.congr {n : ℕ} {offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {m₁ m₂ : ℕ → ℕ}
    (hoff : ∀ a, offBase ≤ a → a < offBase + n + 1 → m₂ a = m₁ a)
    (hadj : ∀ a, adjBase ≤ a → a < adjBase + 4 * es.length → m₂ a = m₁ a)
    (h : HoldsUndirCSR offBase adjBase es m₁) : HoldsUndirCSR offBase adjBase es m₂ := by
  refine ⟨(hoff _ le_rfl (by omega)).trans h.off_zero, fun u => ?_,
    (hoff _ (by omega) (by omega)).trans h.off_end, fun u => ?_⟩
  · have hu1 := hoff (offBase + u.val) (by omega) (by omega)
    have hu2 := hoff (offBase + u.val + 1) (by omega) (by omega)
    rw [hu1, hu2]
    exact h.off_mono u
  · have hu1 := hoff (offBase + u.val) (by omega) (by omega)
    have hu2 := hoff (offBase + u.val + 1) (by omega) (by omega)
    have hhi := h.offset_le_end (u.val + 1) u.isLt
    rw [hu1, hu2]
    have hmap :
        ((List.range (m₁ (offBase + u.val + 1) - m₁ (offBase + u.val))).map (fun k =>
          let p := m₁ (offBase + u.val) + k
          (m₂ (adjBase + 2 * p), m₂ (adjBase + 2 * p + 1)))) =
        ((List.range (m₁ (offBase + u.val + 1) - m₁ (offBase + u.val))).map (fun k =>
          let p := m₁ (offBase + u.val) + k
          (m₁ (adjBase + 2 * p), m₁ (adjBase + 2 * p + 1)))) := by
      refine List.map_congr_left fun k hk => ?_
      rw [List.mem_range] at hk
      rw [← Nat.add_assoc] at hhi
      have hp_lt : m₁ (offBase + u.val) + k < 2 * es.length := by omega
      ext <;> dsimp only
      · exact hadj _ (by omega) (by omega)
      · exact hadj _ (by omega) (by omega)
    rw [hmap]
    exact h.adj_perm u

/-- Membership equivalence for vertex `u`'s CSR neighbor slice. -/
theorem HoldsUndirCSR.mem_slice_iff {n : ℕ} {offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (h : HoldsUndirCSR offBase adjBase es mem) (u : Fin n) (nb eIdx : ℕ) :
    (nb, eIdx) ∈ (List.range (mem (offBase + u.val + 1) - mem (offBase + u.val))).map (fun k =>
      let p := mem (offBase + u.val) + k
      (mem (adjBase + 2 * p), mem (adjBase + 2 * p + 1))) ↔
      ∃ i : Fin es.length, i.val = eIdx ∧
        ((es[i.val].u = u ∧ es[i.val].v.val = nb) ∨
         (es[i.val].v = u ∧ es[i.val].u.val = nb)) := by
  rw [(h.adj_perm u).mem_iff, List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨i, hi, hpair⟩ | ⟨i, hi, hpair⟩)
    · rw [List.mem_filter, decide_eq_true_eq] at hi
      exact ⟨i, congrArg Prod.snd hpair, Or.inl ⟨hi.2, congrArg Prod.fst hpair⟩⟩
    · rw [List.mem_filter, decide_eq_true_eq] at hi
      exact ⟨i, congrArg Prod.snd hpair, Or.inr ⟨hi.2, congrArg Prod.fst hpair⟩⟩
  · rintro ⟨i, rfl, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · exact Or.inl ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hu⟩,
        Prod.ext hv rfl⟩
    · exact Or.inr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hv⟩,
        Prod.ext hu rfl⟩

/-! ## Degree-Prefix Helpers and CSR Loop Steps -/

private def edgeDegPrefix {n : ℕ} (es : List (IndexedEdge n)) (k : ℕ) (u : Fin n) : ℕ :=
  (es.take k).countP (fun e => decide (e.u = u)) +
  (es.take k).countP (fun e => decide (e.v = u))

private theorem edgeDegPrefix_zero {n : ℕ} (es : List (IndexedEdge n)) (u : Fin n) :
    edgeDegPrefix es 0 u = 0 := by
  simp only [edgeDegPrefix, List.take_zero, List.countP_nil]

private theorem edgeDegPrefix_succ {n : ℕ} (es : List (IndexedEdge n)) {k : ℕ}
    (hk : k < es.length) (u : Fin n) :
    edgeDegPrefix es (k + 1) u =
      edgeDegPrefix es k u +
        (if es[k].u = u then 1 else 0) + (if es[k].v = u then 1 else 0) := by
  have htake : es.take (k + 1) = es.take k ++ [es[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  simp only [edgeDegPrefix, htake, List.countP_append, List.countP_singleton, decide_eq_true_eq]
  split_ifs <;> omega

private theorem edgeDegPrefix_mono {n : ℕ} (es : List (IndexedEdge n)) {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) (_hk₂ : k₂ ≤ es.length) (u : Fin n) :
    edgeDegPrefix es k₁ u ≤ edgeDegPrefix es k₂ u :=
  Nat.add_le_add (List.take_sublist_take_left hk).countP_le
    (List.take_sublist_take_left hk).countP_le

private theorem sum_edgeDegPrefix {n : ℕ} (es : List (IndexedEdge n)) (k : ℕ) (hk : k ≤ es.length) :
    ∑ u : Fin n, edgeDegPrefix es k u = 2 * k := by
  induction k with
  | zero => simp only [edgeDegPrefix_zero, Finset.sum_const_zero, Nat.mul_zero]
  | succ k ih =>
    have hk' : k < es.length := by omega
    have hsum : ∀ u : Fin n, edgeDegPrefix es (k + 1) u =
        edgeDegPrefix es k u + (if es[k].u = u then 1 else 0) +
          (if es[k].v = u then 1 else 0) := fun u => edgeDegPrefix_succ es hk' u
    simp_rw [hsum, Finset.sum_add_distrib]
    have hs1 : ∑ u : Fin n, (if es[k].u = u then 1 else 0) = 1 := by simp
    have hs2 : ∑ u : Fin n, (if es[k].v = u then 1 else 0) = 1 := by simp
    have ih' := ih (by omega)
    omega

private theorem edgeDegPrefix_le {n : ℕ} (es : List (IndexedEdge n)) (k : ℕ) (hk : k ≤ es.length)
    (u : Fin n) : edgeDegPrefix es k u ≤ 2 * k := by
  have h1 : edgeDegPrefix es k u ≤ ∑ v : Fin n, edgeDegPrefix es k v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  rw [sum_edgeDegPrefix es k hk] at h1
  exact h1

private structure CSREnv where
  edgeBase : ℕ
  bufBase : ℕ

private word_enc_structure encCSREnv : CSREnv where
  edgeBase : wordWords,
  bufBase : wordWords

private instance : WordEncoding CSREnv := ⟨2, encCSREnv⟩

private def csrCountStep (x : CSREnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let j := Prod.snd x
  let u ← Memory.read (env.edgeBase + 4 * j)
  let cu ← Memory.read (env.bufBase + u)
  Memory.write (env.bufBase + u) (cu + 1)
  let v ← Memory.read (env.edgeBase + 4 * j + 1)
  let cv ← Memory.read (env.bufBase + v)
  Memory.write (env.bufBase + v) (cv + 1)
  pure (j + 1)

private def csrCountStepSafe (w : ℕ) (x : CSREnv × ℕ) (_ : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1)

private theorem realizes_csrCountStep_history : Realizes .exact
    csrCountStep (appendWords encCSREnv wordWords) wordWords
    (fun w d s => csrCountStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (csrCountStep d)))
    (fun _ _ => 0) := by
  unfold csrCountStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_csrCountStep : Realizes .exact
    csrCountStep (appendWords encCSREnv wordWords) wordWords csrCountStepSafe (fun _ _ => 0) :=
  realizes_csrCountStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem csrCount_framed {w n edgeBase offBase : ℕ} {es : List (IndexedEdge n)}
    {s₀ : Memory.State} (h16 : Fits w 16) (hwf₀ : Memory.WellFormed w s₀)
    (hfit_m1 : Fits w (es.length + 1)) (hfit_2m : Fits w (2 * es.length))
    (hin₀ : HoldsIndexedEdges edgeBase es s₀.mem)
    (hdisj : edgeBase + 4 * es.length ≤ offBase)
    (hoff_le : offBase + (n + 1) ≤ s₀.frontier)
    (hzero : ∀ j < n + 1, s₀.mem (offBase + j) = 0) :
    let S := Set.Ico offBase (offBase + n)
    iterationSafe csrCountStep csrCountStepSafe w ⟨edgeBase, offBase⟩ es.length 0 s₀ ∧
    Memory.FramedTriple w s₀ (iterate csrCountStep ⟨edgeBase, offBase⟩ es.length 0)
      (6 * es.length) S fun _ s₁ =>
        s₁.frontier = s₀.frontier ∧ Memory.WellFormed w s₁ ∧
        (∀ u : Fin n, s₁.mem (offBase + u.val) = edgeDegPrefix es es.length u) ∧
        s₁.mem (offBase + n) = 0 := by
  have ⟨hsafe, h⟩ := Memory.FramedTriple.iterate (w := w) (body := csrCountStep)
    (safe := csrCountStepSafe) (d := ⟨edgeBase, offBase⟩) (c := 6)
    (S := Set.Ico offBase (offBase + n))
    (fun k a t => a = k ∧ t.frontier = s₀.frontier ∧
      (∀ u : Fin n, t.mem (offBase + u.val) = edgeDegPrefix es k u) ∧ t.mem (offBase + n) = 0)
    ⟨rfl, rfl, fun u => (hzero u (by omega)).trans (edgeDegPrefix_zero es u).symm,
      hzero n (by omega)⟩
    (fun k hk a t ⟨ha, htfr, hdeg, hend⟩ ⟨hfr, hframe⟩ => by
      subst a
      obtain ⟨hu, hv, _, _⟩ :=
        hin₀.congr (fun x _ hx => hframe x (by omega) (by region_omega)) k hk
      have hu_lt := es[k].u.isLt
      have hv_lt := es[k].v.isLt
      have hcu : t.mem (offBase + t.mem (edgeBase + 4 * k)) = edgeDegPrefix es k es[k].u :=
        hu ▸ hdeg _
      have hcu_le := edgeDegPrefix_le es k hk.le es[k].u
      have hcv_le := edgeDegPrefix_le es k hk.le es[k].v
      have hv_mid : Function.update t.mem (offBase + t.mem (edgeBase + 4 * k))
          (t.mem (offBase + t.mem (edgeBase + 4 * k)) + 1) (edgeBase + 4 * k + 1) = es[k].v := by
        rw [Function.update_of_ne (by omega), hv]
      refine ⟨⟨h16, hfit_m1.of_le (by omega)⟩, ?_⟩
      unfold csrCountStep
      framed_triple
      · dsimp only; rw [hv_mid, hu, Function.update_apply]
        split_ifs <;> fits [hdeg es[k].u, hdeg es[k].v]
      · dsimp only; rw [hv_mid, hu]
        refine ⟨rfl, htfr, fun u => ?_, ?_⟩
        · rw [edgeDegPrefix_succ es hk u, ← hdeg u]
          simp only [Function.update_apply, add_right_inj, Fin.val_inj]
          split_ifs <;> subst_vars <;> first | omega | simp only [‹es[k].v = es[k].u›]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hend])
    (n := es.length) fun _ _ h _ => h
  exact ⟨hsafe, (h.wellFormed hwf₀).mono le_rfl fun _ _ ⟨⟨_, h1, h2, h3⟩, h4⟩ => ⟨h1, h4, h2, h3⟩⟩

private structure CSRScatterEnv where
  edgeBase : ℕ
  curBase : ℕ
  adjBase : ℕ

private word_enc_structure encCSRScatterEnv : CSRScatterEnv where
  edgeBase : wordWords,
  curBase : wordWords,
  adjBase : wordWords

private instance : WordEncoding CSRScatterEnv := ⟨3, encCSRScatterEnv⟩

private def csrScatterStep (x : CSRScatterEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let j := Prod.snd x
  let u ← Memory.read (env.edgeBase + 4 * j)
  let v ← Memory.read (env.edgeBase + 4 * j + 1)
  let pu ← Memory.read (env.curBase + u)
  Memory.write (env.curBase + u) (pu + 1)
  Memory.write (env.adjBase + 2 * pu) v
  Memory.write (env.adjBase + 2 * pu + 1) j
  let pv ← Memory.read (env.curBase + v)
  Memory.write (env.curBase + v) (pv + 1)
  Memory.write (env.adjBase + 2 * pv) u
  Memory.write (env.adjBase + 2 * pv + 1) j
  pure (j + 1)

private def csrScatterStepSafe (w : ℕ) (x : CSRScatterEnv × ℕ) (_ : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1)

private theorem realizes_csrScatterStep_history : Realizes .exact
    csrScatterStep (appendWords encCSRScatterEnv wordWords) wordWords
    (fun w d s => csrScatterStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (csrScatterStep d)))
    (fun _ _ => 0) := by
  unfold csrScatterStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_csrScatterStep : Realizes .exact
    csrScatterStep (appendWords encCSRScatterEnv wordWords) wordWords csrScatterStepSafe
    (fun _ _ => 0) :=
  realizes_csrScatterStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem csrScatterOne_mem_slice {n adj cur : ℕ}
    (mem : ℕ → ℕ) (off : Fin (n + 1) → ℕ) (hmono : ∀ u : Fin n, off u.castSucc ≤ off u.succ)
    (lenOf : Fin n → ℕ) (x₀ : Fin n) (nb eIdx : ℕ)
    (hadj_cur : adj + 2 * off ⟨n, Nat.lt_succ_self n⟩ ≤ cur)
    (hcur : ∀ u : Fin n, mem (cur + u.val) = off u.castSucc + lenOf u)
    (hle : lenOf x₀ < off x₀.succ - off x₀.castSucc)
    (hsep : ∀ u : Fin n, off u.castSucc + lenOf u ≤ off u.succ) :
    let pos := mem (cur + x₀.val)
    let mem' := Function.update (Function.update (Function.update mem (cur + x₀.val) (pos + 1))
      (adj + 2 * pos) nb) (adj + 2 * pos + 1) eIdx
    (∀ u : Fin n, mem' (cur + u.val) =
      off u.castSucc + (if u = x₀ then lenOf u + 1 else lenOf u)) ∧
    (∀ u : Fin n, u ≠ x₀ → ∀ j < lenOf u,
      mem' (adj + 2 * (off u.castSucc + j)) = mem (adj + 2 * (off u.castSucc + j)) ∧
      mem' (adj + 2 * (off u.castSucc + j) + 1) = mem (adj + 2 * (off u.castSucc + j) + 1)) ∧
    (∀ j < lenOf x₀,
      mem' (adj + 2 * (off x₀.castSucc + j)) = mem (adj + 2 * (off x₀.castSucc + j)) ∧
      mem' (adj + 2 * (off x₀.castSucc + j) + 1) = mem (adj + 2 * (off x₀.castSucc + j) + 1)) ∧
    (mem' (adj + 2 * (off x₀.castSucc + lenOf x₀)) = nb ∧
     mem' (adj + 2 * (off x₀.castSucc + lenOf x₀) + 1) = eIdx) ∧
    (∀ a, ¬(cur ≤ a ∧ a < cur + n) → ¬(adj ≤ a ∧ a < adj + 2 * off ⟨n, Nat.lt_succ_self n⟩) →
      mem' a = mem a) ∧
    pos < off ⟨n, Nat.lt_succ_self n⟩ := by
  intro pos mem'
  have hmono' : Monotone off := Fin.monotone_iff_le_succ.mpr hmono
  have hpos_eq : pos = off x₀.castSucc + lenOf x₀ := hcur x₀
  have hx₀_hi : off x₀.succ ≤ off ⟨n, Nat.lt_succ_self n⟩ :=
    hmono' (show x₀.succ.val ≤ n by rw [Fin.val_succ]; omega)
  have hpos_lt_end : pos + 1 ≤ off ⟨n, Nat.lt_succ_self n⟩ := by omega
  have hcur_gt : ∀ y : Fin n, ∀ q, q < 2 * off ⟨n, Nat.lt_succ_self n⟩ →
      adj + q ≠ cur + y.val := fun y q hq => by omega
  have hdisj_other : ∀ u : Fin n, u ≠ x₀ → ∀ j < lenOf u,
      off u.castSucc + j ≠ pos := fun u hu j hj => by
    have := u.isLt; have := x₀.isLt
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hu) with hlt | hlt
    · have h1 : off u.succ ≤ off x₀.castSucc :=
        hmono' (show u.succ.val ≤ x₀.castSucc.val by rw [Fin.val_succ, Fin.val_castSucc]; omega)
      have h2 := hsep u
      omega
    · have h1 : off x₀.succ ≤ off u.castSucc :=
        hmono' (show x₀.succ.val ≤ u.castSucc.val by rw [Fin.val_succ, Fin.val_castSucc]; omega)
      omega
  refine ⟨fun u => ?_, fun u hu j hj => ?_, fun j hj => ?_, ⟨?_, ?_⟩, fun a hc ha => ?_,
    by omega⟩
  · dsimp only [mem']
    have hu1 : adj + 2 * pos + 1 ≠ cur + u.val := by
      have := hcur_gt u (2 * pos + 1) (by omega); omega
    have hu2 : adj + 2 * pos ≠ cur + u.val := hcur_gt u (2 * pos) (by omega)
    rw [Function.update_of_ne hu1.symm, Function.update_of_ne hu2.symm]
    by_cases hux : u = x₀
    · subst u
      rw [Function.update_self, hpos_eq]
      simp only [↓reduceIte]; omega
    · rw [Function.update_of_ne (by intro h; apply hux; exact Fin.ext (by omega))]
      simp only [hux, ↓reduceIte]
      exact hcur u
  · have hne := hdisj_other u hu j hj
    have hu_hi : off u.succ ≤ off ⟨n, Nat.lt_succ_self n⟩ :=
      hmono' (show u.succ.val ≤ n by rw [Fin.val_succ]; omega)
    have hsep_u := hsep u
    have hcur1 := hcur_gt x₀ (2 * (off u.castSucc + j)) (by omega)
    have hcur2 := hcur_gt x₀ (2 * (off u.castSucc + j) + 1) (by omega)
    dsimp only [mem']
    refine ⟨?_, ?_⟩ <;>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · have hcur1 := hcur_gt x₀ (2 * (off x₀.castSucc + j)) (by omega)
    have hcur2 := hcur_gt x₀ (2 * (off x₀.castSucc + j) + 1) (by omega)
    dsimp only [mem']
    refine ⟨?_, ?_⟩ <;>
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · dsimp only [mem']
    rw [← hpos_eq]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · dsimp only [mem']
    rw [← hpos_eq, Function.update_self]
  · dsimp only [mem']
    have h1 := x₀.isLt
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]

private theorem csrScatter_framed {w n edgeBase adj cur fEnd : ℕ}
    {es : List (IndexedEdge n)} {t₂ : Memory.State} (offFn : Fin (n + 1) → ℕ)
    (h16 : Fits w 16) (hfit_m1 : Fits w (es.length + 1)) (hfit_n1 : Fits w (n + 1))
    (hfit_2m : Fits w (2 * es.length))
    (hfEnd_rel : fEnd = cur + n ∧ cur = adj + 4 * es.length ∧ edgeBase + 4 * es.length ≤ adj)
    (ht₂_fr : t₂.frontier = fEnd) (hwt₂ : Memory.WellFormed w t₂)
    (ht₂_in : HoldsIndexedEdges edgeBase es t₂.mem)
    (hoffFn_mono : ∀ u : Fin n, offFn u.castSucc ≤ offFn u.succ)
    (hoffFn_diff : ∀ u : Fin n, offFn u.succ - offFn u.castSucc = edgeDegPrefix es es.length u)
    (hoffVal_n : offFn ⟨n, Nat.lt_succ_self n⟩ = 2 * es.length)
    (ht₂_cur : ∀ u : Fin n, t₂.mem (cur + u.val) = offFn u.castSucc) :
    let S₃ := Set.Ico cur (cur + n) ∪ Set.Ico adj (adj + 4 * es.length)
    iterationSafe csrScatterStep csrScatterStepSafe w ⟨edgeBase, cur, adj⟩ es.length 0 t₂ ∧
    Memory.FramedTriple w t₂ (iterate csrScatterStep ⟨edgeBase, cur, adj⟩ es.length 0)
      (10 * es.length) S₃ fun _ t₃ =>
        t₃.frontier = fEnd ∧ Memory.WellFormed w t₃ ∧
        ∀ u : Fin n, ((List.range (edgeDegPrefix es es.length u)).map fun j =>
          let p := offFn u.castSucc + j
          (t₃.mem (adj + 2 * p), t₃.mem (adj + 2 * p + 1))).Perm
          (((List.finRange es.length).filter fun i => decide (es[i.val].u = u)).map
            (fun i => (es[i.val].v.val, i.val)) ++
           ((List.finRange es.length).filter fun i => decide (es[i.val].v = u)).map
            (fun i => (es[i.val].u.val, i.val))) := by
  let inv₃ (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = fEnd ∧
    (∀ u : Fin n, t.mem (cur + u.val) = offFn u.castSucc + edgeDegPrefix es k u) ∧
    ∀ u : Fin n, ((List.range (edgeDegPrefix es k u)).map fun j =>
      let p := offFn u.castSucc + j
      (t.mem (adj + 2 * p), t.mem (adj + 2 * p + 1))).Perm
      ((((List.finRange es.length).take k).filter fun i => decide (es[i.val].u = u)).map
        (fun i => (es[i.val].v.val, i.val)) ++
       (((List.finRange es.length).take k).filter fun i => decide (es[i.val].v = u)).map
        (fun i => (es[i.val].u.val, i.val)))
  have hstep : ∀ k < es.length, ∀ a t, inv₃ k a t →
      Memory.Modifies (Set.Ico cur (cur + n) ∪ Set.Ico adj (adj + 4 * es.length)) t₂ t →
      csrScatterStepSafe w (⟨edgeBase, cur, adj⟩, a) t ∧
      Memory.FramedTriple w t (csrScatterStep (⟨edgeBase, cur, adj⟩, a)) 10
        (Set.Ico cur (cur + n) ∪ Set.Ico adj (adj + 4 * es.length)) (inv₃ (k + 1)) := by
    rintro k hk a t ⟨ha, htfr, hcur_k, hperm_k⟩ ⟨hfr, hframe⟩
    subst a
    obtain ⟨hu, hv, _, _⟩ :=
      ht₂_in.congr (fun x _ hx => hframe x (by omega) (by region_omega)) k hk
    let eu := es[k].u
    let ev := es[k].v
    have hu' : t.mem (edgeBase + 4 * k) = eu.val := hu
    have hv' : t.mem (edgeBase + 4 * k + 1) = ev.val := hv
    have heu := eu.isLt
    have hev := ev.isLt
    let len₁ : Fin n → ℕ := fun u => edgeDegPrefix es k u
    have hsep₁ : ∀ u : Fin n, offFn u.castSucc + len₁ u ≤ offFn u.succ := fun u => by
      have hm := edgeDegPrefix_mono es hk.le le_rfl u
      have hd := hoffFn_diff u
      have hmo := hoffFn_mono u
      dsimp only [len₁] at *
      omega
    have hle₁ : len₁ eu < offFn eu.succ - offFn eu.castSucc := by
      have hm := edgeDegPrefix_mono es (show k + 1 ≤ es.length by omega) le_rfl eu
      have hs := edgeDegPrefix_succ es hk eu
      have hd := hoffFn_diff eu
      dsimp only [len₁]
      simp only [show es[k].u = eu from rfl, ↓reduceIte] at hs
      omega
    have hadj_cur : adj + 2 * offFn ⟨n, Nat.lt_succ_self n⟩ ≤ cur := by rw [hoffVal_n]; omega
    obtain ⟨hcur₁, hother₁, hsame₁, hnew₁, -, hpos₁_lt⟩ :=
      csrScatterOne_mem_slice t.mem offFn hoffFn_mono len₁ eu ev.val k hadj_cur hcur_k hle₁ hsep₁
    let pos₁ := t.mem (cur + eu.val)
    let tMid : Memory.State :=
      ⟨Function.update (Function.update (Function.update t.mem (cur + eu.val) (pos₁ + 1))
        (adj + 2 * pos₁) ev.val) (adj + 2 * pos₁ + 1) k, t.frontier⟩
    have htMid_new : tMid.mem (adj + 2 * (offFn eu.castSucc + len₁ eu)) = ev.val ∧
        tMid.mem (adj + 2 * (offFn eu.castSucc + len₁ eu) + 1) = k := hnew₁
    let len₂ : Fin n → ℕ := fun u => if u = eu then len₁ u + 1 else len₁ u
    have hsep₂ : ∀ u : Fin n, offFn u.castSucc + len₂ u ≤ offFn u.succ := fun u => by
      dsimp only [len₂]
      split_ifs with hue
      · rw [hue]; have := hle₁; omega
      · exact hsep₁ u
    have hle₂ : len₂ ev < offFn ev.succ - offFn ev.castSucc := by
      have hm := edgeDegPrefix_mono es (show k + 1 ≤ es.length by omega) le_rfl ev
      have hs := edgeDegPrefix_succ es hk ev
      have hd := hoffFn_diff ev
      dsimp only [len₂, len₁, eu, ev] at hs hm hd ⊢
      by_cases hee : es[k].v = es[k].u
      · simp only [hee, ↓reduceIte] at hs hm hd ⊢; omega
      · simp only [hee, Ne.symm hee, ↓reduceIte] at hs hm hd ⊢; omega
    obtain ⟨hcur₂, hother₂, hsame₂, hnew₂, -, hpos₂_lt⟩ :=
      csrScatterOne_mem_slice _ offFn hoffFn_mono len₂ ev eu.val k hadj_cur hcur₁ hle₂ hsep₂
    rw [hoffVal_n] at hpos₁_lt hpos₂_lt
    refine ⟨⟨h16, hfit_m1.of_le (by omega)⟩, ?_⟩
    unfold csrScatterStep
    eapply Memory.FramedTriple.mono (hQ := fun _ _ => id)
    on_goal 1 =>
      dsimp only
      framed_triple_step; framed_triple_step
      rw [hu', hv']
      repeat' framed_triple_step
    on_goal 2 => omega
    let pos₂ := tMid.mem (cur + ev.val)
    let tEnd : Memory.State :=
      ⟨Function.update (Function.update (Function.update tMid.mem (cur + ev.val) (pos₂ + 1))
        (adj + 2 * pos₂) eu.val) (adj + 2 * pos₂ + 1) k, t.frontier⟩
    have htEnd_new : tEnd.mem (adj + 2 * (offFn ev.castSucc + len₂ ev)) = eu.val ∧
        tEnd.mem (adj + 2 * (offFn ev.castSucc + len₂ ev) + 1) = k := hnew₂
    show inv₃ (k + 1) (k + 1) tEnd
    refine ⟨rfl, htfr, fun u => ?_, fun u => ?_⟩
    · dsimp only [tEnd]
      rw [hcur₂ u, edgeDegPrefix_succ es hk u]
      dsimp only [len₂, len₁, eu, ev]
      split_ifs <;> subst_vars <;> omega
    · have hs₁_u : ∀ j < len₁ u,
          tMid.mem (adj + 2 * (offFn u.castSucc + j)) = t.mem (adj + 2 * (offFn u.castSucc + j)) ∧
          tMid.mem (adj + 2 * (offFn u.castSucc + j) + 1) =
            t.mem (adj + 2 * (offFn u.castSucc + j) + 1) := fun j hj => by
        by_cases hu1 : u = eu
        · subst u; exact hsame₁ j hj
        · exact hother₁ u hu1 j hj
      have hs₂_u : ∀ j < len₂ u,
          tEnd.mem (adj + 2 * (offFn u.castSucc + j)) =
            tMid.mem (adj + 2 * (offFn u.castSucc + j)) ∧
          tEnd.mem (adj + 2 * (offFn u.castSucc + j) + 1) =
            tMid.mem (adj + 2 * (offFn u.castSucc + j) + 1) := fun j hj => by
        by_cases hu2 : u = ev
        · subst u; exact hsame₂ j hj
        · exact hother₂ u hu2 j hj
      have hpref_keep :
          ((List.range (len₁ u)).map fun j =>
            let p := offFn u.castSucc + j
            (tEnd.mem (adj + 2 * p), tEnd.mem (adj + 2 * p + 1))) =
          ((List.range (len₁ u)).map fun j =>
            let p := offFn u.castSucc + j
            (t.mem (adj + 2 * p), t.mem (adj + 2 * p + 1))) := by
        refine List.map_congr_left fun j hj => ?_
        rw [List.mem_range] at hj
        have hlen_le : len₁ u ≤ len₂ u := by dsimp only [len₂]; split_ifs <;> omega
        obtain ⟨a1, b1⟩ := hs₂_u j (by omega)
        obtain ⟨a2, b2⟩ := hs₁_u j hj
        exact Prod.ext (a1.trans a2) (b1.trans b2)
      have hperm_prev := hperm_k u
      have htake_succ : (List.finRange es.length).take (k + 1) =
          (List.finRange es.length).take k ++ [⟨k, hk⟩] := by
        rw [List.take_add_one,
          List.getElem?_eq_getElem (by simp only [List.length_finRange]; exact hk),
          Option.toList_some]
        simp only [List.getElem_finRange, Fin.cast_mk]
      have hsucc_u :
          ((List.finRange es.length).take (k + 1)).filter (fun i => decide (es[i.val].u = u)) =
          ((List.finRange es.length).take k).filter (fun i => decide (es[i.val].u = u)) ++
            if eu = u then [⟨k, hk⟩] else [] := by
        rw [htake_succ, List.filter_append]
        split_ifs with h <;> simp [eu, h]
      have hsucc_v :
          ((List.finRange es.length).take (k + 1)).filter (fun i => decide (es[i.val].v = u)) =
          ((List.finRange es.length).take k).filter (fun i => decide (es[i.val].v = u)) ++
            if ev = u then [⟨k, hk⟩] else [] := by
        rw [htake_succ, List.filter_append]
        split_ifs with h <;> simp [ev, h]
      rw [hsucc_u, hsucc_v, List.map_append, List.map_append, edgeDegPrefix_succ es hk u]
      have hcomm : ∀ A B : List (ℕ × ℕ), ∀ x : ℕ × ℕ,
          ((A ++ B) ++ [x]).Perm ((A ++ [x]) ++ B) := fun A B x => by
        rw [List.append_assoc A B [x], List.append_assoc A [x] B]
        exact List.Perm.append_left A List.perm_append_comm
      by_cases hu1 : u = eu <;> by_cases hu2 : u = ev
      · have heu_ev : eu = ev := hu1.symm.trans hu2
        subst u
        simp only [show es[k].u = eu from rfl, show es[k].v = ev from rfl,
          ← heu_ev, ↓reduceIte]
        rw [List.range_succ, List.map_append, List.range_succ, List.map_append,
          List.map_singleton, List.map_singleton, List.map_singleton, List.map_singleton,
          hpref_keep]
        have hesv_eu : (es[k].v.val, k) = (eu.val, k) :=
          congrArg (fun x : Fin n => (x.val, k)) heu_ev.symm
        have hesu_eu : (es[k].u.val, k) = (eu.val, k) := rfl
        dsimp only; rw [hesv_eu, hesu_eu]
        obtain ⟨ha1, hb1⟩ := hs₂_u (len₁ eu) (by dsimp only [len₂]; simp only [↓reduceIte]; omega)
        have hsl1 : (tEnd.mem (adj + 2 * (offFn eu.castSucc + len₁ eu)),
            tEnd.mem (adj + 2 * (offFn eu.castSucc + len₁ eu) + 1)) = (eu.val, k) := by
          rw [ha1, hb1, htMid_new.1, htMid_new.2]
          exact Prod.ext (congrArg Fin.val heu_ev.symm) rfl
        have hl2 : len₂ ev = len₁ eu + 1 := by
          dsimp only [len₂]; simp only [← heu_ev, ↓reduceIte]
        have hsl2 : (tEnd.mem (adj + 2 * (offFn eu.castSucc + (len₁ eu + 1))),
            tEnd.mem (adj + 2 * (offFn eu.castSucc + (len₁ eu + 1)) + 1)) = (eu.val, k) := by
          rw [show offFn eu.castSucc + (len₁ eu + 1) = offFn ev.castSucc + len₂ ev by
            rw [hl2, ← heu_ev]]
          exact Prod.ext htEnd_new.1 htEnd_new.2
        rw [hsl1, hsl2]
        refine (List.Perm.append_right [(eu.val, k)]
          ((List.Perm.append_right [(eu.val, k)] hperm_prev).trans (hcomm _ _ (eu.val, k)))).trans
          ?_
        simp only [List.append_assoc]
        exact List.Perm.refl _
      · have heuv : eu ≠ ev := fun h => hu2 (hu1.trans h)
        subst u
        simp only [show es[k].u = eu from rfl, show es[k].v = ev from rfl,
          Ne.symm heuv, ↓reduceIte, Nat.add_zero, List.map_nil, List.append_nil]
        rw [List.range_succ, List.map_append, List.map_singleton, hpref_keep]
        obtain ⟨ha1, hb1⟩ := hs₂_u (len₁ eu) (by dsimp only [len₂]; simp only [↓reduceIte]; omega)
        rw [ha1, hb1, htMid_new.1, htMid_new.2]
        have hesv_ev : (es[k].v.val, k) = (ev.val, k) := rfl
        rw [hesv_ev]
        exact (List.Perm.append_right [(ev.val, k)] hperm_prev).trans (hcomm _ _ (ev.val, k))
      · have hevu : ev ≠ eu := fun h => hu1 (hu2.trans h)
        subst u
        simp only [show es[k].u = eu from rfl, show es[k].v = ev from rfl,
          Ne.symm hevu, ↓reduceIte, Nat.add_zero, List.map_nil, List.append_nil]
        rw [List.range_succ, List.map_append, List.map_singleton, List.map_singleton, hpref_keep]
        have hl2 : len₂ ev = len₁ ev := by
          dsimp only [len₂]; simp only [hevu, ↓reduceIte]
        have hsl : (tEnd.mem (adj + 2 * (offFn ev.castSucc + len₁ ev)),
            tEnd.mem (adj + 2 * (offFn ev.castSucc + len₁ ev) + 1)) = (eu.val, k) := by
          rw [← hl2]; exact Prod.ext htEnd_new.1 htEnd_new.2
        rw [hsl]
        have hesu_eu : (es[k].u.val, k) = (eu.val, k) := rfl
        rw [hesu_eu]
        exact (List.Perm.append_right [(eu.val, k)] hperm_prev).trans (by rw [List.append_assoc])
      · simp only [show es[k].u = eu from rfl, show es[k].v = ev from rfl,
          Ne.symm hu1, Ne.symm hu2, ↓reduceIte, Nat.add_zero, List.map_nil, List.append_nil]
        rw [hpref_keep]
        exact hperm_prev
  obtain ⟨hsafe₃, h₃⟩ := Memory.FramedTriple.iterate inv₃
    ⟨rfl, ht₂_fr, fun u => by rw [edgeDegPrefix_zero, Nat.add_zero]; exact ht₂_cur u,
      fun u => by simp only [edgeDegPrefix_zero, List.range_zero, List.map_nil, List.take_zero,
        List.filter_nil, List.append_nil, List.Perm.refl]⟩ hstep fun _ _ h _ => h
  refine ⟨hsafe₃, (h₃.wellFormed hwt₂).mono le_rfl
    fun _ _ ⟨⟨_, hfr₃, _, hperm₃⟩, hwt₃⟩ => ⟨hfr₃, hwt₃, fun u => ?_⟩⟩
  have htake_full : (List.finRange es.length).take es.length = List.finRange es.length :=
    List.take_of_length_le (by simp)
  simpa only [htake_full] using hperm₃ u

/-! ## `buildUndirCSR`: Program, Realization, and Framed Specification -/

/-- Construct undirected CSR arrays `⟨offBase, adjBase⟩` for `g : GraphSlice` in `O(m + n)`
memory operations (`m = g.numEdges`, `n = g.numVertices`). -/
def buildUndirCSR (g : GraphSlice) : Memory.Prog UndirCSR := do
  let off ← Memory.allocBlock (g.numVertices + 1)
  let _ ← iterate csrCountStep ⟨g.edgeBase, off.base⟩ g.numEdges 0
  let _ ← prefixSumProg off.base (g.numVertices + 1)
  let adj ← Memory.allocBlockDirty (4 * g.numEdges)
  let cur ← Memory.allocBlockDirty g.numVertices
  Memory.copy off.base cur.base g.numVertices
  let _ ← iterate csrScatterStep ⟨g.edgeBase, cur.base, adj.base⟩ g.numEdges 0
  pure ⟨off.base, adj.base⟩

private theorem buildUndirCSR_word_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (2 * n + 4 * es.length + 1))) :
    let m := es.length
    let off := s.frontier
    let adj := off + (n + 1)
    let cur := adj + 4 * m
    let fEnd := cur + n
    let s₀ : Memory.State := ⟨clear s.mem off (n + 1), off + (n + 1)⟩
    let s₁ := (Memory.spec 0).clientState s₀ (iterate csrCountStep ⟨edgeBase, off⟩ m 0)
    let s₂_pre := (Memory.spec 0).clientState s₁ (prefixSumProg off (n + 1))
    let s₂_cur : Memory.State := ⟨s₂_pre.mem, fEnd⟩
    let s₂ := (Memory.spec 0).clientState s₂_cur (Memory.copy off cur n)
    iterationSafe csrCountStep csrCountStepSafe w ⟨edgeBase, off⟩ m 0 s₀ ∧
    s₁.frontier = adj ∧
    s₂_pre.frontier = adj ∧
    Fits w (∑ i ∈ Finset.range (n + 1), s₁.mem (off + i)) ∧
    iterationSafe csrScatterStep csrScatterStepSafe w ⟨edgeBase, cur, adj⟩ m 0 s₂ ∧
    Memory.FramedTriple w s (buildUndirCSR ⟨n, m, edgeBase⟩) (16 * m + 5 * n + 6) ∅
      fun csr s' =>
        csr.offBase = off ∧ csr.adjBase = adj ∧
        s'.frontier = s.frontier + (2 * n + 4 * m + 1) ∧ Memory.WellFormed w s' ∧
        HoldsUndirCSR csr.offBase csr.adjBase es s'.mem := by
  let m := es.length
  let off := s.frontier
  let adj := off + (n + 1)
  let cur := adj + 4 * m
  let fEnd := cur + n
  have hfit_n1 : Fits w (n + 1) := hfit.of_le (by omega)
  have hfit_m1 : Fits w (m + 1) := hfit.of_le (by omega)
  have hfit_2m : Fits w (2 * m) := hfit.of_le (by omega)
  have hfit_off : Fits w (off + (n + 1)) := hfit.of_le (by omega)
  have hfit_adj : Fits w (off + (n + 1) + 4 * m) := hfit.of_le (by omega)
  let s₀ : Memory.State := ⟨clear s.mem off (n + 1), off + (n + 1)⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .alloc (n + 1)) hfit_off
  have hin₀ : HoldsIndexedEdges edgeBase es s₀.mem :=
    hin.congr fun x hx1 hx2 => clear_of_not_owns (by dsimp only [Block.Owns]; omega)
  have hzero₀ : ∀ j < n + 1, s₀.mem (off + j) = 0 := fun j hj =>
    clear_of_owns (Block.owns_add (b := ⟨off, n + 1⟩) hj)
  obtain ⟨hsafe₁, hft_cnt⟩ := csrCount_framed h16 hwf₀ hfit_m1 hfit_2m hin₀
    (by omega) (by dsimp only [s₀]; omega) hzero₀
  let s₁ := (Memory.spec 0).clientState s₀ (iterate csrCountStep ⟨edgeBase, off⟩ m 0)
  obtain ⟨hv₁, hm₁, hmod₁, hs₁_fr, hwf₁, hdeg₁, hend₁⟩ := framedTriple_iff_realization.mp hft_cnt
  let degAt (i : ℕ) : ℕ := if h : i < n then edgeDegPrefix es m ⟨i, h⟩ else 0
  have hdegAt_val : ∀ u : Fin n, degAt u.val = edgeDegPrefix es m u := fun u => dite_eq_left u.isLt
  have hs₁_sum : ∀ j ≤ n + 1, ∑ i ∈ Finset.range j, s₁.mem (off + i) =
      ∑ i ∈ Finset.range j, degAt i := fun j hj => by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    dsimp only [degAt]
    split_ifs with hlt
    · exact hdeg₁ ⟨i, hlt⟩
    · rw [show i = n by omega, hend₁]
  have hsum_deg : ∑ i ∈ Finset.range n, degAt i = 2 * m := by
    rw [← Fin.sum_univ_eq_sum_range degAt n, Finset.sum_congr rfl fun u _ => hdegAt_val u]
    exact sum_edgeDegPrefix es m (le_refl m)
  have hsum_n1 : ∑ i ∈ Finset.range (n + 1), s₁.mem (off + i) = 2 * m := by
    rw [hs₁_sum (n + 1) (le_refl (n + 1)), Finset.sum_range_succ]
    rw [show degAt n = 0 from dite_eq_right (Nat.lt_irrefl n), Nat.add_zero, hsum_deg]
  have hsum_fit : Fits w (∑ i ∈ Finset.range (n + 1), s₁.mem (off + i)) :=
    hsum_n1 ▸ hfit_2m
  have hft_ps := prefixSumProg_spec hwf₁ hfit_n1 (by rw [hs₁_fr]) hsum_fit
  let s₂_pre := (Memory.spec 0).clientState s₁ (prefixSumProg off (n + 1))
  obtain ⟨hv_ps, hm_ps, hmod_ps, hs₂_res, hs₂_fr, hwf₂_pre, hs₂_vals⟩ :=
    framedTriple_iff_realization.mp hft_ps
  let offFn : Fin (n + 1) → ℕ := fun j => ∑ i ∈ Finset.range j.val, degAt i
  have hoffFn_eq : ∀ j (hj : j < n + 1), s₂_pre.mem (off + j) = offFn ⟨j, hj⟩ := fun j hj => by
    rw [hs₂_vals j hj, hs₁_sum j (le_of_lt hj)]
  have hoffFn_mono : ∀ u : Fin n, offFn u.castSucc ≤ offFn u.succ := fun u => by
    simp only [offFn, Fin.val_castSucc, Fin.val_succ, Finset.sum_range_succ]; omega
  have hoffFn_diff : ∀ u : Fin n, offFn u.succ - offFn u.castSucc = edgeDegPrefix es m u :=
    fun u => by
      simp only [offFn, Fin.val_castSucc, Fin.val_succ, Finset.sum_range_succ, hdegAt_val u]
      omega
  have hoffVal_n : offFn ⟨n, Nat.lt_succ_self n⟩ = 2 * m := hsum_deg
  have hs₂_in_pre : HoldsIndexedEdges edgeBase es s₂_pre.mem :=
    hin₀.congr fun x hx1 hx2 =>
      ((hmod_ps.mem_eq_of_not_mem (by rw [hs₁_fr]; dsimp only [s₀]; omega) (by region_omega)).trans
        (hmod₁.mem_eq_of_not_mem (by dsimp only [s₀]; omega) (by region_omega)))
  let s₂_cur : Memory.State := ⟨s₂_pre.mem, fEnd⟩
  have hwf₂_cur : Memory.WellFormed w s₂_cur :=
    ⟨hfit.of_le (by dsimp only [s₂_cur, fEnd, cur, adj, off, m]; omega), hwf₂_pre.mem_fits⟩
  have hs₂_copy_fit : ∀ i < n, Fits w (s₂_cur.mem (off + i)) := fun i hi => hwf₂_pre.mem_fits _
  let s₂ := (Memory.spec 0).clientState s₂_cur (Memory.copy off cur n)
  have hcp := Memory.FramedTriple.copy (s := s₂_cur) (src := off) (dst := cur) (n := n)
    (Q := fun _ t => t = ⟨Cslib.WordRAM.ArrayCopy.copyPrefix s₂_cur.mem off cur n, fEnd⟩)
    (Or.inl (by omega)) (show off + n ≤ fEnd by omega) (show cur + n ≤ fEnd by omega)
    hs₂_copy_fit rfl
  obtain ⟨-, -, -, hs₂_eq, hwf₂⟩ := framedTriple_iff_realization.mp (hcp.wellFormed hwf₂_cur)
  have hs₂_mem_eq : s₂.mem = Cslib.WordRAM.ArrayCopy.copyPrefix s₂_cur.mem off cur n :=
    congrArg Memory.State.mem hs₂_eq
  have hs₂_fr_eq : s₂.frontier = fEnd := congrArg Memory.State.frontier hs₂_eq
  have hs₂_in : HoldsIndexedEdges edgeBase es s₂.mem := hs₂_in_pre.congr fun x hx1 hx2 => by
    rw [hs₂_mem_eq, Cslib.WordRAM.ArrayCopy.copyPrefix_outside (by omega)]
  have hs₂_cur_eq : ∀ u : Fin n, s₂.mem (cur + u.val) = offFn u.castSucc := fun u => by
    rw [hs₂_mem_eq, Cslib.WordRAM.ArrayCopy.copyPrefix_read u.isLt]
    exact hoffFn_eq u.val (by omega)
  obtain ⟨hsafe₃, hft_sc⟩ := csrScatter_framed offFn h16 hfit_m1 hfit_n1 hfit_2m
    ⟨rfl, rfl, by omega⟩ hs₂_fr_eq hwf₂ hs₂_in hoffFn_mono hoffFn_diff hoffVal_n hs₂_cur_eq
  refine ⟨hsafe₁, hs₁_fr, hs₂_fr.trans hs₁_fr, hsum_fit, hsafe₃, ?_⟩
  exact Memory.FramedTriple.mono
    (Memory.FramedTriple.frame_empty_of_ge_frontier (S := Set.Ico off fEnd)
    (Memory.FramedTriple.allocBlock_bind hfit_off
    (Memory.FramedTriple.seq hft_cnt (by region_omega)
    (Memory.FramedTriple.seq hft_ps (by region_omega)
    (Memory.FramedTriple.allocBlockDirty_bind_at (hs₂_fr.trans hs₁_fr) hfit_adj
    (Memory.FramedTriple.allocBlockDirty_bind (hfit.of_le (by omega) : Fits w (cur + n))
    (Memory.FramedTriple.seq hcp (by region_omega)
    (Memory.FramedTriple.call hft_sc (by region_omega)
      fun _ t₃ ⟨hfr₃, hwt₃, hperm₃⟩ (hm₃ : Memory.Modifies _ s₂ t₃) => by
      have hoff : ∀ j (hj : j < n + 1), t₃.mem (off + j) = offFn ⟨j, hj⟩ := fun j hj => by
        rw [hm₃.mem_eq_of_not_mem (by omega) (by region_omega), hs₂_mem_eq,
          Cslib.WordRAM.ArrayCopy.copyPrefix_outside (by omega)]
        exact hoffFn_eq j hj
      refine Memory.FramedTriple.pure (c := 0) ⟨rfl, rfl, by omega, hwt₃,
        show HoldsUndirCSR off adj es t₃.mem from
        ⟨by rw [← Nat.add_zero off, hoff 0 (Nat.zero_lt_succ n)]; rfl, fun u => ?_,
          by rw [hoff n (Nat.lt_succ_self n)]; exact hoffVal_n, fun u => ?_⟩⟩
      all_goals
        rw [show t₃.mem (off + u.val) = offFn u.castSucc from hoff u.val (by omega),
          show t₃.mem (off + u.val + 1) = offFn u.succ from hoff (u.val + 1) (by omega)]
      · exact hoffFn_mono u
      · rw [hoffFn_diff u]; exact hperm₃ u)))))))
    fun _ ha => (Set.mem_Ico.mp ha).1) (by dsimp only; omega) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `buildUndirCSR` with `work = 0`. -/
theorem realizes_buildUndirCSR :
    Realizes .exact buildUndirCSR WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (2 * g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact buildUndirCSR WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let off := s.frontier
        let adj := off + (g.numVertices + 1)
        let cur := adj + 4 * g.numEdges
        let fEnd := cur + g.numVertices
        let s₀ : Memory.State := ⟨clear s.mem off (g.numVertices + 1), adj⟩
        let it₁ := iterate csrCountStep ⟨g.edgeBase, off⟩ g.numEdges 0
        let s₁ := (Memory.spec 0).clientState s₀ it₁
        let ps := prefixSumProg off (g.numVertices + 1)
        let s₂_pre := (Memory.spec 0).clientState s₁ ps
        let s₂_cur : Memory.State := ⟨s₂_pre.mem, fEnd⟩
        let s₂ := (Memory.spec 0).clientState s₂_cur (Memory.copy off cur g.numVertices)
        Fits w 16 ∧ Fits w fEnd ∧
        s₁.frontier = adj ∧ s₂_pre.frontier = adj ∧
        iterationSafe csrCountStep csrCountStepSafe w ⟨g.edgeBase, off⟩ g.numEdges 0 s₀ ∧
        Fits w (∑ i ∈ Finset.range (g.numVertices + 1), s₁.mem (off + i)) ∧
        iterationSafe csrScatterStep csrScatterStepSafe w
          ⟨g.edgeBase, cur, adj⟩ g.numEdges 0 s₂)
      (fun _ _ => 0) := by
    unfold buildUndirCSR
    have hblkZ_R : ∀ (st : Memory.State) (k : ℕ),
        (Memory.spec 0).clientResult st (Memory.allocBlock k) = ⟨st.frontier, k⟩ :=
      fun _ _ => rfl
    have hblkZ_S : ∀ (st : Memory.State) (k : ℕ),
        (Memory.spec 0).clientState st (Memory.allocBlock k) =
          ⟨clear st.mem st.frontier k, st.frontier + k⟩ :=
      fun _ _ => rfl
    have hblkR : ∀ (st : Memory.State) (k : ℕ),
        (Memory.spec 0).clientResult st (Memory.allocBlockDirty k) = ⟨st.frontier, k⟩ :=
      fun _ _ => rfl
    have hblkS : ∀ (st : Memory.State) (k : ℕ),
        (Memory.spec 0).clientState st (Memory.allocBlockDirty k) = ⟨st.mem, st.frontier + k⟩ :=
      fun _ _ => rfl
    realize [realizes_allocBlock, realizes_csrCountStep, realizes_prefixSumProg,
      realizes_allocBlockDirty, realizes_copy, realizes_csrScatterStep]
    all_goals
      rcases h with ⟨h16, hfit, hs₁_fr, hs₂_fr, hsafe₁, hsum, hsafe₃⟩
      try simp only [hblkZ_R, hblkZ_S] at hs₁_fr hs₂_fr hsafe₁ hsum hsafe₃ ⊢
      first
      | exact h16.of_le (by decide)
      | exact hfit.of_le (by omega)
      | rw [hs₁_fr]
      | exact hsum
      | exact iterationSafe_imp hsafe₁ (fun _ => rfl) (fun _ _ hs => hs)
      | (simp only [hblkR, hblkS, hs₂_fr] at *
         first
         | omega
         | exact iterationSafe_imp hsafe₃ (fun _ => rfl) (fun _ _ hs => hs))
  refine hraw.consequence (fun w g s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨es, hes_len, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have hspec := buildUndirCSR_word_spec h16 hmem hin (hes_len ▸ hin_lt) (hes_len ▸ hfit)
  rcases hspec with ⟨hsafe₁, hs₁_fr, hs₂_fr, hsum_fit, hsafe₃, _⟩
  refine ⟨h16, hfit.of_le (by omega), by simpa [hes_len] using hs₁_fr,
    by simpa [hes_len] using hs₂_fr, by simpa [hes_len] using hsafe₁,
    by simpa [hes_len] using hsum_fit, by simpa [hes_len] using hsafe₃⟩

/-- Framed specification for `buildUndirCSR`: allocates and populates an undirected CSR
representation for `es` starting at `offBase = s.frontier` leaving all cells below `s.frontier`
untouched, in at most `16 * es.length + 5 * n + 6` memory operations. -/
theorem buildUndirCSR_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (2 * n + 4 * es.length + 1))) :
    Memory.FramedTriple w s (buildUndirCSR ⟨n, es.length, edgeBase⟩)
      (16 * es.length + 5 * n + 6) ∅ fun csr s' =>
        csr.offBase = s.frontier ∧
        csr.adjBase = s.frontier + (n + 1) ∧
        s'.frontier = s.frontier + (2 * n + 4 * es.length + 1) ∧
        Memory.WellFormed w s' ∧
        HoldsUndirCSR csr.offBase csr.adjBase es s'.mem :=
  (buildUndirCSR_word_spec h16 hwf hin hin_lt hfit).2.2.2.2.2

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
