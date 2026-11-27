/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.CSR
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg

/-!
# Word-RAM Connected Components, Contraction, and Vertex Compaction

Implements three linear-time Word-RAM graph primitives over stride-4 `IndexedEdge` layouts and
undirected CSR graphs, reusing `ArrayOps.fillConstProg`, `Memory.allocBlockDirty`,
`Memory.FramedTriple`, `LoopFrame.iterate_potential_spec`, and
`LoopFrame.boundedWhile_potential_spec`.

## Main definitions

* `ComponentsResult`, `ContractEdgesArgs`, `CompactResult`: Word-RAM I/O structures with encodings.
* `connectedComponentsProg`: `O(m + n)` BFS connected components returning `ComponentsResult`.
* `contractEdgesProg`: `O(m)` parallel edge contraction along a component array `compBase`.
* `compactVerticesProg`: `O(m + n)` isolated-vertex compaction returning `CompactResult`.

## Main results

* `realizes_connectedComponentsProg`, `connectedComponentsProg_spec`: correctness and linear cost.
* `realizes_contractEdgesProg`, `contractEdgesProg_spec`: correctness and edge-contraction cost.
* `realizes_compactVerticesProg`, `compactVerticesProg_spec`, `compactVertices_isSimple`,
  `compactVertices_isMinSpanningForest`: correctness, simplicity, and MSF preservation.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest

/-! ## Public Result and Argument Structures -/

/-- Output handles produced by `connectedComponentsProg`. -/
structure ComponentsResult where
  /-- Base address of the `n`-word component label array `comp : Fin n → Fin numComps`. -/
  compBase : ℕ
  /-- Number of connected components in the input graph. -/
  numComps : ℕ

/-- Faithful two-word encoding of `ComponentsResult` as `[compBase, numComps]`. -/
word_enc_structure encComponentsResult : ComponentsResult where
  compBase : wordWords,
  numComps : wordWords

instance : WordEncoding ComponentsResult := ⟨2, encComponentsResult⟩

/-- Arguments for `contractEdgesProg`: edge slice `(numEdges, edgeBase)` and
vertex component array `compBase`. -/
structure ContractEdgesArgs where
  /-- Number of stride-4 edges `m` at `edgeBase`. -/
  numEdges : ℕ
  /-- Base address of the input stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of the vertex component label array. -/
  compBase : ℕ

/-- Faithful three-word encoding of `ContractEdgesArgs` as `[numEdges, edgeBase, compBase]`. -/
word_enc_structure encContractEdgesArgs : ContractEdgesArgs where
  numEdges : wordWords,
  edgeBase : wordWords,
  compBase : wordWords

instance : WordEncoding ContractEdgesArgs := ⟨3, encContractEdgesArgs⟩

/-- Output handles produced by `compactVerticesProg`. -/
structure CompactResult where
  /-- Base address of the compacted stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Number of non-isolated vertices `nOut ≤ n`. -/
  numVertices : ℕ
  /-- Base address of the `n`-word table mapping active vertices `u` to compacted index `y`. -/
  liftBase : ℕ

/-- Faithful three-word encoding of `CompactResult` as `[edgeBase, numVertices, liftBase]`. -/
word_enc_structure encCompactResult : CompactResult where
  edgeBase : wordWords,
  numVertices : wordWords,
  liftBase : wordWords

instance : WordEncoding CompactResult := ⟨3, encCompactResult⟩

/-! ## Partition Connectivity Helpers -/

private theorem closed_of_edgePartition_rel {n : ℕ} (es : List (IndexedEdge n))
    (P : Fin n → Prop) (hclosed : ∀ e ∈ es, P e.u ↔ P e.v)
    {x y : Fin n} (hrel : (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true) :
    P x ↔ P y := by
  rw [rel_edgePartition_iff_eqvGen] at hrel
  induction hrel with
  | rel a b hab =>
    rcases hab with ⟨e, he, rfl, rfl⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hclosed e' he'
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem rel_of_indexedEdge {n : ℕ} {es : List (IndexedEdge n)}
    (e : IndexedEdge n) (he : e ∈ es) :
    (edgePartition (es.map IndexedEdge.toWeighted)).rel e.u e.v = true :=
  (rel_edgePartition_iff_eqvGen (es.map IndexedEdge.toWeighted) e.u e.v).mpr
    (.rel _ _ ⟨e.toWeighted, List.mem_map.mpr ⟨e, he, rfl⟩, rfl, rfl⟩)

private def edgesOfMem (n m edgeBase : ℕ) (mem : ℕ → ℕ)
    (hedges : ∀ j < m, mem (edgeBase + 4 * j) < n ∧ mem (edgeBase + 4 * j + 1) < n) :
    List (IndexedEdge n) := List.ofFn fun k : Fin m =>
    ⟨⟨mem (edgeBase + 4 * k.val), (hedges k.val k.isLt).1⟩,
     ⟨mem (edgeBase + 4 * k.val + 1), (hedges k.val k.isLt).2⟩,
     mem (edgeBase + 4 * k.val + 2), mem (edgeBase + 4 * k.val + 3)⟩

private theorem edgesOfMem_length (n m edgeBase : ℕ) (mem : ℕ → ℕ)
    (hedges : ∀ j < m, mem (edgeBase + 4 * j) < n ∧ mem (edgeBase + 4 * j + 1) < n) :
    (edgesOfMem n m edgeBase mem hedges).length = m := by simp [edgesOfMem]

private theorem holdsIndexedEdges_edgesOfMem (n m edgeBase : ℕ) (mem : ℕ → ℕ)
    (hedges : ∀ j < m, mem (edgeBase + 4 * j) < n ∧ mem (edgeBase + 4 * j + 1) < n) :
    HoldsIndexedEdges edgeBase (edgesOfMem n m edgeBase mem hedges) mem := fun _ _ => by
  simp only [edgesOfMem, List.getElem_ofFn]; trivial

private theorem framedTriple_seq_frame {α β : Type} {w : ℕ} {s : Memory.State}
    {p₁ : Memory.Prog α} {p₂ : α → Memory.Prog β} {c₁ c₂ : ℕ} {S₁ S₂ S : Set ℕ}
    {P : α → Memory.State → Prop} {Q : β → Memory.State → Prop}
    (h₁ : Memory.FramedTriple w s p₁ c₁ S₁ P)
    (hsub₁ : S₁ ⊆ S) (hsub₂ : S₂ ⊆ S)
    (h₂ : P ((Memory.spec 0).clientResult s p₁) ((Memory.spec 0).clientState s p₁) →
      Memory.FramedTriple w ((Memory.spec 0).clientState s p₁)
        (p₂ ((Memory.spec 0).clientResult s p₁)) c₂ S₂ Q) :
    Memory.FramedTriple w s (p₁ >>= p₂) (c₁ + c₂) S Q := by
  obtain ⟨hv₁, hc₁, hm₁, hp₁⟩ := framedTriple_iff_realization.mp h₁
  obtain ⟨hv₂, hc₂, hm₂, hq⟩ := framedTriple_iff_realization.mp (h₂ hp₁)
  refine framedTriple_iff_realization.mpr ⟨validHistory_bind_step hv₁ hv₂, ?_, ?_, ?_⟩
  · rw [memoryCost_bind']; omega
  · rw [StateTransitionSpec.clientState_bind]; exact (hm₁.mono hsub₁).trans (hm₂.mono hsub₂)
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]; exact hq

private theorem allocDirty_cr (s : Memory.State) (k : ℕ) :
    (Memory.spec 0).clientResult s (Memory.allocBlockDirty k) = ⟨s.frontier, k⟩ := rfl

private theorem allocDirty_cs (s : Memory.State) (k : ℕ) :
    (Memory.spec 0).clientState s (Memory.allocBlockDirty k) = ⟨s.mem, s.frontier + k⟩ := rfl

private theorem fillConst_fr {w : ℕ} (b v c : ℕ) {s : Memory.State} (hw : Memory.WellFormed w s)
    (hv : Fits w v) (hc : Fits w c) (hle : b + c ≤ s.frontier) :
    ((Memory.spec 0).clientState s (fillConstProg b v c)).frontier = s.frontier :=
  (framedTriple_iff_realization.mp (fillConstProg_spec hw hv hc hle)).2.2.2.1

private theorem holdsIndexedEdges_of_ico {n edgeBase lo hi : ℕ} {es : List (IndexedEdge n)}
    {s s' : Memory.State} (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hmod : Memory.Modifies (Set.Ico lo hi) s s')
    (hlt : edgeBase + 4 * es.length ≤ lo) (hfr : lo ≤ s.frontier) :
    HoldsIndexedEdges edgeBase es s'.mem :=
  hin.congr fun a _ ha => hmod.mem_eq_of_not_mem (by omega) (by simp; omega)

private theorem holdsUndirCSR_of_ico {n offBase adjBase lo hi : ℕ} {es : List (IndexedEdge n)}
    {s s' : Memory.State} (hcsr : HoldsUndirCSR offBase adjBase es s.mem)
    (hmod : Memory.Modifies (Set.Ico lo hi) s s')
    (hoff : offBase + n + 1 ≤ lo) (hadj : adjBase + 4 * es.length ≤ lo) (hfr : lo ≤ s.frontier) :
    HoldsUndirCSR offBase adjBase es s'.mem :=
  hcsr.congr (fun a _ ha => hmod.mem_eq_of_not_mem (by omega) (by simp; omega))
    (fun a _ ha => hmod.mem_eq_of_not_mem (by omega) (by simp; omega))

/-! ## Internal Potential and BFS Steps -/

private noncomputable def ccPot {n : ℕ} (offBase compBase queueBase cid head : ℕ)
    (mem : ℕ → ℕ) : ℕ := ∑ u : Fin n,
    if mem (compBase + u.val) < cid ∨ ∃ i < head, mem (queueBase + i) = u.val then 0
    else 4 + 4 * (mem (offBase + u.val + 1) - mem (offBase + u.val))

private theorem ccPot_zero {n offBase adjBase compBase queueBase : ℕ}
    {es : List (IndexedEdge n)} {mem : ℕ → ℕ}
    (hcsr : HoldsUndirCSR offBase adjBase es mem)
    (hinit : ∀ u : Fin n, mem (compBase + u.val) = n) :
    ccPot (n := n) offBase compBase queueBase 0 0 mem = 4 * n + 8 * es.length := by
  have hsum : ∀ k ≤ n, (∀ j < k, mem (offBase + j) ≤ mem (offBase + j + 1)) →
      mem offBase ≤ mem (offBase + k) ∧
      (∑ i ∈ Finset.range k, (mem (offBase + i + 1) - mem (offBase + i))) =
        mem (offBase + k) - mem offBase := by
    intro k hk hmono
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨h0, hsum_k⟩ := ih (by omega) fun j hj => hmono j (by omega)
      have hk_le := hmono k (Nat.lt_succ_self k)
      rw [Finset.sum_range_succ, hsum_k, show offBase + (k + 1) = offBase + k + 1 by omega]
      exact ⟨by omega, by omega⟩
  have hdeg := (hsum n (le_refl n) fun j hj => hcsr.off_mono ⟨j, hj⟩).2
  rw [← Fin.sum_univ_eq_sum_range (fun i => mem (offBase + i + 1) - mem (offBase + i)) n,
    hcsr.off_zero, hcsr.off_end, Nat.sub_zero] at hdeg
  have hcongr : ccPot (n := n) offBase compBase queueBase 0 0 mem =
      ∑ u : Fin n, (4 + 4 * (mem (offBase + u.val + 1) - mem (offBase + u.val))) :=
    Finset.sum_congr rfl fun u _ => by simp [hinit u]
  rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul,
    ← Finset.mul_sum, hdeg]; omega

private theorem ccPot_step_pop {n offBase compBase queueBase cid head : ℕ}
    {m₁ m₂ : ℕ → ℕ} (u : Fin n) (hoff : ∀ j ≤ n, m₂ (offBase + j) = m₁ (offBase + j))
    (hpop_old : ¬(m₁ (compBase + u.val) < cid ∨ ∃ i < head, m₁ (queueBase + i) = u.val))
    (hpop_new : m₂ (compBase + u.val) < cid ∨ ∃ i < head + 1, m₂ (queueBase + i) = u.val)
    (hother : ∀ x : Fin n, x ≠ u →
      ((m₂ (compBase + x.val) < cid ∨ ∃ i < head + 1, m₂ (queueBase + i) = x.val) ↔
       (m₁ (compBase + x.val) < cid ∨ ∃ i < head, m₁ (queueBase + i) = x.val))) :
    ccPot (n := n) offBase compBase queueBase cid (head + 1) m₂ +
      (4 + 4 * (m₁ (offBase + u.val + 1) - m₁ (offBase + u.val))) =
      ccPot (n := n) offBase compBase queueBase cid head m₁ := by
  dsimp only [ccPot]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
  simp only [hpop_old, ↓reduceIte, hpop_new, zero_add]
  rw [Nat.add_comm (∑ x ∈ Finset.univ.erase u, _)]
  congr 1; refine Finset.sum_congr rfl fun x hx => ?_
  have hne : x ≠ u := (Finset.mem_erase.mp hx).1
  rw [Nat.add_assoc, hoff (x.val + 1) x.isLt, ← Nat.add_assoc, hoff x.val (le_of_lt x.isLt)]
  simp only [hother x hne]

private structure RelaxCfg where
  adjBase : ℕ
  compBase : ℕ
  queueBase : ℕ
  numVertices : ℕ
  cid : ℕ

private word_enc_structure encRelaxCfg : RelaxCfg where
  adjBase : wordWords,
  compBase : wordWords,
  queueBase : wordWords,
  numVertices : wordWords,
  cid : wordWords

private instance : WordEncoding RelaxCfg := ⟨5, encRelaxCfg⟩

private structure BfsPos where
  edgePos : ℕ
  tail : ℕ

private word_enc_structure encBfsPos : BfsPos where
  edgePos : wordWords,
  tail : wordWords

private instance : WordEncoding BfsPos := ⟨2, encBfsPos⟩

private def ccRelaxStep (x : RelaxCfg × BfsPos) : Memory.Prog BfsPos := do
  let cfg := Prod.fst x
  let st := Prod.snd x
  let nb ← Memory.read (cfg.adjBase + 2 * st.edgePos)
  let c ← Memory.read (cfg.compBase + nb)
  if c = cfg.numVertices then
    Memory.write (cfg.compBase + nb) cfg.cid
    Memory.write (cfg.queueBase + st.tail) nb
    pure ⟨st.edgePos + 1, st.tail + 1⟩
  else
    pure ⟨st.edgePos + 1, st.tail⟩

private def ccRelaxStepSafe (w : ℕ) (x : RelaxCfg × BfsPos) (s : Memory.State) : Prop :=
  let cfg := Prod.fst x
  let st := Prod.snd x
  Fits w 16 ∧ Fits w (st.edgePos + 1) ∧ Fits w cfg.cid ∧ Fits w cfg.numVertices ∧
    cfg.adjBase + 2 * st.edgePos < s.frontier ∧
    cfg.compBase + s.mem (cfg.adjBase + 2 * st.edgePos) < s.frontier ∧
    (s.mem (cfg.compBase + s.mem (cfg.adjBase + 2 * st.edgePos)) = cfg.numVertices →
      Fits w (st.tail + 1) ∧ cfg.queueBase + st.tail < s.frontier)

private theorem realizes_ccRelaxStep_history : Realizes .exact
    ccRelaxStep (appendWords encRelaxCfg encBfsPos) encBfsPos
    (fun w d s => ccRelaxStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ccRelaxStep d)))
    (fun _ _ => 0) := by
  unfold ccRelaxStep
  realize
  all_goals
    obtain ⟨⟨h16, hj, hcid, hn, hadj, hcomp, hbr⟩, _⟩ := h
    have hfront := hmem.frontier_fits; have hnb := hmem.mem_fits (d.1.adjBase + 2 * d.2.edgePos)
    first | exact h16.of_le (by decide) | fits

private theorem realizes_ccRelaxStep : Realizes .exact
    ccRelaxStep (appendWords encRelaxCfg encBfsPos) encBfsPos ccRelaxStepSafe (fun _ _ => 0) :=
  realizes_ccRelaxStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private def CompStable (compBase cid : ℕ) {n : ℕ} (s t : Memory.State) : Prop :=
  ∀ x : Fin n, (t.mem (compBase + x.val) < cid ↔ s.mem (compBase + x.val) < cid) ∧
    (s.mem (compBase + x.val) < cid → t.mem (compBase + x.val) = s.mem (compBase + x.val))

private theorem CompStable.refl (compBase cid n : ℕ) (s : Memory.State) :
    CompStable compBase cid (n := n) s s := fun _ => ⟨Iff.rfl, fun _ => rfl⟩

private theorem CompStable.trans {compBase cid n : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : CompStable compBase cid (n := n) s₁ s₂)
    (h₂ : CompStable compBase cid (n := n) s₂ s₃) :
    CompStable compBase cid (n := n) s₁ s₃ := fun x =>
  ⟨(h₂ x).1.trans (h₁ x).1, fun h => ((h₂ x).2 ((h₁ x).1.mpr h)).trans ((h₁ x).2 h)⟩

private structure BfsInv {n : ℕ} (compBase queueBase cid : ℕ)
    (es : List (IndexedEdge n)) (r : Fin n) (q : List (Fin n)) (t : Memory.State) : Prop where
  nd : q.Nodup
  q_mem : ∀ i (hi : i < q.length), t.mem (queueBase + i) = (q[i]'hi).val
  comp_range : ∀ x : Fin n, t.mem (compBase + x.val) = n ∨ t.mem (compBase + x.val) ≤ cid
  comp_cid : ∀ x : Fin n, t.mem (compBase + x.val) = cid ↔ x ∈ q
  q_rel : ∀ x ∈ q, (edgePartition (es.map IndexedEdge.toWeighted)).rel r x = true

private theorem BfsInv.push {n compBase queueBase cid : ℕ} {es : List (IndexedEdge n)}
    {r v : Fin n} {q : List (Fin n)} {t : Memory.State}
    (hb : BfsInv compBase queueBase cid es r q t)
    (hcomp_lt : compBase + n ≤ queueBase) (hcid_lt : cid < n)
    (hv_unvis : t.mem (compBase + v.val) = n)
    (hrel_rv : (edgePartition (es.map IndexedEdge.toWeighted)).rel r v = true) :
    let t' : Memory.State :=
      ⟨Function.update (Function.update t.mem (compBase + v.val) cid) (queueBase + q.length) v.val,
        t.frontier⟩
    v ∉ q ∧ q.length < n ∧ CompStable compBase cid (n := n) t t' ∧
    BfsInv compBase queueBase cid es r (q ++ [v]) t' := by
  have hv_not_q : v ∉ q := fun hvq => by have := (hb.comp_cid v).mpr hvq; omega
  have hq_len : q.length < n := Nat.lt_of_succ_le (by
    simpa only [List.length_cons, Fintype.card_fin] using
      (List.nodup_cons.mpr ⟨hv_not_q, hb.nd⟩).length_le_card)
  let t' : Memory.State :=
    ⟨Function.update (Function.update t.mem (compBase + v.val) cid) (queueBase + q.length) v.val,
      t.frontier⟩
  have hne : ∀ {x : Fin n}, x ≠ v → compBase + x.val ≠ compBase + v.val :=
    fun h hx => h (Fin.ext (by omega))
  have ht_c : ∀ x : Fin n,
      t'.mem (compBase + x.val) = if x = v then cid else t.mem (compBase + x.val) := fun x => by
    dsimp only [t']; split_ifs with hxv
    · subst hxv; update_simp
    · have := hne hxv; update_simp
  refine ⟨hv_not_q, hq_len, fun x => ?_, ⟨List.nodup_append.mpr ⟨hb.nd, List.nodup_singleton v,
      fun a ha b hb' => by
        simp only [List.mem_singleton] at hb'; subst hb'; rintro rfl; exact hv_not_q ha⟩,
    fun i hi => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_⟩⟩
  · rw [ht_c x]; split_ifs with hxv
    · subst hxv; have : ¬t.mem (compBase + x.val) < cid := by omega
      exact ⟨⟨fun h => by omega, fun h => absurd h this⟩, fun h => absurd h this⟩
    · exact ⟨Iff.rfl, fun _ => rfl⟩
  · dsimp only [t']; simp only [List.length_append, List.length_singleton] at hi
    by_cases hi_old : i < q.length
    · rw [List.getElem_append_left hi_old]; update_simp; exact hb.q_mem i hi_old
    · obtain rfl : i = q.length := by omega
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, Function.update_self]
  · rw [ht_c x]; split_ifs <;> [exact .inr (le_refl _); exact hb.comp_range x]
  · rw [ht_c x]; split_ifs with hxv
    · subst hxv; simp
    · simp only [List.mem_append, List.mem_singleton, hxv, or_false]; exact hb.comp_cid x
  · rcases List.mem_append.mp hx with hx | hx
    · exact hb.q_rel x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hrel_rv

private theorem ccRelax_spec {w n offBase adjBase compBase queueBase cid startJ endJ : ℕ}
    {es : List (IndexedEdge n)} {r u : Fin n} {q₀ : List (Fin n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_j : Fits w endJ) (hfit_n1 : Fits w (n + 1))
    (hcsr : HoldsUndirCSR offBase adjBase es s.mem)
    (hoff_lt : offBase + n + 1 ≤ adjBase) (hadj_lt : adjBase + 4 * es.length ≤ compBase)
    (hcomp_lt : compBase + n ≤ queueBase) (hq_lt : queueBase + n ≤ s.frontier) (hcid_lt : cid < n)
    (hslice_start : s.mem (offBase + u.val) = startJ)
    (hslice_end : s.mem (offBase + u.val + 1) = endJ)
    (hb₀ : BfsInv compBase queueBase cid es r q₀ s)
    (hcomp_old : ∀ x : Fin n, s.mem (compBase + x.val) < cid →
      ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true →
        s.mem (compBase + y.val) = s.mem (compBase + x.val))
    (hu_cid : s.mem (compBase + u.val) = cid)
    (hr_rel : (edgePartition (es.map IndexedEdge.toWeighted)).rel r u = true) :
    let cfg : RelaxCfg := ⟨adjBase, compBase, queueBase, n, cid⟩
    let prog := iterate ccRelaxStep cfg (endJ - startJ) ⟨startJ, q₀.length⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    iterationSafe ccRelaxStep ccRelaxStepSafe w cfg (endJ - startJ) ⟨startJ, q₀.length⟩ s ∧
    Memory.FramedTriple w s prog (4 * (endJ - startJ)) (Set.Ico compBase s.frontier)
      (fun _ t => t.frontier = s.frontier ∧ Memory.WellFormed w t) ∧
    res.edgePos = endJ ∧ CompStable compBase cid (n := n) s s' ∧
    (∀ i, i < q₀.length → s'.mem (queueBase + i) = s.mem (queueBase + i)) ∧
    ∃ q₁ : List (Fin n), q₀.Sublist q₁ ∧ res.tail = q₁.length ∧
      BfsInv compBase queueBase cid es r q₁ s' ∧
      (∀ e ∈ es, (e.u = u → e.v ∈ q₁) ∧ (e.v = u → e.u ∈ q₁)) := by
  have hle_slice : startJ ≤ endJ := by rw [← hslice_start, ← hslice_end]; exact hcsr.off_mono u
  have hend_2m : endJ ≤ 2 * es.length := by rw [← hslice_end]; exact hcsr.offset_le_end _ u.isLt
  let cfg : RelaxCfg := ⟨adjBase, compBase, queueBase, n, cid⟩
  let S : Set ℕ := Set.Ico compBase s.frontier
  let inv (k : ℕ) (st : BfsPos) (t : Memory.State) : Prop :=
    t.frontier = s.frontier ∧ Memory.WellFormed w t ∧ (∀ a, a < compBase → t.mem a = s.mem a) ∧
    CompStable compBase cid (n := n) s t ∧
    (∀ i, i < q₀.length → t.mem (queueBase + i) = s.mem (queueBase + i)) ∧
    ∃ q : List (Fin n), st = ⟨startJ + k, q.length⟩ ∧ q₀.Sublist q ∧
      BfsInv compBase queueBase cid es r q t ∧
      (∀ p' < k, ∃ v' : Fin n, t.mem (adjBase + 2 * (startJ + p')) = v'.val ∧ v' ∈ q)
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step ccRelaxStep ccRelaxStepSafe w cfg 4
      (endJ - startJ) inv S (fun k hk st t
        ⟨htfr, hwt, hframe, hold_comp, hold_q, q, hst_eq, hsub, hb, hvis_prev⟩ => by
        subst st
        have hcsr_t : HoldsUndirCSR offBase adjBase es t.mem :=
          hcsr.congr (fun a _ ha => hframe a (by omega)) (fun a _ ha => hframe a (by omega))
        have hs1 : t.mem (offBase + u.val) = startJ := by rw [hframe _ (by omega), hslice_start]
        have hs2 : t.mem (offBase + u.val + 1) = endJ := by rw [hframe _ (by omega), hslice_end]
        have hmem_slice : (t.mem (adjBase + 2 * (startJ + k)),
            t.mem (adjBase + 2 * (startJ + k) + 1)) ∈
            (List.range (t.mem (offBase + u.val + 1) - t.mem (offBase + u.val))).map (fun k' =>
              let p := t.mem (offBase + u.val) + k'
              (t.mem (adjBase + 2 * p), t.mem (adjBase + 2 * p + 1))) :=
          List.mem_map.mpr ⟨k, List.mem_range.mpr (by rw [hs1, hs2]; exact hk), by rw [hs1]⟩
        obtain ⟨eIdx, _, h_uv⟩ := (hcsr_t.mem_slice_iff u _ _).mp hmem_slice
        have hv_lt : t.mem (adjBase + 2 * (startJ + k)) < n := by
          rcases h_uv with ⟨_, hveq⟩ | ⟨_, hueq⟩
          · rw [← hveq]; exact (es[eIdx.val]'eIdx.isLt).v.isLt
          · rw [← hueq]; exact (es[eIdx.val]'eIdx.isLt).u.isLt
        let v : Fin n := ⟨t.mem (adjBase + 2 * (startJ + k)), hv_lt⟩
        have hrel_uv : (edgePartition (es.map IndexedEdge.toWeighted)).rel u v = true := by
          rcases h_uv with ⟨rfl, hveq⟩ | ⟨rfl, hueq⟩
          · rw [show v = (es[eIdx.val]'eIdx.isLt).v from Fin.ext hveq.symm]
            exact rel_of_indexedEdge _ (List.getElem_mem eIdx.isLt)
          · rw [show v = (es[eIdx.val]'eIdx.isLt).u from Fin.ext hueq.symm]
            exact (edgePartition _).symm (rel_of_indexedEdge _ (List.getElem_mem eIdx.isLt))
        have hrel_rv := (edgePartition _).trans hr_rel hrel_uv
        have hq_len_le : q.length ≤ n := by simpa only [Fintype.card_fin] using hb.nd.length_le_card
        have hnb_eq : t.mem (adjBase + 2 * (startJ + k)) = v.val := rfl
        have hu_lt := u.isLt; have hv_isLt := v.isLt
        let stepProg := ccRelaxStep (cfg, ⟨startJ + k, q.length⟩)
        have hsafe : ccRelaxStepSafe w (cfg, ⟨startJ + k, q.length⟩) t := by
          dsimp only [ccRelaxStepSafe, cfg]
          refine ⟨h16, hfit_j.of_le (by omega), hfit_n1.of_le (by omega), hfit_n1.of_le (by omega),
            by rw [htfr]; omega, by rw [htfr]; omega, fun hcv => ?_⟩
          rw [hnb_eq] at hcv
          have hq_lt_n := (hb.push hcomp_lt hcid_lt hcv hrel_rv).2.1
          exact ⟨hfit_n1.of_le (by omega), by rw [htfr]; omega⟩
        have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
          dsimp only [stepProg, ccRelaxStep, cfg]; valid_prog with [htfr, hnb_eq]
          all_goals try dsimp only
          all_goals rw [hnb_eq] at *
          all_goals
            first
            | exact hfit_n1.of_le (by omega)
            | exact (hsafe.2.2.2.2.2.2 (by assumption)).2
            | omega
        have hcost : memoryCost stepProg t ≤ 4 := by
          dsimp only [stepProg, ccRelaxStep, cfg]; prog_cost
        by_cases hcv : t.mem (compBase + v.val) = n
        · obtain ⟨_, _, hcs_step, hb'⟩ := hb.push hcomp_lt hcid_lt hcv hrel_rv
          let t' : Memory.State :=
            ⟨Function.update (Function.update t.mem (compBase + v.val) cid)
              (queueBase + q.length) v.val, t.frontier⟩
          have hst : (Memory.spec 0).clientState t stepProg = t' := by
            dsimp only [stepProg, ccRelaxStep, cfg]
            rw [clientState_bind_read, hnb_eq, clientState_bind_read]
            simp only [hcv, ↓reduceIte]; rfl
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨startJ + k + 1, q.length + 1⟩ := by
            dsimp only [stepProg, ccRelaxStep, cfg]
            rw [clientResult_bind_read, hnb_eq, clientResult_bind_read]
            simp only [hcv, ↓reduceIte, clientResult_bind_write,
              StateTransitionSpec.clientResult_pure]
          have hmod : ∀ a, a ∉ S → t'.mem a = t.mem a := fun a ha => by
            dsimp only [t']; simp only [S, Set.mem_Ico, not_and, not_lt] at ha; update_simp
          have hq₀_le := hsub.length_le
          refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
            ⟨hvh, hcost, ⟨by rw [hst], fun a _ ha => by rw [hst]; exact hmod a ha⟩, ?_⟩⟩
          rw [hst, hres]; refine ⟨htfr, hst ▸ wellFormed_clientState hwt hvh,
            fun a ha => (hmod a (by simp only [S, Set.mem_Ico]; omega)).trans (hframe a ha),
            hold_comp.trans hcs_step,
            fun i hi => by dsimp only [t']; update_simp; exact hold_q i hi,
            q ++ [v], by simp only [List.length_append, List.length_singleton, Nat.add_assoc],
            hsub.trans (List.sublist_append_left q [v]), hb', fun p' hp' => ?_⟩
          dsimp only [t']; by_cases hp : p' = k
          · subst hp
            exact ⟨v, by update_simp, List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))⟩
          · obtain ⟨v', hv', hv'_q⟩ := hvis_prev p' (by omega)
            exact ⟨v', by update_simp; exact hv', List.mem_append.mpr (.inl hv'_q)⟩
        · have hst : (Memory.spec 0).clientState t stepProg = t := by
            dsimp only [stepProg, ccRelaxStep, cfg]
            rw [clientState_bind_read, hnb_eq, clientState_bind_read]
            simp only [hcv, ↓reduceIte]; rfl
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨startJ + k + 1, q.length⟩ := by
            dsimp only [stepProg, ccRelaxStep, cfg]
            rw [clientResult_bind_read, hnb_eq, clientResult_bind_read]
            simp only [hcv, ↓reduceIte, StateTransitionSpec.clientResult_pure]
          refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
            ⟨hvh, hcost, ⟨by rw [hst], fun _ _ _ => by rw [hst]⟩, ?_⟩⟩
          rw [hst, hres]; refine ⟨htfr, hwt, hframe, hold_comp, hold_q, q,
            by simp only [Nat.add_assoc], hsub, hb, fun p' hp' => ?_⟩
          by_cases hp : p' = k
          · subst hp; refine ⟨v, hnb_eq, ?_⟩
            rcases hb.comp_range v with h_n | h_le
            · exact absurd h_n hcv
            · rcases Nat.lt_or_eq_of_le h_le with hlt_cid | h_eq_cid
              · exfalso; have hs_v := (hold_comp v).1.mp hlt_cid
                have := hcomp_old v hs_v u
                  ((edgePartition _).trans ((edgePartition _).symm hrel_rv) hr_rel)
                omega
              · exact (hb.comp_cid v).mp h_eq_cid
          · exact hvis_prev p' (by omega))
      ⟨startJ, q₀.length⟩ s
      ⟨rfl, hwf, fun _ _ => rfl, CompStable.refl _ _ _ _, fun _ _ => rfl,
        q₀, by simp, List.Sublist.refl q₀, hb₀, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hv, hm, hmod, hfr, hwf', _, hold_comp, hold_q, q₁, hst_end, hsub₁, hb₁, hvis₁⟩ :=
    framedTriple_iff_realization.mp hft
  have hcsr' := holdsUndirCSR_of_ico hcsr hmod (by omega) (by omega) (by omega)
  have hs_end : ((Memory.spec 0).clientState s
      (iterate ccRelaxStep cfg (endJ - startJ) ⟨startJ, q₀.length⟩)).mem (offBase + u.val) =
      startJ :=
    (hmod.mem_eq_of_not_mem (by omega) (by simp only [S, Set.mem_Ico]; omega)).trans hslice_start
  have he_end : ((Memory.spec 0).clientState s
      (iterate ccRelaxStep cfg (endJ - startJ) ⟨startJ, q₀.length⟩)).mem (offBase + u.val + 1) =
      endJ :=
    (hmod.mem_eq_of_not_mem (by omega) (by simp only [S, Set.mem_Ico]; omega)).trans hslice_end
  refine ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, hm, hmod, hfr, hwf'⟩,
    by rw [hst_end]; dsimp only; omega, hold_comp, hold_q, q₁, hsub₁, by rw [hst_end], hb₁,
    fun e he => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have hmem_v : ∀ (w' : Fin n) (k : ℕ), k < endJ - startJ →
      ((Memory.spec 0).clientState s (iterate ccRelaxStep cfg (endJ - startJ)
        ⟨startJ, q₀.length⟩)).mem (adjBase + 2 * (startJ + k)) = w'.val → w' ∈ q₁ :=
    fun w' k hk h =>
      let ⟨v', hv', hv'_q⟩ := hvis₁ k hk; (Fin.ext (hv'.symm.trans h) : v' = w') ▸ hv'_q
  exact ⟨fun heu => by
    obtain ⟨k, hk, hp⟩ := List.mem_map.mp
      ((hcsr'.mem_slice_iff u (es[i]'hi).v.val i).mpr ⟨⟨i, hi⟩, rfl, .inl ⟨heu, rfl⟩⟩)
    rw [List.mem_range, hs_end, he_end] at hk; rw [hs_end] at hp
    exact hmem_v _ k hk (congrArg Prod.fst hp), fun hev => by
    obtain ⟨k, hk, hp⟩ := List.mem_map.mp
      ((hcsr'.mem_slice_iff u (es[i]'hi).u.val i).mpr ⟨⟨i, hi⟩, rfl, .inr ⟨hev, rfl⟩⟩)
    rw [List.mem_range, hs_end, he_end] at hk; rw [hs_end] at hp
    exact hmem_v _ k hk (congrArg Prod.fst hp)⟩

private structure BfsCfg where
  offBase : ℕ
  adjBase : ℕ
  compBase : ℕ
  queueBase : ℕ
  numVertices : ℕ
  cid : ℕ

private word_enc_structure encBfsCfg : BfsCfg where
  offBase : wordWords,
  adjBase : wordWords,
  compBase : wordWords,
  queueBase : wordWords,
  numVertices : wordWords,
  cid : wordWords

private instance : WordEncoding BfsCfg := ⟨6, encBfsCfg⟩

private def ccBfsStep (x : BfsCfg × BfsPos) : Memory.Prog BfsPos := do
  let cfg := Prod.fst x
  let st := Prod.snd x
  let u ← Memory.read (cfg.queueBase + st.edgePos)
  let sJ ← Memory.read (cfg.offBase + u)
  let eJ ← Memory.read (cfg.offBase + u + 1)
  let res ← iterate ccRelaxStep
    ⟨cfg.adjBase, cfg.compBase, cfg.queueBase, cfg.numVertices, cfg.cid⟩ (eJ - sJ) ⟨sJ, st.tail⟩
  pure ⟨st.edgePos + 1, res.tail⟩

private def ccBfsStepSafe (w : ℕ) (x : BfsCfg × BfsPos) (s : Memory.State) : Prop :=
  let cfg := Prod.fst x
  let st := Prod.snd x
  let u := s.mem (cfg.queueBase + st.edgePos)
  let sJ := s.mem (cfg.offBase + u)
  let eJ := s.mem (cfg.offBase + u + 1)
  Fits w 16 ∧ Fits w (st.edgePos + 1) ∧
    cfg.queueBase + st.edgePos < s.frontier ∧
    cfg.offBase + u + 1 < s.frontier ∧
    sJ ≤ eJ ∧
    iterationSafe ccRelaxStep ccRelaxStepSafe w
      ⟨cfg.adjBase, cfg.compBase, cfg.queueBase, cfg.numVertices, cfg.cid⟩
      (eJ - sJ) ⟨sJ, st.tail⟩ s

private theorem realizes_ccBfsStep_history : Realizes .exact
    ccBfsStep (appendWords encBfsCfg encBfsPos) encBfsPos
    (fun w d s => ccBfsStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ccBfsStep d)))
    (fun _ _ => 0) := by
  unfold ccBfsStep
  realize [realizes_ccRelaxStep]
  all_goals
    obtain ⟨⟨h16, hh, hq, ho, hle, hsafe⟩, _⟩ := h; have hfront := hmem.frontier_fits
    first | fits | exact hle | exact iterationSafe_imp hsafe (fun _ => rfl) (fun _ _ hs => hs)

private theorem realizes_ccBfsStep : Realizes .exact
    ccBfsStep (appendWords encBfsCfg encBfsPos) encBfsPos ccBfsStepSafe (fun _ _ => 0) :=
  realizes_ccBfsStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem ccBfsStep_spec {w n offBase adjBase compBase queueBase cid head : ℕ}
    {es : List (IndexedEdge n)} {r : Fin n} {q₀ : List (Fin n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_n1 : Fits w (n + 1)) (hfit_2m1 : Fits w (2 * es.length + 1))
    (hcsr : HoldsUndirCSR offBase adjBase es s.mem) (hoff_lt : offBase + n + 1 ≤ adjBase)
    (hadj_lt : adjBase + 4 * es.length ≤ compBase) (hcomp_lt : compBase + n ≤ queueBase)
    (hq_lt : queueBase + n ≤ s.frontier) (hcid_lt : cid < n)
    (hb₀ : BfsInv compBase queueBase cid es r q₀ s) (hhead_lt : head < q₀.length)
    (hcomp_old : ∀ x : Fin n, s.mem (compBase + x.val) < cid →
      ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true →
        s.mem (compBase + y.val) = s.mem (compBase + x.val)) :
    let cfg : BfsCfg := ⟨offBase, adjBase, compBase, queueBase, n, cid⟩
    let prog := ccBfsStep (cfg, ⟨head, q₀.length⟩)
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ccBfsStepSafe w (cfg, ⟨head, q₀.length⟩) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s + ccPot (n := n) offBase compBase queueBase cid (head + 1) s'.mem ≤
      ccPot (n := n) offBase compBase queueBase cid head s.mem ∧
    res.edgePos = head + 1 ∧ Memory.Modifies (Set.Ico compBase s.frontier) s s' ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧ CompStable compBase cid (n := n) s s' ∧
    (∀ i, i < q₀.length → s'.mem (queueBase + i) = s.mem (queueBase + i)) ∧
    ∃ q₁ : List (Fin n), q₀.Sublist q₁ ∧ res.tail = q₁.length ∧
      BfsInv compBase queueBase cid es r q₁ s' ∧
      (∀ e ∈ es, (e.u = q₀[head]'hhead_lt → e.v ∈ q₁) ∧
        (e.v = q₀[head]'hhead_lt → e.u ∈ q₁)) := by
  let u := q₀[head]'hhead_lt
  let startJ := s.mem (offBase + u.val); let endJ := s.mem (offBase + u.val + 1)
  have hu_mem : s.mem (queueBase + head) = u.val := hb₀.q_mem head hhead_lt
  have hq_len_le : q₀.length ≤ n := by simpa only [Fintype.card_fin] using hb₀.nd.length_le_card
  have hle_slice : startJ ≤ endJ := hcsr.off_mono u
  have hend_le : endJ ≤ 2 * es.length := hcsr.offset_le_end (u.val + 1) u.isLt
  have hu_cid : s.mem (compBase + u.val) = cid := (hb₀.comp_cid u).mpr (List.getElem_mem hhead_lt)
  obtain ⟨hsafe_it, hft_it, _, hold_comp, hold_q, q₁, hsub₁, hlen₁, hb₁, hneigh₁⟩ :=
    @ccRelax_spec w n offBase adjBase compBase queueBase cid startJ endJ es r u q₀ s h16 hwf
      (hfit_2m1.of_le (by omega)) hfit_n1 hcsr hoff_lt hadj_lt hcomp_lt hq_lt hcid_lt rfl rfl hb₀
      hcomp_old hu_cid (hb₀.q_rel u (List.getElem_mem hhead_lt))
  obtain ⟨hv_it, hm_it, hmod_it, hfr_it, hwf'⟩ := framedTriple_iff_realization.mp hft_it
  set itProg := iterate ccRelaxStep ⟨adjBase, compBase, queueBase, n, cid⟩ (endJ - startJ)
    ⟨startJ, q₀.length⟩
  set s' := (Memory.spec 0).clientState s itProg
  let cfg : BfsCfg := ⟨offBase, adjBase, compBase, queueBase, n, cid⟩
  have hprog : ccBfsStep (cfg, ⟨head, q₀.length⟩) =
      (Memory.read (queueBase + head) >>= fun u' => Memory.read (offBase + u') >>= fun sJ =>
        Memory.read (offBase + u' + 1) >>= fun eJ => iterate ccRelaxStep
          ⟨adjBase, compBase, queueBase, n, cid⟩ (eJ - sJ) ⟨sJ, q₀.length⟩ >>= fun st =>
            pure ⟨head + 1, st.tail⟩) := rfl
  let stepProg := ccBfsStep (cfg, ⟨head, q₀.length⟩)
  have hu_lt := u.isLt
  have hsafe : ccBfsStepSafe w (cfg, ⟨head, q₀.length⟩) s := by
    dsimp only [ccBfsStepSafe, cfg]
    refine ⟨h16, hfit_n1.of_le (by omega), by omega, by rw [hu_mem]; omega,
      by rw [hu_mem]; exact hle_slice, by simpa only [hu_mem] using hsafe_it⟩
  have hvh : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s stepProg) := by
    dsimp only [stepProg]; rw [hprog]; refine validHistory_read_bind (by omega) ?_; rw [hu_mem]
    exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_bind_step hv_it (validHistory_pure w _ _)))
  have hst : (Memory.spec 0).clientState s stepProg = s' := by
    dsimp only [stepProg]; rw [hprog, clientState_bind_read, hu_mem, clientState_bind_read,
      clientState_bind_read, StateTransitionSpec.clientState_bind]; rfl
  have hres : (Memory.spec 0).clientResult s stepProg = ⟨head + 1, q₁.length⟩ := by
    dsimp only [stepProg]; rw [hprog, clientResult_bind_read, hu_mem, clientResult_bind_read,
      clientResult_bind_read, StateTransitionSpec.clientResult_bind, hlen₁]; rfl
  have hcost : memoryCost stepProg s ≤ 3 + 4 * (endJ - startJ) := by
    dsimp only [stepProg]
    rw [hprog, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hu_mem,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, memoryCost_bind',
      memoryCost_read, clientResult_read, clientState_read, memoryCost_bind', memoryCost_pure,
      add_zero]; change 1 + (1 + (1 + memoryCost itProg s)) ≤ _; omega
  have hpop_old : ¬(s.mem (compBase + u.val) < cid ∨
      ∃ i < head, s.mem (queueBase + i) = u.val) := by
    rintro (hlt | ⟨i, hi_lt, hi_eq⟩)
    · omega
    · have := hb₀.nd.getElem_inj_iff.mp (Fin.ext ((hb₀.q_mem i (by omega)).symm.trans hi_eq))
      omega
  have hother : ∀ x : Fin n, x ≠ u →
      ((s'.mem (compBase + x.val) < cid ∨ ∃ i < head + 1, s'.mem (queueBase + i) = x.val) ↔
       (s.mem (compBase + x.val) < cid ∨ ∃ i < head, s.mem (queueBase + i) = x.val)) := by
    intro x hne; rw [(hold_comp x).1]; refine ⟨?_, ?_⟩
    · rintro (h | ⟨i, hi, heq⟩)
      · exact .inl h
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hilt | rfl
        · exact .inr ⟨i, hilt, (hold_q i (by omega)).symm.trans heq⟩
        · exact absurd (Fin.ext (heq.symm.trans ((hold_q i (by omega)).trans hu_mem))) hne
    · exact fun h => h.elim .inl fun ⟨i, hi, heq⟩ =>
        .inr ⟨i, by omega, (hold_q i (by omega)).trans heq⟩
  have hpot := ccPot_step_pop (offBase := offBase) u
    (fun j hj => hmod_it.mem_eq_of_not_mem (by omega)
      (by simp only [Set.mem_Ico, not_and, not_lt]; omega))
    hpop_old (.inr ⟨head, Nat.lt_succ_self head, (hold_q head hhead_lt).trans hu_mem⟩) hother
  refine ⟨hsafe, hvh, ?_, by rw [hres], by rw [hst]; exact hmod_it, by rw [hst]; exact hfr_it,
    by rw [hst]; exact hwf', fun x => by rw [hst]; exact hold_comp x,
    fun i hi => by rw [hst]; exact hold_q i hi, q₁, hsub₁, by rw [hres], by rw [hst]; exact hb₁,
    hneigh₁⟩
  rw [hst]; dsimp only [startJ, endJ, itProg, stepProg, cfg] at hcost hpot ⊢; omega

private theorem ccBfs_spec {w n offBase adjBase compBase queueBase cid : ℕ}
    {es : List (IndexedEdge n)} {r : Fin n} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_n1 : Fits w (n + 1)) (hfit_2m1 : Fits w (2 * es.length + 1))
    (hcsr : HoldsUndirCSR offBase adjBase es s.mem) (hoff_lt : offBase + n + 1 ≤ adjBase)
    (hadj_lt : adjBase + 4 * es.length ≤ compBase) (hcomp_lt : compBase + n ≤ queueBase)
    (hq_lt : queueBase + n ≤ s.frontier) (hcid_lt : cid < n)
    (hcomp_range : ∀ x : Fin n, s.mem (compBase + x.val) = n ∨ s.mem (compBase + x.val) < cid)
    (hcomp_old : ∀ x : Fin n, s.mem (compBase + x.val) < cid →
      ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true →
        s.mem (compBase + y.val) = s.mem (compBase + x.val))
    (hr_unvis : s.mem (compBase + r.val) = n) :
    let mem₁ := Function.update s.mem (compBase + r.val) cid
    let s₀ : Memory.State := ⟨Function.update mem₁ queueBase r.val, s.frontier⟩
    let cfg : BfsCfg := ⟨offBase, adjBase, compBase, queueBase, n, cid⟩
    let prog := boundedWhile (fun (_ : BfsCfg) (st : BfsPos) => st.edgePos < st.tail)
      ccBfsStep cfg n ⟨0, 1⟩
    let s' := (Memory.spec 0).clientState s₀ prog
    whileSafe (fun (_ : BfsCfg) (st : BfsPos) => st.edgePos < st.tail)
      ccBfsStep ccBfsStepSafe w cfg n ⟨0, 1⟩ s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    Memory.Modifies (Set.Ico compBase s.frontier) s₀ s' ∧
    s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
    memoryCost prog s₀ + ccPot (n := n) offBase compBase queueBase (cid + 1) 0 s'.mem ≤
      ccPot (n := n) offBase compBase queueBase cid 0 s.mem ∧
    CompStable compBase cid (n := n) s s' ∧
    (∀ x : Fin n, s'.mem (compBase + x.val) = n ∨ s'.mem (compBase + x.val) < cid + 1) ∧
    (∀ y : Fin n, s'.mem (compBase + y.val) = cid ↔
      (edgePartition (es.map IndexedEdge.toWeighted)).rel r y = true) := by
  let mem₁ := Function.update s.mem (compBase + r.val) cid
  let s₀ : Memory.State := ⟨Function.update mem₁ queueBase r.val, s.frontier⟩
  let cfg : BfsCfg := ⟨offBase, adjBase, compBase, queueBase, n, cid⟩
  let S : Set ℕ := Set.Ico compBase s.frontier
  have hbf_s : BfsInv compBase queueBase cid es r [] s :=
    ⟨List.nodup_nil, fun _ h => absurd h (Nat.not_lt_zero _),
      fun x => (hcomp_range x).elim .inl (fun h => .inr h.le),
      fun x => ⟨fun heq => by rcases hcomp_range x with h | h <;> omega,
        fun h => absurd h List.not_mem_nil⟩, fun _ h => absurd h List.not_mem_nil⟩
  obtain ⟨_, _, hs₀_hold, hbf₀⟩ := hbf_s.push hcomp_lt hcid_lt hr_unvis ((edgePartition _).refl r)
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hwf.frontier_fits, fun a => by
    dsimp only [s₀, mem₁]; rw [Function.update_apply, Function.update_apply]
    split_ifs <;> first | exact hfit_n1.of_le (by omega) | exact hwf.mem_fits a⟩
  have hs₀_frame : ∀ a, a < compBase → s₀.mem a = s.mem a := fun a ha => by
    dsimp only [s₀, mem₁]; have := r.isLt
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  let inv (st : BfsPos) (t : Memory.State) : Prop :=
    t.frontier = s.frontier ∧ Memory.WellFormed w t ∧ (∀ a, a < compBase → t.mem a = s.mem a) ∧
    CompStable compBase cid (n := n) s t ∧
    ∃ q : List (Fin n), st.tail = q.length ∧ st.edgePos ≤ q.length ∧ 0 < q.length ∧
      BfsInv compBase queueBase cid es r q t ∧ r ∈ q ∧
      ∀ i (hi : i < st.edgePos) (hiq : i < q.length), ∀ e ∈ es,
        (e.u = q[i]'hiq → e.v ∈ q) ∧ (e.v = q[i]'hiq → e.u ∈ q)
  let rank (st : BfsPos) (_ : Memory.State) : ℕ := n - st.edgePos
  let pot (st : BfsPos) (t : Memory.State) : ℕ :=
    ccPot (n := n) offBase compBase queueBase cid st.edgePos t.mem
  have hzero : ∀ st t, inv st t → rank st t = 0 → ¬(st.edgePos < st.tail) := by
    rintro st t ⟨_, _, _, _, q, hlen, _, _, hb, _⟩ hr0
    have := (by simpa only [Fintype.card_fin] using hb.nd.length_le_card : q.length ≤ n)
    dsimp only [rank] at hr0; omega
  have hinv0 : inv ⟨0, 1⟩ s₀ := ⟨rfl, hwf₀, hs₀_frame, hs₀_hold, [r], rfl, Nat.zero_le 1,
    Nat.one_pos, hbf₀, List.mem_singleton.mpr rfl, fun _ h _ => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hv, hstop, inv_end, hmod, hcost_pot⟩ :=
    boundedWhile_potential_spec (fun (_ : BfsCfg) (st : BfsPos) => st.edgePos < st.tail)
      ccBfsStep ccBfsStepSafe w cfg 0 inv rank pot S hzero
      (fun ⟨head, tail⟩ t ⟨htfr, hwt, hframe, hold, q, hlen, hle, hpos, hb, hr_q, hneigh⟩ hg => by
        dsimp only at hlen hle hg hneigh; subst tail
        have hcsr_t : HoldsUndirCSR offBase adjBase es t.mem :=
          hcsr.congr (fun a _ ha => hframe a (by omega)) (fun a _ ha => hframe a (by omega))
        have hcomp_old_t : ∀ x : Fin n, t.mem (compBase + x.val) < cid →
            ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true →
              t.mem (compBase + y.val) = t.mem (compBase + x.val) := fun x hx y hxy => by
          have hxs := (hold x).1.mp hx; have hys := hcomp_old x hxs y hxy
          rw [(hold x).2 hxs, (hold y).2 (by omega), hys]
        obtain ⟨hsafe, hvh, hcost_pot, hres1, hmod', hfr', hwt', hold', hold_q',
            q', hsub', hres2, hb', hneigh_u⟩ :=
          @ccBfsStep_spec w n offBase adjBase compBase queueBase cid head es r q t
            h16 hwt hfit_n1 hfit_2m1 hcsr_t hoff_lt hadj_lt hcomp_lt (by rw [htfr]; exact hq_lt)
            hcid_lt hb hg hcomp_old_t
        have hmod_S : Memory.Modifies S t ((Memory.spec 0).clientState t
            (ccBfsStep (cfg, ⟨head, q.length⟩))) := by rwa [htfr] at hmod'
        have hq_le : q.length ≤ n := by simpa only [Fintype.card_fin] using hb.nd.length_le_card
        refine ⟨hsafe, hvh, by dsimp only [pot]; rw [hres1]; exact hcost_pot, hmod_S,
          ⟨hfr'.trans htfr, hwt', fun a ha => (hmod_S.mem_eq_of_not_mem (by rw [htfr]; omega)
              (by simp only [S, Set.mem_Ico, not_and, not_lt]; omega)).trans (hframe a ha),
            hold.trans hold', q', hres2, by rw [hres1]; have := hsub'.length_le; omega,
            lt_of_lt_of_le hpos hsub'.length_le, hb', hsub'.subset hr_q, fun i hi hiq' => ?_⟩,
          by dsimp only [rank]; rw [hres1]; omega⟩
        rw [hres1] at hi; by_cases hi_old : i < head
        · have hi_q : i < q.length := by omega
          have hqi : q'[i]'hiq' = q[i]'hi_q :=
            Fin.ext ((hb'.q_mem i hiq').symm.trans ((hold_q' i hi_q).trans (hb.q_mem i hi_q)))
          intro e he; rw [hqi]
          exact ⟨fun hu => hsub'.subset ((hneigh i hi_old hi_q e he).1 hu),
            fun hv => hsub'.subset ((hneigh i hi_old hi_q e he).2 hv)⟩
        · have hi_eq : i = head := by omega
          have hqh : q'[i]'hiq' = q[head]'hg :=
            Fin.ext (by rw [← hb'.q_mem i hiq', hi_eq, hold_q' head hg, hb.q_mem head hg])
          intro e he; rw [hqh]; exact hneigh_u e he)
      n ⟨0, 1⟩ s₀ hinv0 (by dsimp only [rank]; omega)
  rcases inv_end with ⟨hfr, hwf', _, hold', q₁, hlen', hle', _, hb₁, hr_q₁, hneigh'⟩
  set bwP := boundedWhile (fun (_ : BfsCfg) (st : BfsPos) => st.edgePos < st.tail)
    ccBfsStep cfg n ⟨0, 1⟩
  set s' := (Memory.spec 0).clientState s₀ bwP; set res := (Memory.spec 0).clientResult s₀ bwP
  have hhead_eq : res.edgePos = q₁.length := by have : ¬(res.edgePos < res.tail) := hstop; omega
  have hclosed : ∀ e ∈ es, e.u ∈ q₁ ↔ e.v ∈ q₁ := fun e he =>
    ⟨fun heu => let ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp heu
      (hneigh' i (hhead_eq ▸ hi) hi e he).1 hqi.symm,
     fun hev => let ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hev
      (hneigh' i (hhead_eq ▸ hi) hi e he).2 hqi.symm⟩
  have hpot_init : pot ⟨0, 1⟩ s₀ = ccPot (n := n) offBase compBase queueBase cid 0 s.mem :=
    Finset.sum_congr rfl fun x _ => by
      dsimp only [pot, ccPot]
      have h0 : s₀.mem (compBase + x.val) < cid ↔ s.mem (compBase + x.val) < cid := (hs₀_hold x).1
      simp only [Nat.not_lt_zero, false_and, exists_false, or_false, h0,
        hs₀_frame _ (by omega : offBase + x.val < compBase),
        hs₀_frame _ (by omega : offBase + x.val + 1 < compBase)]
  have hpot_end : ccPot (n := n) offBase compBase queueBase (cid + 1) 0 s'.mem = pot res s' :=
    Finset.sum_congr rfl fun x _ => by
      have hpop_iff : (s'.mem (compBase + x.val) < cid + 1) ↔
          (s'.mem (compBase + x.val) < cid ∨ ∃ i < res.edgePos, s'.mem (queueBase + i) = x.val) :=
        ⟨fun hlt => (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt)).elim .inl fun heq =>
            let ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp ((hb₁.comp_cid x).mp heq)
            .inr ⟨i, hhead_eq ▸ hi, (hb₁.q_mem i hi).trans (congrArg Fin.val hqi)⟩,
         by rintro (hlt | ⟨i, hi, heq⟩)
            · omega
            · have hi_q : i < q₁.length := hhead_eq ▸ hi
              have := (hb₁.comp_cid x).mpr ((Fin.ext (heq.symm.trans (hb₁.q_mem i hi_q)) :
                x = q₁[i]'hi_q) ▸ List.getElem_mem hi_q); omega⟩
      simp only [Nat.not_lt_zero, false_and, exists_false, or_false, hpop_iff]
  refine ⟨hsafe, hv, hmod, hfr, hwf', ?_, hold',
    fun x => (hb₁.comp_range x).elim .inl (fun h => .inr (Nat.lt_succ_of_le h)),
    fun y => by rw [hb₁.comp_cid y]; exact ⟨fun hy => hb₁.q_rel y hy,
      fun hrel => (closed_of_edgePartition_rel es (· ∈ q₁) hclosed hrel).mp hr_q₁⟩⟩
  dsimp only [pot] at hcost_pot hpot_init hpot_end; rw [hpot_end, ← hpot_init]
  dsimp only [cfg, s₀, mem₁] at hcost_pot ⊢; simpa only [zero_mul, add_zero] using hcost_pot

private structure OuterCfg where
  offBase : ℕ
  adjBase : ℕ
  compBase : ℕ
  queueBase : ℕ
  numVertices : ℕ

private word_enc_structure encOuterCfg : OuterCfg where
  offBase : wordWords,
  adjBase : wordWords,
  compBase : wordWords,
  queueBase : wordWords,
  numVertices : wordWords

private instance : WordEncoding OuterCfg := ⟨5, encOuterCfg⟩

private structure OuterPos where
  v : ℕ
  cid : ℕ

private word_enc_structure encOuterPos : OuterPos where
  v : wordWords,
  cid : wordWords

private instance : WordEncoding OuterPos := ⟨2, encOuterPos⟩

private def ccOuterStep (x : OuterCfg × OuterPos) : Memory.Prog OuterPos := do
  let cfg := Prod.fst x
  let st := Prod.snd x
  let c ← Memory.read (cfg.compBase + st.v)
  if c = cfg.numVertices then
    Memory.write (cfg.compBase + st.v) st.cid
    Memory.write cfg.queueBase st.v
    let _ ← boundedWhile (fun (_ : BfsCfg) (b : BfsPos) => b.edgePos < b.tail)
      ccBfsStep ⟨cfg.offBase, cfg.adjBase, cfg.compBase, cfg.queueBase, cfg.numVertices, st.cid⟩
      cfg.numVertices ⟨0, 1⟩
    pure ⟨st.v + 1, st.cid + 1⟩
  else
    pure ⟨st.v + 1, st.cid⟩

private def ccOuterStepSafe (w : ℕ) (x : OuterCfg × OuterPos) (s : Memory.State) : Prop :=
  let cfg := Prod.fst x
  let st := Prod.snd x
  Fits w 16 ∧ Fits w (st.v + 1) ∧ Fits w (st.cid + 1) ∧
    cfg.compBase + st.v < s.frontier ∧
    (s.mem (cfg.compBase + st.v) = cfg.numVertices →
      cfg.queueBase < s.frontier ∧
      whileSafe (fun (_ : BfsCfg) (b : BfsPos) => b.edgePos < b.tail)
        ccBfsStep ccBfsStepSafe w
        ⟨cfg.offBase, cfg.adjBase, cfg.compBase, cfg.queueBase, cfg.numVertices, st.cid⟩
        cfg.numVertices ⟨0, 1⟩
        ⟨Function.update (Function.update s.mem (cfg.compBase + st.v) st.cid)
          cfg.queueBase st.v, s.frontier⟩)

private theorem realizes_ccOuterStep_history : Realizes .exact
    ccOuterStep (appendWords encOuterCfg encOuterPos) encOuterPos
    (fun w d s => ccOuterStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ccOuterStep d)))
    (fun _ _ => 0) := by
  unfold ccOuterStep
  realize [realizes_ccBfsStep]
  all_goals
    obtain ⟨⟨h16, hv, hcid, hlt, hbr⟩, _⟩ := h; have hfront := hmem.frontier_fits
    first
    | exact h16.of_le (by decide)
    | fits
    | exact fun _ => whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl)
        (fun _ _ _ hs => by dsimp only; exact hs) (hbr hc).2

private theorem realizes_ccOuterStep : Realizes .exact
    ccOuterStep (appendWords encOuterCfg encOuterPos) encOuterPos ccOuterStepSafe (fun _ _ => 0) :=
  realizes_ccOuterStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem ccOuter_spec {w n offBase adjBase compBase queueBase : ℕ}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_n1 : Fits w (n + 1)) (hfit_2m1 : Fits w (2 * es.length + 1))
    (hcsr : HoldsUndirCSR offBase adjBase es s.mem) (hoff_lt : offBase + n + 1 ≤ adjBase)
    (hadj_lt : adjBase + 4 * es.length ≤ compBase) (hcomp_lt : compBase + n ≤ queueBase)
    (hq_lt : queueBase + n ≤ s.frontier) (hinit : ∀ x : Fin n, s.mem (compBase + x.val) = n) :
    let cfg : OuterCfg := ⟨offBase, adjBase, compBase, queueBase, n⟩
    let prog := iterate ccOuterStep cfg n ⟨0, 0⟩
    iterationSafe ccOuterStep ccOuterStepSafe w cfg n ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s prog (7 * n + 8 * es.length) (Set.Ico compBase s.frontier)
      (fun res s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        res.v = n ∧ res.cid ≤ n ∧
        (∀ x : Fin n, s'.mem (compBase + x.val) < res.cid) ∧
        (∀ c < res.cid, ∃ x : Fin n, s'.mem (compBase + x.val) = c) ∧
        ∀ x y : Fin n, s'.mem (compBase + x.val) = s'.mem (compBase + y.val) ↔
          (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true) := by
  let cfg : OuterCfg := ⟨offBase, adjBase, compBase, queueBase, n⟩
  let S : Set ℕ := Set.Ico compBase s.frontier
  let pot (_ : ℕ) (st : OuterPos) (t : Memory.State) : ℕ :=
    ccPot (n := n) offBase compBase queueBase st.cid 0 t.mem
  let inv (k : ℕ) (st : OuterPos) (t : Memory.State) : Prop :=
    t.frontier = s.frontier ∧ Memory.WellFormed w t ∧ (∀ a, a < compBase → t.mem a = s.mem a) ∧
    ∃ cid : ℕ, st = ⟨k, cid⟩ ∧ cid ≤ k ∧
      (∀ x : Fin n, t.mem (compBase + x.val) = n ∨ t.mem (compBase + x.val) < cid) ∧
      (∀ x : Fin n, x.val < k → t.mem (compBase + x.val) < cid) ∧
      (∀ c < cid, ∃ x : Fin n, t.mem (compBase + x.val) = c) ∧
      ∀ x : Fin n, t.mem (compBase + x.val) < cid →
        ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true ↔
          t.mem (compBase + y.val) = t.mem (compBase + x.val)
  obtain ⟨hsafe, hv, hm_pot, hmod, hfr, hwf', _, cid, hres_eq, hcid_le, _, hvis_all, hsurj_all,
      hconn_all⟩ := iterate_potential_spec ccOuterStep ccOuterStepSafe w cfg 3 n inv pot S
      (fun k hk st t ⟨htfr, hwt, hframe, cid, hst_eq, hcid_le, hcr, hvis, hsurj, hconn⟩ => by
        subst st
        have hcsr_t : HoldsUndirCSR offBase adjBase es t.mem :=
          hcsr.congr (fun a _ ha => hframe a (by omega)) (fun a _ ha => hframe a (by omega))
        have hconn' : ∀ x : Fin n, t.mem (compBase + x.val) < cid →
            ∀ y : Fin n, (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true →
              t.mem (compBase + y.val) = t.mem (compBase + x.val) := fun x hx y hxy =>
          (hconn x hx y).mp hxy
        have hprog : ccOuterStep (cfg, ⟨k, cid⟩) =
            (Memory.read (compBase + k) >>= fun c => if c = n then
                Memory.write (compBase + k) cid >>= fun _ => Memory.write queueBase k >>= fun _ =>
                  boundedWhile (fun (_ : BfsCfg) (b : BfsPos) => b.edgePos < b.tail) ccBfsStep
                    ⟨offBase, adjBase, compBase, queueBase, n, cid⟩ n ⟨0, 1⟩ >>= fun _ =>
                      pure ⟨k + 1, cid + 1⟩ else pure ⟨k + 1, cid⟩) := rfl
        let stepProg := ccOuterStep (cfg, ⟨k, cid⟩)
        by_cases hcv : t.mem (compBase + k) = n
        · let r : Fin n := ⟨k, hk⟩
          obtain ⟨hsafe_bw, hv_bw, hmod_bw, hfr_bw, hwf', hm_pot, hold_bw, hcr', hrel'⟩ :=
            @ccBfs_spec w n offBase adjBase compBase queueBase cid es r t h16 hwt hfit_n1 hfit_2m1
              hcsr_t hoff_lt hadj_lt hcomp_lt (by rw [htfr]; exact hq_lt) (by omega) hcr hconn' hcv
          let mem₁ := Function.update t.mem (compBase + k) cid
          let s₀ : Memory.State := ⟨Function.update mem₁ queueBase k, t.frontier⟩
          let bwProg := boundedWhile (fun (_ : BfsCfg) (b : BfsPos) => b.edgePos < b.tail)
            ccBfsStep ⟨offBase, adjBase, compBase, queueBase, n, cid⟩ n ⟨0, 1⟩
          have hmod_step : Memory.Modifies S t ((Memory.spec 0).clientState s₀ bwProg) := by
            have hmod0 : Memory.Modifies S t s₀ := ⟨le_rfl, fun a _ ha => by
              dsimp only [s₀, mem₁]; simp only [S, Set.mem_Ico, not_and, not_lt] at ha; update_simp⟩
            exact hmod0.trans (by
              dsimp only [s₀, mem₁, r]; rw [htfr] at hmod_bw ⊢; exact hmod_bw)
          have hsafe : ccOuterStepSafe w (cfg, ⟨k, cid⟩) t := by
            dsimp only [ccOuterStepSafe, cfg]
            exact ⟨h16, hfit_n1.of_le (by omega), hfit_n1.of_le (by omega), by rw [htfr]; omega,
              fun _ => ⟨by rw [htfr]; omega, hsafe_bw⟩⟩
          have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
            dsimp only [stepProg]; rw [hprog]
            refine validHistory_read_bind (by rw [htfr]; omega) ?_
            simp only [hcv, ↓reduceIte]
            exact validHistory_write_bind (by rw [htfr]; omega) (hfit_n1.of_le (by omega))
              (validHistory_write_bind (by rw [htfr]; omega) (hfit_n1.of_le (by omega))
                (validHistory_bind_step hv_bw (validHistory_pure w _ _)))
          have hst : (Memory.spec 0).clientState t stepProg =
              (Memory.spec 0).clientState s₀ bwProg := by
            dsimp only [stepProg]; rw [hprog, clientState_bind_read]; simp only [hcv, ↓reduceIte]
            rw [clientState_bind_write, clientState_bind_write,
              StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨k + 1, cid + 1⟩ := by
            dsimp only [stepProg]; rw [hprog, clientResult_bind_read]
            simp only [hcv, ↓reduceIte, StateTransitionSpec.clientResult_bind,
              StateTransitionSpec.clientResult_pure]
          have hcost : memoryCost stepProg t ≤ 3 + memoryCost bwProg s₀ := by
            dsimp only [stepProg]; rw [hprog]; prog_cost
            change 1 + (1 + (1 + memoryCost bwProg s₀)) ≤ _; omega
          refine ⟨hsafe, hvh, ?_, by rw [hst]; exact hmod_step,
            by rw [hst]; exact hfr_bw.trans htfr, by rw [hst]; exact hwf', fun a ha => by
              rw [hst]; exact (hmod_step.mem_eq_of_not_mem (by rw [htfr]; omega)
                (by simp only [S, Set.mem_Ico]; omega)).trans (hframe a ha),
            cid + 1, hres, by omega, fun x => by rw [hst]; exact hcr' x, fun x hx => ?_,
            fun c hc => ?_, fun x hx y => ?_⟩
          · rw [hst, hres]
            dsimp only [stepProg, s₀, mem₁, bwProg, pot, r] at hcost hm_pot ⊢; omega
          · rw [hst]; by_cases hxk : x.val < k
            · have hx_old := hvis x hxk; have hhold := (hold_bw x).2 hx_old
              dsimp only [s₀, mem₁, bwProg, r] at hhold ⊢; omega
            · have hxr : x = r := Fin.ext (by dsimp only [r]; omega)
              subst hxr; have hr_cid := (hrel' r).mpr ((edgePartition _).refl r)
              dsimp only [s₀, mem₁, bwProg, r] at hr_cid ⊢; omega
          · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hc) with hc_lt | rfl
            · obtain ⟨x, hx⟩ := hsurj c hc_lt
              exact ⟨x, by rw [hst, (hold_bw x).2 (by omega), hx]⟩
            · exact ⟨r, by rw [hst]; exact (hrel' r).mpr ((edgePartition _).refl r)⟩
          · rw [hst] at hx ⊢
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hx) with hx_lt | hx_eq
            · have hx_old := (hold_bw x).1.mp hx_lt; have hconn_xy := hconn x hx_old y
              refine ⟨fun hxy => ?_, fun heq => ?_⟩
              · have hy_old := hconn_xy.mp hxy
                rw [(hold_bw y).2 (by omega), (hold_bw x).2 hx_old, hy_old]
              · have hy_old := (hold_bw y).1.mp (heq ▸ hx_lt)
                rw [(hold_bw y).2 hy_old, (hold_bw x).2 hx_old] at heq; exact hconn_xy.mpr heq
            · rw [hx_eq]; have hrx := (hrel' x).mp hx_eq
              exact ⟨fun hxy => (hrel' y).mpr ((edgePartition _).trans hrx hxy),
                fun hy => (edgePartition _).trans ((edgePartition _).symm hrx) ((hrel' y).mp hy)⟩
        · have hc_lt : t.mem (compBase + k) < cid := (hcr ⟨k, hk⟩).elim (fun h => absurd h hcv) id
          have hsafe : ccOuterStepSafe w (cfg, ⟨k, cid⟩) t := by
            dsimp only [ccOuterStepSafe, cfg]
            exact ⟨h16, hfit_n1.of_le (by omega), hfit_n1.of_le (by omega), by rw [htfr]; omega,
              fun h => absurd h hcv⟩
          have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
            dsimp only [stepProg]; rw [hprog]
            exact validHistory_read_bind (by rw [htfr]; omega) (by
              simp only [hcv, ↓reduceIte]; exact validHistory_pure w _ _)
          have hst : (Memory.spec 0).clientState t stepProg = t := by
            dsimp only [stepProg]; rw [hprog, clientState_bind_read]
            simp only [hcv, ↓reduceIte]; rfl
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨k + 1, cid⟩ := by
            dsimp only [stepProg]; rw [hprog, clientResult_bind_read]
            simp only [hcv, ↓reduceIte, StateTransitionSpec.clientResult_pure]
          have hcost : memoryCost stepProg t ≤ 1 := by
            dsimp only [stepProg]; rw [hprog, memoryCost_bind', memoryCost_read,
              clientResult_read, clientState_read]; simp only [hcv, ↓reduceIte,
              memoryCost_pure, add_zero]; omega
          refine ⟨hsafe, hvh, by rw [hst, hres]; dsimp only [stepProg, pot] at hcost ⊢; omega,
            ⟨by rw [hst], fun _ _ _ => by rw [hst]⟩, by rw [hst]; exact htfr,
            by rw [hst]; exact hwt, fun a ha => by rw [hst]; exact hframe a ha, cid, hres, by omega,
            fun x => by rw [hst]; exact hcr x, fun x hx => ?_,
            fun c hc => let ⟨x, hx⟩ := hsurj c hc; ⟨x, by rw [hst]; exact hx⟩,
            fun x hx y => by rw [hst] at hx ⊢; exact hconn x hx y⟩
          rw [hst]; by_cases hxk : x.val < k
          · exact hvis x hxk
          · exact (Fin.ext (by dsimp only; omega) : x = ⟨k, hk⟩) ▸ hc_lt)
      ⟨0, 0⟩ s ⟨rfl, hwf, fun _ _ => rfl, 0, rfl, le_rfl, fun x => .inl (hinit x),
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hpot0 : pot 0 ⟨0, 0⟩ s = 4 * n + 8 * es.length := ccPot_zero hcsr hinit
  have hm : memoryCost (iterate ccOuterStep cfg n ⟨0, 0⟩) s ≤ 7 * n + 8 * es.length := by
    dsimp only [pot] at hm_pot hpot0; omega
  refine ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, hm, hmod, hfr, hwf', by rw [hres_eq],
    by rw [hres_eq]; exact hcid_le, fun x => by rw [hres_eq]; exact hvis_all x x.isLt,
    fun c hc => by rw [hres_eq] at hc; exact hsurj_all c hc,
    fun x y => by rw [eq_comm]; exact (hconn_all x (hvis_all x x.isLt) y).symm⟩⟩

/-! ## `connectedComponentsProg`: Program, Realization, and Framed Specification -/

/-- Compute connected components of `g : GraphSlice` in `O(m + n)` memory operations,
returning `⟨compBase, numComps⟩`. -/
def connectedComponentsProg (g : GraphSlice) : Memory.Prog ComponentsResult := do
  let csr ← buildUndirCSR g
  let compB ← Memory.allocBlockDirty g.numVertices
  let _ ← fillConstProg compB.base g.numVertices g.numVertices
  let queueB ← Memory.allocBlockDirty g.numVertices
  let res ← iterate ccOuterStep
    ⟨csr.offBase, csr.adjBase, compB.base, queueB.base, g.numVertices⟩ g.numVertices ⟨0, 0⟩
  pure ⟨compB.base, res.cid⟩

private theorem connectedComponentsProg_word_spec {w n edgeBase : ℕ}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (4 * n + 4 * es.length + 1))) :
    let m := es.length; let csrOff := s.frontier; let csrAdj := csrOff + (n + 1)
    let compBase := csrOff + (2 * n + 4 * m + 1); let queueBase := compBase + n
    let s₁ : Memory.State := ⟨((Memory.spec 0).clientState s (buildUndirCSR ⟨n, m, edgeBase⟩)).mem,
      compBase + n⟩
    let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg compBase n n)
    let s₃ : Memory.State := ⟨s₂.mem, queueBase + n⟩
    iterationSafe ccOuterStep ccOuterStepSafe w
      ⟨csrOff, csrAdj, compBase, queueBase, n⟩ n ⟨0, 0⟩ s₃ ∧
    Memory.FramedTriple w s (connectedComponentsProg ⟨n, m, edgeBase⟩) (24 * m + 13 * n + 8) ∅
      fun res s' =>
        res.compBase = compBase ∧
        res.numComps ≤ n ∧
        s'.frontier = s.frontier + (4 * n + 4 * m + 1) ∧
        Memory.WellFormed w s' ∧
        (∀ u : Fin n, s'.mem (res.compBase + u.val) < res.numComps) ∧
        (∀ c : Fin res.numComps, ∃ u : Fin n, s'.mem (res.compBase + u.val) = c.val) ∧
        (∀ x y : Fin n, s'.mem (res.compBase + x.val) = s'.mem (res.compBase + y.val) ↔
          (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true) ∧
        res.numComps = (edgePartition (es.map IndexedEdge.toWeighted)).numComponents := by
  let m := es.length; let csrOff := s.frontier; let csrAdj := csrOff + (n + 1)
  let compBase := csrOff + (2 * n + 4 * m + 1); let queueBase := compBase + n
  let fEnd := queueBase + n; let S_all : Set ℕ := Set.Ico s.frontier fEnd
  have hfit_n1 : Fits w (n + 1) := hfit.of_le (by omega)
  have hfit_n : Fits w n := hfit_n1.of_le (by omega)
  have hfit_comp : Fits w (compBase + n) := hfit.of_le (by dsimp only [compBase, csrOff]; omega)
  have hfit_q : Fits w (queueBase + n) :=
    hfit.of_le (by dsimp only [queueBase, compBase, csrOff]; omega)
  have hft_csr := buildUndirCSR_spec h16 hwf hin hin_lt (hfit.of_le (by omega))
  let s_csr := (Memory.spec 0).clientState s (buildUndirCSR ⟨n, m, edgeBase⟩)
  obtain ⟨_, _, _, hcsr_off, hcsr_adj, _, hwf_csr, hcsr_holds⟩ :=
    framedTriple_iff_realization.mp hft_csr
  let s₁ : Memory.State := ⟨s_csr.mem, compBase + n⟩
  have hft_fill := fillConstProg_spec (base := compBase) (val := n) (count := n) (s := s₁)
    ⟨hfit_comp, hwf_csr.mem_fits⟩ hfit_n hfit_n (le_refl _)
  let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg compBase n n)
  obtain ⟨_, _, hmod_fill, hfr_fill, hwf₂, hvals_fill⟩ := framedTriple_iff_realization.mp hft_fill
  let s₃ : Memory.State := ⟨s₂.mem, queueBase + n⟩
  rw [hcsr_off, hcsr_adj] at hcsr_holds
  have hcsr_3 := holdsUndirCSR_of_ico (s := s₁) (s' := s₂) hcsr_holds hmod_fill
    (by dsimp only [compBase, csrOff]; omega) (by dsimp only [compBase, csrAdj, csrOff]; omega)
    (by dsimp only [s₁]; omega)
  obtain ⟨hsafe_out, hft_out⟩ := ccOuter_spec (s := s₃) h16 ⟨hfit_q, hwf₂.mem_fits⟩ hfit_n1
    (hfit.of_le (by omega)) hcsr_3 (by omega)
    (by dsimp only [compBase, csrAdj, csrOff]; omega) le_rfl le_rfl
    (fun u => hvals_fill u.val u.isLt)
  refine ⟨hsafe_out, ?_⟩
  have hprog : connectedComponentsProg ⟨n, m, edgeBase⟩ =
      (buildUndirCSR ⟨n, m, edgeBase⟩ >>= fun csr => Memory.allocBlockDirty n >>= fun compB =>
        fillConstProg compB.base n n >>= fun _ => Memory.allocBlockDirty n >>= fun queueB =>
          iterate ccOuterStep ⟨csr.offBase, csr.adjBase, compB.base, queueB.base, n⟩ n ⟨0, 0⟩ >>=
            fun res => pure ⟨compB.base, res.cid⟩) := rfl
  rw [hprog]
  have hsub_S : Set.Ico compBase (queueBase + n) ⊆ S_all := fun x hx => by
    simp only [Set.mem_Ico] at hx; simp only [S_all, Set.mem_Ico]
    dsimp only [S_all, fEnd, queueBase, compBase, csrOff] at *; omega
  let Post : ComponentsResult → Memory.State → Prop := fun res s' =>
    res.compBase = compBase ∧ res.numComps ≤ n ∧ s'.frontier = s.frontier + (4 * n + 4 * m + 1) ∧
    Memory.WellFormed w s' ∧
    (∀ u : Fin n, s'.mem (res.compBase + u.val) < res.numComps) ∧
    (∀ c : Fin res.numComps, ∃ u : Fin n, s'.mem (res.compBase + u.val) = c.val) ∧
    (∀ x y : Fin n, s'.mem (res.compBase + x.val) = s'.mem (res.compBase + y.val) ↔
      (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true) ∧
    res.numComps = (edgePartition (es.map IndexedEdge.toWeighted)).numComponents
  have hout_pure : Memory.FramedTriple w s₃
      (iterate ccOuterStep ⟨csrOff, csrAdj, compBase, queueBase, n⟩ n ⟨0, 0⟩ >>= fun res =>
        pure (⟨compBase, res.cid⟩ : ComponentsResult))
      (7 * n + 8 * m + 0) S_all Post := by
    refine framedTriple_seq_frame hft_out (by simpa only [s₃] using hsub_S) (Set.empty_subset _) ?_
    rintro ⟨hfr_o, hwf_o, _, hcid_o, hvis_o, hsurj_o, hconn_o⟩
    refine Memory.FramedTriple.pure ⟨rfl, hcid_o,
      by rw [hfr_o]; dsimp only [fEnd, queueBase, compBase, csrOff, s₃]; omega, hwf_o,
      hvis_o, fun c => hsurj_o c.val c.isLt, fun x y => hconn_o x y, ?_⟩
    set itProg := iterate ccOuterStep ⟨csrOff, csrAdj, compBase, queueBase, n⟩ n ⟨0, 0⟩
    set res_o := (Memory.spec 0).clientResult s₃ itProg
    set s' := (Memory.spec 0).clientState s₃ itProg
    let p := edgePartition (es.map IndexedEdge.toWeighted)
    let f : Fin res_o.cid → Finset (Fin n) :=
      fun c => p.classOf (Classical.choose (hsurj_o c.val c.isLt))
    change res_o.cid = p.components.card; rw [← Fintype.card_fin res_o.cid]
    refine Finset.card_bij (fun c _ => f c) (fun c _ => p.classOf_mem_components _)
      (fun c₁ _ c₂ _ hfeq => ?_) (fun K hK => ?_)
    · have hmem : Classical.choose (hsurj_o c₁.val c₁.isLt) ∈ f c₂ := hfeq ▸ p.self_mem_classOf _
      have heq_mem := (hconn_o _ _).mpr (DisjointSet.Partition.mem_classOf.mp hmem)
      rw [Classical.choose_spec (hsurj_o c₁.val c₁.isLt),
        Classical.choose_spec (hsurj_o c₂.val c₂.isLt)] at heq_mem; exact Fin.ext heq_mem.symm
    · obtain ⟨r, _, rfl⟩ := DisjointSet.Partition.mem_components.mp hK
      exact ⟨⟨s'.mem (compBase + r.val), hvis_o r⟩, Finset.mem_univ _,
        DisjointSet.Partition.classOf_eq_iff.mpr ((hconn_o _ r).mp
          (Classical.choose_spec (hsurj_o _ (hvis_o r))))⟩
  exact ((framedTriple_seq_frame hft_csr (Set.empty_subset _) le_rfl
    fun ⟨hco, hca, hcfr, _, _⟩ => Memory.FramedTriple.allocBlockDirty_bind
      (by rw [hcfr]; exact hfit_comp) (by
        rw [hcfr, hco, hca]
        exact framedTriple_seq_frame hft_fill (fun x hx =>
            hsub_S ⟨hx.1, hx.2.trans_le (by dsimp only [queueBase, compBase]; omega)⟩)
          le_rfl fun _ => Memory.FramedTriple.allocBlockDirty_bind (by rw [hfr_fill]; exact hfit_q)
            (by rw [hfr_fill]; dsimp only [s₁]; exact hout_pure))).frame_empty_of_ge_frontier
    (S := Set.Ico s.frontier fEnd) fun _ ha => ha.1).mono (by omega) fun _ _ h => h

private theorem buildUndirCSR_cs {w : ℕ} {g : GraphSlice} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hlt : g.edgeBase + 4 * g.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (2 * g.numVertices + 4 * g.numEdges + 1)))
    (hedges : ∀ j < g.numEdges, s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
      s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) :
    ((Memory.spec 0).clientResult s (buildUndirCSR g) =
      ⟨s.frontier, s.frontier + (g.numVertices + 1)⟩) ∧
    ((Memory.spec 0).clientState s (buildUndirCSR g)).frontier =
      s.frontier + (2 * g.numVertices + 4 * g.numEdges + 1) ∧
    Memory.WellFormed w ((Memory.spec 0).clientState s (buildUndirCSR g)) := by
  let es := edgesOfMem g.numVertices g.numEdges g.edgeBase s.mem hedges
  have hlen : es.length = g.numEdges := edgesOfMem_length _ _ _ _ _
  obtain ⟨_, _, _, ho, ha, hfr, hwf_c, _⟩ := framedTriple_iff_realization.mp
    (buildUndirCSR_spec h16 hwf (holdsIndexedEdges_edgesOfMem _ _ _ _ _)
      (by rw [hlen]; exact hlt) (by rw [hlen]; exact hfit))
  have hes_g : (⟨g.numVertices, es.length, g.edgeBase⟩ : GraphSlice) = g := by simp [hlen]
  rw [hes_g] at ho ha hfr hwf_c; rw [hlen] at hfr
  refine ⟨?_, hfr, hwf_c⟩
  cases hres : (Memory.spec 0).clientResult s (buildUndirCSR g)
  rw [hres] at ho ha; dsimp only at ho ha; exact congrArg₂ UndirCSR.mk ho ha

/-- Uniform `Realizes .exact` certificate for `connectedComponentsProg` with `work = 0`. -/
theorem realizes_connectedComponentsProg :
    Realizes .exact connectedComponentsProg WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (4 * g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact connectedComponentsProg WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let csrOff := s.frontier; let csrAdj := csrOff + (g.numVertices + 1)
        let compBase := csrOff + (2 * g.numVertices + 4 * g.numEdges + 1)
        let queueBase := compBase + g.numVertices
        let s₁ : Memory.State := ⟨((Memory.spec 0).clientState s (buildUndirCSR g)).mem,
          compBase + g.numVertices⟩
        let s₃ : Memory.State := ⟨((Memory.spec 0).clientState s₁
          (fillConstProg compBase g.numVertices g.numVertices)).mem, queueBase + g.numVertices⟩
        Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (4 * g.numVertices + 4 * g.numEdges + 1)) ∧
        (∀ j < g.numEdges, s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
        iterationSafe ccOuterStep ccOuterStepSafe w
          ⟨csrOff, csrAdj, compBase, queueBase, g.numVertices⟩ g.numVertices ⟨0, 0⟩ s₃)
      (fun _ _ => 0) := by
    unfold connectedComponentsProg
    realize [realizes_buildUndirCSR, realizes_allocBlockDirty, realizes_fillConstProg,
      realizes_ccOuterStep]
    all_goals
      rcases h with ⟨h16, hlt, hfit, hedges, hsafe⟩
      first
      | exact hfit.of_le (by omega) | exact h16.of_le (by decide) | exact hlt | exact hedges
      | (rw [allocDirty_cr, allocDirty_cs]; done)
      | (have hc := buildUndirCSR_cs h16 hmem hlt (hfit.of_le (by omega)) hedges
         rw [hc.1, allocDirty_cr, allocDirty_cs, hc.2.1, allocDirty_cr, allocDirty_cs]
         have hwf1 : Memory.WellFormed w
             ⟨((Memory.spec 0).clientState s (buildUndirCSR d)).mem,
              s.frontier + (2 * d.numVertices + 4 * d.numEdges + 1) + d.numVertices⟩ :=
           ⟨by dsimp only; exact hfit.of_le (by omega), hc.2.2.mem_fits⟩
         have hfr2 := fillConst_fr _ d.numVertices d.numVertices hwf1
           (hfit.of_le (by omega)) (hfit.of_le (by omega)) (le_refl _)
         rw [hfr2]
         exact iterationSafe_imp hsafe (fun _ => rfl) (fun _ _ hs => hs))
  refine hraw.consequence (fun w g s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  let es := edgesOfMem g.numVertices g.numEdges g.edgeBase s.mem hedges
  have hlen : es.length = g.numEdges := edgesOfMem_length _ _ _ _ _
  have hsafe := (connectedComponentsProg_word_spec h16 hmem (holdsIndexedEdges_edgesOfMem _ _ _ _ _)
    (by rw [hlen]; exact hin_lt) (by rw [hlen]; exact hfit)).1
  exact ⟨h16, hin_lt, hfit, hedges, by simpa [es, hlen] using hsafe⟩

/-- Framed specification for `connectedComponentsProg`: labels every vertex `u : Fin n` with its
component ID in `[0, res.numComps)` matching `(edgePartition (es.map IndexedEdge.toWeighted))`,
with `res.numComps = (edgePartition (es.map IndexedEdge.toWeighted)).numComponents`, leaving all
cells below `s.frontier` untouched, in at most `24 * es.length + 13 * n + 8` memory ops. -/
theorem connectedComponentsProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (4 * n + 4 * es.length + 1))) :
    Memory.FramedTriple w s (connectedComponentsProg ⟨n, es.length, edgeBase⟩)
      (24 * es.length + 13 * n + 8) ∅ fun res s' =>
        res.compBase = s.frontier + (2 * n + 4 * es.length + 1) ∧
        res.numComps ≤ n ∧
        s'.frontier = s.frontier + (4 * n + 4 * es.length + 1) ∧
        Memory.WellFormed w s' ∧
        (∀ u : Fin n, s'.mem (res.compBase + u.val) < res.numComps) ∧
        (∀ c : Fin res.numComps, ∃ u : Fin n, s'.mem (res.compBase + u.val) = c.val) ∧
        (∀ x y : Fin n, s'.mem (res.compBase + x.val) = s'.mem (res.compBase + y.val) ↔
          (edgePartition (es.map IndexedEdge.toWeighted)).rel x y = true) ∧
        res.numComps = (edgePartition (es.map IndexedEdge.toWeighted)).numComponents :=
  (connectedComponentsProg_word_spec h16 hwf hin hin_lt hfit).2

/-! ## `contractEdgesProg`: Edge Endpoint Contraction -/

private structure ContractCfg where
  edgeBase : ℕ
  compBase : ℕ
  outBase : ℕ

private word_enc_structure encContractCfg : ContractCfg where
  edgeBase : wordWords,
  compBase : wordWords,
  outBase : wordWords

private def contractEdgeStep (x : ContractCfg × ℕ) : Memory.Prog ℕ := do
  let cfg := Prod.fst x
  let k := Prod.snd x
  let u ← Memory.read (cfg.edgeBase + 4 * k)
  let v ← Memory.read (cfg.edgeBase + 4 * k + 1)
  let wt ← Memory.read (cfg.edgeBase + 4 * k + 2)
  let eid ← Memory.read (cfg.edgeBase + 4 * k + 3)
  let cu ← Memory.read (cfg.compBase + u)
  let cv ← Memory.read (cfg.compBase + v)
  Memory.write (cfg.outBase + 4 * k) cu
  Memory.write (cfg.outBase + 4 * k + 1) cv
  Memory.write (cfg.outBase + 4 * k + 2) wt
  Memory.write (cfg.outBase + 4 * k + 3) eid
  pure (k + 1)

private def contractEdgeStepSafe (w : ℕ) (x : ContractCfg × ℕ) (s : Memory.State) : Prop :=
  let cfg := Prod.fst x
  let k := Prod.snd x
  Fits w 16 ∧ Fits w (k + 1) ∧
    cfg.edgeBase + 4 * k + 3 < s.frontier ∧
    cfg.compBase + s.mem (cfg.edgeBase + 4 * k) < s.frontier ∧
    cfg.compBase + s.mem (cfg.edgeBase + 4 * k + 1) < s.frontier ∧
    cfg.outBase + 4 * k + 3 < s.frontier

private theorem realizes_contractEdgeStep_history : Realizes .exact
    contractEdgeStep (appendWords encContractCfg wordWords) wordWords
    (fun w d s => contractEdgeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (contractEdgeStep d)))
    (fun _ _ => 0) := by
  unfold contractEdgeStep
  realize
  all_goals
    obtain ⟨⟨h16, hk, he, hu, hv, ho⟩, _⟩ := h; have hfront := hmem.frontier_fits
    have hmu := hmem.mem_fits (d.1.edgeBase + 4 * d.2)
    have hmv := hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 1)
    have hmw := hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 2)
    have hmid := hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 3)
    have hcu := hmem.mem_fits (d.1.compBase + s.mem (d.1.edgeBase + 4 * d.2))
    have hcv := hmem.mem_fits (d.1.compBase + s.mem (d.1.edgeBase + 4 * d.2 + 1))
    first | exact h16.of_le (by decide) | fits

private theorem realizes_contractEdgeStep : Realizes .exact
    contractEdgeStep (appendWords encContractCfg wordWords) wordWords
    contractEdgeStepSafe (fun _ _ => 0) :=
  realizes_contractEdgeStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Remap `d.numEdges` stride-4 edges starting at `d.edgeBase` along vertex labels at
`d.compBase`, returning the base address of a newly allocated contracted stride-4 array. -/
def contractEdgesProg (d : ContractEdgesArgs) : Memory.Prog ℕ := do
  let outB ← Memory.allocBlockDirty (4 * d.numEdges)
  let _ ← iterate contractEdgeStep ⟨d.edgeBase, d.compBase, outB.base⟩ d.numEdges 0
  pure outB.base

private theorem contractEdges_loop_spec {w : ℕ} {d : ContractEdgesArgs} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit : Fits w (s.frontier + 4 * d.numEdges))
    (hbounds : ∀ j < d.numEdges,
      d.edgeBase + 4 * j + 3 < s.frontier ∧
      d.compBase + s.mem (d.edgeBase + 4 * j) < s.frontier ∧
      d.compBase + s.mem (d.edgeBase + 4 * j + 1) < s.frontier) :
    let outBase := s.frontier
    let fEnd := outBase + 4 * d.numEdges
    iterationSafe contractEdgeStep contractEdgeStepSafe w
      ⟨d.edgeBase, d.compBase, outBase⟩ d.numEdges 0 ⟨s.mem, fEnd⟩ ∧
    Memory.FramedTriple w ⟨s.mem, fEnd⟩
      (iterate contractEdgeStep ⟨d.edgeBase, d.compBase, outBase⟩ d.numEdges 0)
      (10 * d.numEdges) (Set.Ico outBase fEnd) fun _ t =>
        t.frontier = fEnd ∧ Memory.WellFormed w t ∧
        (∀ a < outBase, t.mem a = s.mem a) ∧
        ∀ i < d.numEdges,
          t.mem (outBase + 4 * i) = s.mem (d.compBase + s.mem (d.edgeBase + 4 * i)) ∧
          t.mem (outBase + 4 * i + 1) = s.mem (d.compBase + s.mem (d.edgeBase + 4 * i + 1)) ∧
          t.mem (outBase + 4 * i + 2) = s.mem (d.edgeBase + 4 * i + 2) ∧
          t.mem (outBase + 4 * i + 3) = s.mem (d.edgeBase + 4 * i + 3) := by
  let outBase := s.frontier
  let fEnd := outBase + 4 * d.numEdges
  let s₀ : Memory.State := ⟨s.mem, fEnd⟩
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit, hwf.mem_fits⟩
  let S : Set ℕ := Set.Ico outBase fEnd
  let inv (k st : ℕ) (t : Memory.State) : Prop :=
    st = k ∧ t.frontier = fEnd ∧ Memory.WellFormed w t ∧ (∀ a < outBase, t.mem a = s.mem a) ∧
    ∀ i < k,
      t.mem (outBase + 4 * i) = s.mem (d.compBase + s.mem (d.edgeBase + 4 * i)) ∧
      t.mem (outBase + 4 * i + 1) = s.mem (d.compBase + s.mem (d.edgeBase + 4 * i + 1)) ∧
      t.mem (outBase + 4 * i + 2) = s.mem (d.edgeBase + 4 * i + 2) ∧
      t.mem (outBase + 4 * i + 3) = s.mem (d.edgeBase + 4 * i + 3)
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step contractEdgeStep contractEdgeStepSafe w
      ⟨d.edgeBase, d.compBase, outBase⟩ 10 d.numEdges inv S
      (fun k hk st t ⟨hst_eq, htfr, hwf_t, hframe, hpref⟩ => by
        subst st; obtain ⟨hb1, hb2, hb3⟩ := hbounds k hk
        have hu : t.mem (d.edgeBase + 4 * k) = s.mem (d.edgeBase + 4 * k) := hframe _ (by omega)
        have hv : t.mem (d.edgeBase + 4 * k + 1) = s.mem (d.edgeBase + 4 * k + 1) :=
          hframe _ (by omega)
        let stepProg := contractEdgeStep (⟨d.edgeBase, d.compBase, outBase⟩, k)
        have hsafe : contractEdgeStepSafe w (⟨d.edgeBase, d.compBase, outBase⟩, k) t := by
          dsimp only [contractEdgeStepSafe]
          exact ⟨h16, hfit.of_le (by omega), by rw [htfr]; dsimp only [fEnd, outBase]; omega,
            by rw [htfr, hu]; dsimp only [fEnd, outBase]; omega,
            by rw [htfr, hv]; dsimp only [fEnd, outBase]; omega,
            by rw [htfr]; dsimp only [fEnd, outBase]; omega⟩
        have hmem_t : ∀ a, Fits w (t.mem a) := hwf_t.mem_fits
        have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
          dsimp only [stepProg, contractEdgeStep]; valid_prog with [htfr, hu, hv]
          all_goals dsimp only [outBase, fEnd] at *
          all_goals first | exact hmem_t _ | rw [htfr]; omega
        have hcost : memoryCost stepProg t ≤ 10 := by
          dsimp only [stepProg, contractEdgeStep]; prog_cost
        have hres : (Memory.spec 0).clientResult t stepProg = k + 1 := by
          dsimp only [stepProg, contractEdgeStep]
          simp only [clientResult_bind_read, clientResult_bind_write,
            StateTransitionSpec.clientResult_pure]
        let t' : Memory.State :=
          ⟨Function.update (Function.update (Function.update (Function.update t.mem
            (outBase + 4 * k) (t.mem (d.compBase + t.mem (d.edgeBase + 4 * k))))
            (outBase + 4 * k + 1) (t.mem (d.compBase + t.mem (d.edgeBase + 4 * k + 1))))
            (outBase + 4 * k + 2) (t.mem (d.edgeBase + 4 * k + 2)))
            (outBase + 4 * k + 3) (t.mem (d.edgeBase + 4 * k + 3)), t.frontier⟩
        have hst : (Memory.spec 0).clientState t stepProg = t' := by
          dsimp only [stepProg, contractEdgeStep]; repeat rw [clientState_bind_read]; rfl
        have hmod : ∀ x, x ∉ S → t'.mem x = t.mem x := fun x hx => by
          dsimp only [t']; simp only [S, Set.mem_Ico, not_and, not_lt] at hx; update_simp
        refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
          ⟨hvh, hcost, ⟨by rw [hst], fun x _ hx => by rw [hst]; exact hmod x hx⟩, ?_⟩⟩
        rw [hst, hres]; refine ⟨rfl, htfr, hst ▸ wellFormed_clientState hwf_t hvh,
          fun a ha => (hmod a (by simp only [S, Set.mem_Ico]; omega)).trans (hframe a ha),
          fun i hi => ?_⟩
        dsimp only [t']; by_cases hik : i = k
        · subst i; refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp
          · exact (hframe _ (by omega)).trans (by rw [hu])
          · exact (hframe _ (by omega)).trans (by rw [hv])
          all_goals exact hframe _ (by omega)
        · obtain ⟨h1, h2, h3, h4⟩ := hpref i (by omega)
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (update_simp; assumption))
      0 s₀ ⟨rfl, rfl, hwf₀, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe, hft.mono le_rfl fun _ _ ⟨_, hfr, hw, hfrm, hv⟩ => ⟨hfr, hw, hfrm, hv⟩⟩

private theorem contractEdgesProg_word_spec {w n n' : ℕ} {d : ContractEdgesArgs}
    {es : List (IndexedEdge n)} {compFn : Fin n → ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hm : d.numEdges = es.length) (hin : HoldsIndexedEdges d.edgeBase es s.mem)
    (hin_lt : d.edgeBase + 4 * es.length ≤ s.frontier)
    (hcomp : ∀ u : Fin n, s.mem (d.compBase + u.val) = compFn u)
    (hcomp_disj : d.compBase + n ≤ s.frontier)
    (hcomp_lt : ∀ e ∈ es, compFn e.u < n' ∧ compFn e.v < n')
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    let outBase := s.frontier; let fEnd := outBase + 4 * es.length
    iterationSafe contractEdgeStep contractEdgeStepSafe w
      ⟨d.edgeBase, d.compBase, outBase⟩ es.length 0 ⟨s.mem, fEnd⟩ ∧
    Memory.FramedTriple w s (contractEdgesProg d) (10 * es.length + 1) ∅ fun out s' =>
      out = s.frontier ∧ s'.frontier = s.frontier + 4 * es.length ∧ Memory.WellFormed w s' ∧
      ∃ esOut : List (IndexedEdge n'), esOut.length = es.length ∧
        HoldsIndexedEdges out esOut s'.mem ∧
        ∀ i (hi : i < es.length) (hi' : i < esOut.length),
          (esOut[i]'hi').u.val = compFn (es[i]'hi).u ∧
          (esOut[i]'hi').v.val = compFn (es[i]'hi).v ∧
          (esOut[i]'hi').weight = (es[i]'hi).weight ∧ (esOut[i]'hi').id = (es[i]'hi).id := by
  have hbounds : ∀ j < d.numEdges,
      d.edgeBase + 4 * j + 3 < s.frontier ∧
      d.compBase + s.mem (d.edgeBase + 4 * j) < s.frontier ∧
      d.compBase + s.mem (d.edgeBase + 4 * j + 1) < s.frontier := fun j hj => by
    have hj' : j < es.length := hm ▸ hj
    obtain ⟨hu, hv, _, _⟩ := hin j hj'
    have := (es[j]'hj').u.isLt; have := (es[j]'hj').v.isLt
    exact ⟨by omega, by rw [hu]; omega, by rw [hv]; omega⟩
  obtain ⟨hsafe, hft_it⟩ := contractEdges_loop_spec h16 hwf (hm ▸ hfit) hbounds
  rw [hm] at hsafe hft_it
  refine ⟨hsafe, ?_⟩
  have hprog : contractEdgesProg d =
      (Memory.allocBlockDirty (4 * es.length) >>= fun outB =>
        iterate contractEdgeStep ⟨d.edgeBase, d.compBase, outB.base⟩ es.length 0 >>= fun _ =>
          pure outB.base) := by simp only [contractEdgesProg, hm]
  rw [hprog]
  let esOut : List (IndexedEdge n') := List.ofFn fun i : Fin es.length =>
    ⟨⟨compFn (es[i.val]'i.isLt).u, (hcomp_lt _ (List.getElem_mem i.isLt)).1⟩,
     ⟨compFn (es[i.val]'i.isLt).v, (hcomp_lt _ (List.getElem_mem i.isLt)).2⟩,
     (es[i.val]'i.isLt).weight, (es[i.val]'i.isLt).id⟩
  have hiter_ft : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * es.length⟩
      (iterate contractEdgeStep ⟨d.edgeBase, d.compBase, s.frontier⟩ es.length 0 >>=
        fun _ => pure s.frontier)
      (10 * es.length + 0) (Set.Ico s.frontier (s.frontier + 4 * es.length)) fun out s' =>
        out = s.frontier ∧ s'.frontier = s.frontier + 4 * es.length ∧ Memory.WellFormed w s' ∧
        ∃ esOut : List (IndexedEdge n'), esOut.length = es.length ∧
          HoldsIndexedEdges out esOut s'.mem ∧
          ∀ i (hi : i < es.length) (hi' : i < esOut.length),
            (esOut[i]'hi').u.val = compFn (es[i]'hi).u ∧
            (esOut[i]'hi').v.val = compFn (es[i]'hi).v ∧
            (esOut[i]'hi').weight = (es[i]'hi).weight ∧ (esOut[i]'hi').id = (es[i]'hi).id :=
    framedTriple_seq_frame hft_it le_rfl (Set.empty_subset _) fun ⟨hfr, hwf', _, hvals⟩ =>
      Memory.FramedTriple.pure ⟨rfl, hfr, hwf', esOut, by simp [esOut], fun i hi => by
        have hi_len : i < es.length := by simpa [esOut] using hi
        obtain ⟨hu, hv, hw, hid⟩ := hin i hi_len; obtain ⟨m0, m1, m2, m3⟩ := hvals i hi_len
        simp only [esOut, List.getElem_ofFn]
        exact ⟨m0.trans (by rw [hu, hcomp]), m1.trans (by rw [hv, hcomp]),
          m2.trans hw, m3.trans hid⟩,
        fun _ _ _ => by simp [esOut]⟩
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit hiter_ft).frame_empty_of_ge_frontier
    (S := Set.Ico s.frontier (s.frontier + 4 * es.length))
    fun _ ha => ha.1).mono (by omega) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `contractEdgesProg` with `work = 0`. -/
theorem realizes_contractEdgesProg :
    Realizes .exact contractEdgesProg WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + 4 * d.numEdges) ∧
        (∀ j < d.numEdges, d.edgeBase + 4 * j + 3 < s.frontier ∧
          d.compBase + s.mem (d.edgeBase + 4 * j) < s.frontier ∧
          d.compBase + s.mem (d.edgeBase + 4 * j + 1) < s.frontier))
      (fun _ _ => 0) := by
  have hraw : Realizes .exact contractEdgesProg WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (4 * d.numEdges) ∧ Fits w (s.frontier + 4 * d.numEdges) ∧
        iterationSafe contractEdgeStep contractEdgeStepSafe w
          ⟨d.edgeBase, d.compBase, s.frontier⟩ d.numEdges 0 ⟨s.mem, s.frontier + 4 * d.numEdges⟩)
      (fun _ _ => 0) := by
    unfold contractEdgesProg
    realize [realizes_allocBlockDirty, realizes_contractEdgeStep]
    all_goals first
    | exact h.1.of_le (by decide)
    | exact h.2.1
    | exact iterationSafe_imp h.2.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w d s _ hmem ⟨h16, hfit, hbounds⟩ => ?_)
    (fun _ _ => le_rfl)
  exact ⟨h16, hfit.of_le (by omega), hfit, (contractEdges_loop_spec h16 hmem hfit hbounds).1⟩

/-- Framed specification for `contractEdgesProg`: allocates `4 * es.length` cells at
`outBase = s.frontier` and writes remapped `IndexedEdge n'` entries along `compFn`, leaving all
cells below `s.frontier` untouched, in at most `10 * es.length + 1` memory operations. -/
theorem contractEdgesProg_spec {w n n' edgeBase compBase : ℕ}
    {es : List (IndexedEdge n)} {compFn : Fin n → ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hcomp : ∀ u : Fin n, s.mem (compBase + u.val) = compFn u)
    (hcomp_disj : compBase + n ≤ s.frontier)
    (hcomp_lt : ∀ e ∈ es, compFn e.u < n' ∧ compFn e.v < n')
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    Memory.FramedTriple w s (contractEdgesProg ⟨es.length, edgeBase, compBase⟩)
      (10 * es.length + 1) ∅ fun out s' =>
        out = s.frontier ∧
        s'.frontier = s.frontier + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        ∃ esOut : List (IndexedEdge n'),
          esOut.length = es.length ∧
          HoldsIndexedEdges out esOut s'.mem ∧
          ∀ i (hi : i < es.length) (hi' : i < esOut.length),
            (esOut[i]'hi').u.val = compFn (es[i]'hi).u ∧
            (esOut[i]'hi').v.val = compFn (es[i]'hi).v ∧
            (esOut[i]'hi').weight = (es[i]'hi).weight ∧
            (esOut[i]'hi').id = (es[i]'hi).id :=
  (contractEdgesProg_word_spec h16 hwf rfl hin hin_lt hcomp hcomp_disj hcomp_lt hfit).2

/-! ## `compactVerticesProg`: Isolated-Vertex Elimination -/

private structure MarkCfg where
  edgeBase : ℕ
  markBase : ℕ

private word_enc_structure encMarkCfg : MarkCfg where
  edgeBase : wordWords,
  markBase : wordWords

private def compactMarkStep (x : MarkCfg × ℕ) : Memory.Prog ℕ := do
  let cfg := Prod.fst x
  let k := Prod.snd x
  let u ← Memory.read (cfg.edgeBase + 4 * k)
  let v ← Memory.read (cfg.edgeBase + 4 * k + 1)
  Memory.write (cfg.markBase + u) 1
  Memory.write (cfg.markBase + v) 1
  pure (k + 1)

private def compactMarkStepSafe (w : ℕ) (x : MarkCfg × ℕ) (s : Memory.State) : Prop :=
  let cfg := Prod.fst x
  let k := Prod.snd x
  Fits w 16 ∧ Fits w (k + 1) ∧
    cfg.edgeBase + 4 * k + 1 < s.frontier ∧
    cfg.markBase + s.mem (cfg.edgeBase + 4 * k) < s.frontier ∧
    cfg.markBase + s.mem (cfg.edgeBase + 4 * k + 1) < s.frontier

private theorem realizes_compactMarkStep_history : Realizes .exact
    compactMarkStep (appendWords encMarkCfg wordWords) wordWords
    (fun w d s => compactMarkStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (compactMarkStep d)))
    (fun _ _ => 0) := by
  unfold compactMarkStep
  realize
  all_goals
    obtain ⟨⟨h16, hk, he, hu, hv⟩, _⟩ := h; have hfront := hmem.frontier_fits
    have hmu := hmem.mem_fits (d.1.edgeBase + 4 * d.2)
    have hmv := hmem.mem_fits (d.1.edgeBase + 4 * d.2 + 1)
    first | exact h16.of_le (by decide) | fits

private theorem realizes_compactMarkStep : Realizes .exact
    compactMarkStep (appendWords encMarkCfg wordWords) wordWords
      compactMarkStepSafe (fun _ _ => 0) :=
  realizes_compactMarkStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem compactMark_spec {w n edgeBase markBase : ℕ}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ markBase)
    (hmark_lt : markBase + n ≤ s.frontier)
    (hfit_m1 : Fits w (es.length + 1))
    (hinit : ∀ x : Fin n, s.mem (markBase + x.val) = 0) :
    let prog := iterate compactMarkStep ⟨edgeBase, markBase⟩ es.length 0
    let s' := (Memory.spec 0).clientState s prog
    iterationSafe compactMarkStep compactMarkStepSafe w ⟨edgeBase, markBase⟩ es.length 0 s ∧
    Memory.FramedTriple w s prog (4 * es.length) (Set.Ico markBase (markBase + n))
      (fun _ t => t = s' ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t) ∧
    (∀ x : Fin n, s'.mem (markBase + x.val) = 0 ∨ s'.mem (markBase + x.val) = 1) ∧
    ∀ x : Fin n, s'.mem (markBase + x.val) = 1 ↔ ∃ e ∈ es, e.u = x ∨ e.v = x := by
  let S : Set ℕ := Set.Ico markBase (markBase + n)
  let inv (k st : ℕ) (t : Memory.State) : Prop :=
    st = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ a, a < markBase → t.mem a = s.mem a) ∧
    (∀ x : Fin n, t.mem (markBase + x.val) = 0 ∨ t.mem (markBase + x.val) = 1) ∧
    ∀ x : Fin n, t.mem (markBase + x.val) = 1 ↔
      ∃ i, ∃ (_ : i < k) (hlt : i < es.length), (es[i]'hlt).u = x ∨ (es[i]'hlt).v = x
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step compactMarkStep compactMarkStepSafe w
      ⟨edgeBase, markBase⟩ 4 es.length inv S
      (fun k hk st t ⟨hst_eq, htfr, hwt, hframe, h01, hmark⟩ => by
        subst st
        obtain ⟨hu, hv, _, _⟩ := (hin.congr fun a _ ha => hframe a (by omega)) k hk
        let ek := es[k]'hk
        have hu' : t.mem (edgeBase + 4 * k) = ek.u.val := hu
        have hv' : t.mem (edgeBase + 4 * k + 1) = ek.v.val := hv
        have hu_lt := ek.u.isLt; have hv_lt := ek.v.isLt
        let stepProg := compactMarkStep (⟨edgeBase, markBase⟩, k)
        have hsafe : compactMarkStepSafe w (⟨edgeBase, markBase⟩, k) t := by
          dsimp only [compactMarkStepSafe]
          exact ⟨h16, hfit_m1.of_le (by omega), by rw [htfr]; omega, by rw [htfr, hu']; omega,
            by rw [htfr, hv']; omega⟩
        have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
          dsimp only [stepProg, compactMarkStep]; valid_prog with [htfr, hu', hv']
          all_goals try dsimp only
          all_goals first | exact h16.of_le (by decide) | omega
        have hcost : memoryCost stepProg t ≤ 4 := by
          dsimp only [stepProg, compactMarkStep]; prog_cost
        have hres : (Memory.spec 0).clientResult t stepProg = k + 1 := by
          dsimp only [stepProg, compactMarkStep]; simp only [clientResult_bind_read,
            clientResult_bind_write, StateTransitionSpec.clientResult_pure]
        let t' : Memory.State := ⟨Function.update (Function.update t.mem (markBase + ek.u.val) 1)
          (markBase + ek.v.val) 1, t.frontier⟩
        have hst : (Memory.spec 0).clientState t stepProg = t' := by
          dsimp only [stepProg, compactMarkStep]; repeat rw [clientState_bind_read]
          rw [hu', hv']; rfl
        have hmod : ∀ a, a ∉ S → t'.mem a = t.mem a := fun a ha => by
          dsimp only [t']; simp only [S, Set.mem_Ico, not_and, not_lt] at ha; update_simp
        have hup : ∀ x : Fin n, t'.mem (markBase + x.val) =
            if x = ek.v ∨ x = ek.u then 1 else t.mem (markBase + x.val) := fun x => by
          dsimp only [t']; rw [Function.update_apply, Function.update_apply]
          simp only [Nat.add_left_cancel_iff, Fin.val_inj]
          by_cases hxv : x = ek.v <;> by_cases hxu : x = ek.u <;> simp [hxv, hxu]
        refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
          ⟨hvh, hcost, ⟨by rw [hst], fun a _ ha => by rw [hst]; exact hmod a ha⟩, ?_⟩⟩
        rw [hst, hres]; refine ⟨rfl, htfr, hst ▸ wellFormed_clientState hwt hvh,
          fun a ha => (hmod a (by simp only [S, Set.mem_Ico]; omega)).trans (hframe a ha),
          fun x => by rw [hup x]; split <;> [exact .inr rfl; exact h01 x], fun x => ?_⟩
        rw [hup x]; by_cases hor : x = ek.v ∨ x = ek.u
        · simp only [hor, ↓reduceIte, true_iff]
          exact ⟨k, Nat.lt_succ_self k, hk, hor.elim (fun h => .inr h.symm) (fun h => .inl h.symm)⟩
        · simp only [hor, ↓reduceIte, hmark x]
          refine ⟨fun ⟨i, hi, hl, h_or⟩ => ⟨i, Nat.lt_succ_of_lt hi, hl, h_or⟩,
            fun ⟨i, hi, hl, h_or⟩ => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik' | rfl
          · exact ⟨i, hik', hl, h_or⟩
          · exfalso; exact hor (h_or.elim (fun h => .inr h.symm) (fun h => .inl h.symm)))
      0 s ⟨rfl, rfl, hwf, fun _ _ => rfl, fun x => .inl (hinit x), fun x =>
        ⟨fun h => by rw [hinit x] at h; omega, fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩⟩
  obtain ⟨hv, hm, hmod, _, hfr, hwf', _, h01_end, hmark_end⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, hm, hmod, rfl, hfr, hwf'⟩, h01_end,
    fun x => (hmark_end x).trans ⟨fun ⟨i, hi, _, h_or⟩ => ⟨es[i], List.getElem_mem hi, h_or⟩,
      fun ⟨e, he, h_or⟩ => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he; exact ⟨i, hi, hi, h_or⟩⟩⟩

private structure AssignPos where
  k : ℕ
  count : ℕ

private word_enc_structure encAssignPos : AssignPos where
  k : wordWords,
  count : wordWords

private instance : WordEncoding AssignPos := ⟨2, encAssignPos⟩

private def compactAssignStep (x : ℕ × AssignPos) : Memory.Prog AssignPos := do
  let markBase := Prod.fst x
  let st := Prod.snd x
  let flag ← Memory.read (markBase + st.k)
  if flag = 1 then
    Memory.write (markBase + st.k) st.count
    pure ⟨st.k + 1, st.count + 1⟩
  else
    pure ⟨st.k + 1, st.count⟩

private def compactAssignStepSafe (w : ℕ) (x : ℕ × AssignPos) (s : Memory.State) : Prop :=
  let markBase := Prod.fst x
  let st := Prod.snd x
  Fits w 16 ∧ Fits w (st.k + 1) ∧ Fits w (st.count + 1) ∧ markBase + st.k < s.frontier

private theorem realizes_compactAssignStep_history : Realizes .exact
    compactAssignStep (appendWords wordWords encAssignPos) encAssignPos
    (fun w d s => compactAssignStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (compactAssignStep d)))
    (fun _ _ => 0) := by
  unfold compactAssignStep
  realize
  all_goals
    obtain ⟨⟨h16, hk, hc, hm⟩, _⟩ := h
    have hfront := hmem.frontier_fits; have hm_read := hmem.mem_fits (d.1 + d.2.k)
    first | exact h16.of_le (by decide) | fits

private theorem realizes_compactAssignStep : Realizes .exact
    compactAssignStep (appendWords wordWords encAssignPos) encAssignPos
    compactAssignStepSafe (fun _ _ => 0) :=
  realizes_compactAssignStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem compactAssign_spec {w n markBase : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_n1 : Fits w (n + 1)) (hmark_lt : markBase + n ≤ s.frontier) :
    let prog := iterate compactAssignStep markBase n ⟨0, 0⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    iterationSafe compactAssignStep compactAssignStepSafe w markBase n ⟨0, 0⟩ s ∧
    Memory.FramedTriple w s prog (2 * n) (Set.Ico markBase (markBase + n))
      (fun r t => r = res ∧ t = s' ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
        r.k = n ∧ r.count ≤ n) ∧
    res.k = n ∧
    res.count ≤ n ∧
    ∃ lift : Fin res.count → Fin n,
      Function.Injective lift ∧
      (∀ y : Fin res.count, s.mem (markBase + (lift y).val) = 1) ∧
      (∀ x : Fin n, s.mem (markBase + x.val) = 1 → ∃ y : Fin res.count, lift y = x) ∧
      ∀ y : Fin res.count, s'.mem (markBase + (lift y).val) = y.val := by
  let S : Set ℕ := Set.Ico markBase (markBase + n)
  let inv (k : ℕ) (st : AssignPos) (t : Memory.State) : Prop :=
    t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∃ active : List (Fin n),
      st = ⟨k, active.length⟩ ∧ active.Nodup ∧ (∀ x ∈ active, x.val < k) ∧
      (∀ x : Fin n, x.val < k → (s.mem (markBase + x.val) = 1 ↔ x ∈ active)) ∧
      (∀ i (hi : i < active.length), t.mem (markBase + (active[i]'hi).val) = i) ∧
      ∀ x : Fin n, k ≤ x.val → t.mem (markBase + x.val) = s.mem (markBase + x.val)
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step compactAssignStep compactAssignStepSafe w
      markBase 2 n inv S
      (fun k hk st t ⟨htfr, hwt, active, hst_eq, hnd, hlt_k, hact_iff, hvals, htail⟩ => by
        subst st
        let x₀ : Fin n := ⟨k, hk⟩
        have htx₀ : t.mem (markBase + k) = s.mem (markBase + k) := htail x₀ (le_refl _)
        have hx₀_not : x₀ ∉ active := fun hx => absurd (hlt_k x₀ hx) (Nat.lt_irrefl k)
        have hact_len_le : active.length < n := Nat.lt_of_succ_le (by
          simpa only [List.length_cons, Fintype.card_fin] using
            (List.nodup_cons.mpr ⟨hx₀_not, hnd⟩).length_le_card)
        let stepProg := compactAssignStep (markBase, ⟨k, active.length⟩)
        have hsafe : compactAssignStepSafe w (markBase, ⟨k, active.length⟩) t := by
          dsimp only [compactAssignStepSafe]
          exact ⟨h16, hfit_n1.of_le (by omega), hfit_n1.of_le (by omega), by rw [htfr]; omega⟩
        have hvh : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t stepProg) := by
          dsimp only [stepProg, compactAssignStep]; valid_prog with [htfr, htx₀]
          all_goals first | exact hfit_n1.of_le (by omega) | omega
        have hcost : memoryCost stepProg t ≤ 2 := by
          dsimp only [stepProg, compactAssignStep]; prog_cost
        by_cases hf : s.mem (markBase + k) = 1
        · have htf : t.mem (markBase + k) = 1 := htx₀.trans hf
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨k + 1, active.length + 1⟩ := by
            dsimp only [stepProg, compactAssignStep]; rw [clientResult_bind_read]
            simp only [htf, ↓reduceIte, clientResult_bind_write,
              StateTransitionSpec.clientResult_pure]
          let t' : Memory.State := ⟨Function.update t.mem (markBase + k) active.length, t.frontier⟩
          have hst : (Memory.spec 0).clientState t stepProg = t' := by
            dsimp only [stepProg, compactAssignStep]; rw [clientState_bind_read]
            simp only [htf, ↓reduceIte]; rfl
          have hmod : ∀ a, a ∉ S → t'.mem a = t.mem a := fun a ha => by
            dsimp only [t']; simp only [S, Set.mem_Ico, not_and, not_lt] at ha; update_simp
          refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
            ⟨hvh, hcost, ⟨by rw [hst], fun a _ ha => by rw [hst]; exact hmod a ha⟩, ?_⟩⟩
          rw [hst, hres]; refine ⟨htfr, hst ▸ wellFormed_clientState hwt hvh, active ++ [x₀],
            by simp only [List.length_append, List.length_singleton],
            List.nodup_append.mpr ⟨hnd, List.nodup_singleton x₀, fun a ha b hb => by
              simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hx₀_not ha⟩,
            fun x hx => (List.mem_append.mp hx).elim (fun h => Nat.lt_succ_of_lt (hlt_k x h))
              (fun h => by simp only [List.mem_singleton] at h; subst h; exact Nat.lt_succ_self k),
            fun x hx => ?_, fun i hi => ?_,
            fun x hx => by dsimp only [t']; update_simp; exact htail x (by omega)⟩
          · rw [List.mem_append, List.mem_singleton]; by_cases hxk : x.val < k
            · have hxne : x ≠ x₀ := fun h => by rw [h] at hxk; exact Nat.lt_irrefl k hxk
              simp only [hxne, or_false]; exact hact_iff x hxk
            · obtain rfl : x = x₀ := Fin.ext (by dsimp only [x₀]; omega)
              rw [show x₀.val = k from rfl, hf]; simp
          · dsimp only [t']; simp only [List.length_append, List.length_singleton] at hi
            by_cases hi_old : i < active.length
            · rw [List.getElem_append_left hi_old]
              have hne : (active[i]'hi_old).val ≠ k := by
                have := hlt_k (active[i]'hi_old) (List.getElem_mem hi_old); omega
              update_simp; exact hvals i hi_old
            · obtain rfl : i = active.length := by omega
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_singleton, x₀, Function.update_self]
        · have htf : t.mem (markBase + k) ≠ 1 := by rw [htx₀]; exact hf
          have hres : (Memory.spec 0).clientResult t stepProg = ⟨k + 1, active.length⟩ := by
            dsimp only [stepProg, compactAssignStep]; rw [clientResult_bind_read]
            simp only [htf, ↓reduceIte, StateTransitionSpec.clientResult_pure]
          have hst : (Memory.spec 0).clientState t stepProg = t := by
            dsimp only [stepProg, compactAssignStep]; rw [clientState_bind_read]
            simp only [htf, ↓reduceIte]; rfl
          refine ⟨fun _ => hsafe, framedTriple_iff_realization.mpr
            ⟨hvh, hcost, ⟨by rw [hst], fun _ _ _ => by rw [hst]⟩, ?_⟩⟩
          rw [hst, hres]
          refine ⟨htfr, hwt, active, rfl, hnd, fun x hx => Nat.lt_succ_of_lt (hlt_k x hx),
            fun x hx => by
              by_cases hxk : x.val < k
              · exact hact_iff x hxk
              · obtain rfl : x = x₀ := Fin.ext (by dsimp only [x₀]; omega)
                exact ⟨fun h => absurd h hf, fun hm => absurd hm hx₀_not⟩,
            hvals, fun x hx => htail x (by omega)⟩)
      ⟨0, 0⟩ s ⟨rfl, hwf, [], rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ => rfl⟩
  obtain ⟨hv, hm, hmod, hfr, hwf', active, hres_eq, hnd_act, _, hact_iff, hvals_act, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hact_len : active.length ≤ n := by simpa only [Fintype.card_fin] using hnd_act.length_le_card
  set itP := iterate compactAssignStep markBase n ⟨0, 0⟩
  have hres1 : ((Memory.spec 0).clientResult s itP).k = n := by rw [hres_eq]
  have hres2 : ((Memory.spec 0).clientResult s itP).count = active.length := by rw [hres_eq]
  refine ⟨hsafe, framedTriple_iff_realization.mpr ⟨hv, hm, hmod, rfl, rfl, hfr, hwf',
    hres1, by omega⟩, hres1, by omega, fun y => active[y.val]'(hres2 ▸ y.isLt),
    fun y₁ y₂ hyeq => Fin.ext (hnd_act.getElem_inj_iff.mp hyeq),
    fun y => (hact_iff _ (active[y.val]'(hres2 ▸ y.isLt)).isLt).mpr (List.getElem_mem _),
    fun x hx => by
      obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp ((hact_iff x x.isLt).mp hx)
      exact ⟨⟨i, hres2.symm ▸ hi⟩, Fin.ext (by simp [hxi])⟩,
    fun y => hvals_act y.val (hres2 ▸ y.isLt)⟩

/-- Eliminate isolated vertices from `g : GraphSlice` in `O(m + n)` memory operations,
returning `⟨edgeBase, numVertices, liftBase⟩` with non-isolated vertices packed into
`Fin numVertices` and `liftBase[u]` holding the dense index for each active `u`. -/
def compactVerticesProg (g : GraphSlice) : Memory.Prog CompactResult := do
  let markB ← Memory.allocBlockDirty g.numVertices
  let _ ← fillConstProg markB.base 0 g.numVertices
  let _ ← iterate compactMarkStep ⟨g.edgeBase, markB.base⟩ g.numEdges 0
  let res ← iterate compactAssignStep markB.base g.numVertices ⟨0, 0⟩
  let outBase ← contractEdgesProg ⟨g.numEdges, g.edgeBase, markB.base⟩
  pure ⟨outBase, res.count, markB.base⟩

private theorem compactVerticesProg_word_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (n + 4 * es.length + 1))) :
    let m := es.length; let markBase := s.frontier; let s₁ : Memory.State := ⟨s.mem, markBase + n⟩
    let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg markBase 0 n)
    let s₃ := (Memory.spec 0).clientState s₂ (iterate compactMarkStep ⟨edgeBase, markBase⟩ m 0)
    let s₄ := (Memory.spec 0).clientState s₃ (iterate compactAssignStep markBase n ⟨0, 0⟩)
    iterationSafe compactMarkStep compactMarkStepSafe w ⟨edgeBase, markBase⟩ m 0 s₂ ∧
    iterationSafe compactAssignStep compactAssignStepSafe w markBase n ⟨0, 0⟩ s₃ ∧
    s₄.frontier = markBase + n ∧
    HoldsIndexedEdges edgeBase es s₄.mem ∧
    Memory.FramedTriple w s (compactVerticesProg ⟨n, m, edgeBase⟩) (14 * m + 3 * n + 2) ∅
      fun res s' =>
        res.liftBase = s.frontier ∧
        res.edgeBase = s.frontier + n ∧
        res.numVertices ≤ n ∧
        s'.frontier = s.frontier + n + 4 * m ∧
        Memory.WellFormed w s' ∧
        ∃ (lift : Fin res.numVertices → Fin n) (esOut : List (IndexedEdge res.numVertices)),
          Function.Injective lift ∧
          esOut.length = m ∧
          HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
          (∀ y : Fin res.numVertices, s'.mem (res.liftBase + (lift y).val) = y.val) ∧
          (∀ y : Fin res.numVertices, ∃ e ∈ esOut, e.u = y ∨ e.v = y) ∧
          esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = es := by
  let m := es.length; let markBase := s.frontier; let fEnd := markBase + n + 4 * m
  let S_all : Set ℕ := Set.Ico markBase fEnd; let s₁ : Memory.State := ⟨s.mem, markBase + n⟩
  have hfit_n1 : Fits w (n + 1) := hfit.of_le (by omega)
  have hfit_m1 : Fits w (m + 1) := by
    by_cases hm0 : m = 0 <;> [exact hm0 ▸ h16.of_le (by decide); exact hfit.of_le (by omega)]
  have hwf₁ : Memory.WellFormed w s₁ :=
    ⟨hfit.of_le (by dsimp only [s₁, markBase]; omega), hwf.mem_fits⟩
  have hft_fill := fillConstProg_spec (base := markBase) (val := 0) (count := n) hwf₁
    (h16.of_le (by decide)) (hfit_n1.of_le (by omega)) (le_refl (markBase + n))
  let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg markBase 0 n)
  obtain ⟨_, _, hmod_fill, hfr_fill, hwf₂, hvals_fill⟩ := framedTriple_iff_realization.mp hft_fill
  have hs2_fr : s₂.frontier = markBase + n := hfr_fill
  have hin_s2 := holdsIndexedEdges_of_ico (s := s₁) hin hmod_fill
    (by dsimp only [markBase]; omega) (by dsimp only [s₁]; omega)
  obtain ⟨hsafe_mark, hft_mark, _, hmark_iff⟩ := compactMark_spec h16 hwf₂ hin_s2
    (by dsimp only [markBase]; omega) (by rw [hs2_fr]) hfit_m1 (fun x => hvals_fill x.val x.isLt)
  let s₃ := (Memory.spec 0).clientState s₂ (iterate compactMarkStep ⟨edgeBase, markBase⟩ m 0)
  obtain ⟨_, _, hmod_mark, _, hfr_mark, hwf₃⟩ := framedTriple_iff_realization.mp hft_mark
  have hs3_fr : s₃.frontier = markBase + n := hfr_mark.trans hs2_fr
  have hin_s3 := holdsIndexedEdges_of_ico hin_s2 hmod_mark
    (by dsimp only [markBase]; omega) (by rw [hs2_fr]; omega)
  obtain ⟨hsafe_ass, hft_ass, _, hca_le, lift, hlift_inj, hlift_mem, hlift_cov, hlift_val⟩ :=
    compactAssign_spec h16 hwf₃ hfit_n1 (by rw [hs3_fr])
  let s₄ := (Memory.spec 0).clientState s₃ (iterate compactAssignStep markBase n ⟨0, 0⟩)
  let resA := (Memory.spec 0).clientResult s₃ (iterate compactAssignStep markBase n ⟨0, 0⟩)
  obtain ⟨_, _, hmod_ass, _, _, hfr_ass, hwf₄, _, _⟩ := framedTriple_iff_realization.mp hft_ass
  have hs4_fr : s₄.frontier = markBase + n := hfr_ass.trans hs3_fr
  have hin_s4 := holdsIndexedEdges_of_ico hin_s3 hmod_ass
    (by dsimp only [markBase]; omega) (by rw [hs3_fr]; omega)
  refine ⟨hsafe_mark, hsafe_ass, hs4_fr, hin_s4, ?_⟩
  have hprog : compactVerticesProg ⟨n, m, edgeBase⟩ =
      (Memory.allocBlockDirty n >>= fun markB => fillConstProg markB.base 0 n >>= fun _ =>
        iterate compactMarkStep ⟨edgeBase, markB.base⟩ m 0 >>= fun _ =>
          iterate compactAssignStep markB.base n ⟨0, 0⟩ >>= fun res =>
            contractEdgesProg ⟨m, edgeBase, markB.base⟩ >>= fun outBase =>
              pure ⟨outBase, res.count, markB.base⟩) := rfl
  rw [hprog]
  let compFn : Fin n → ℕ := fun x => s₄.mem (markBase + x.val)
  have hcomp_lt : ∀ e ∈ es, compFn e.u < resA.count ∧ compFn e.v < resA.count := fun e he => by
    obtain ⟨yu, hyu⟩ := hlift_cov e.u ((hmark_iff e.u).mpr ⟨e, he, .inl rfl⟩)
    obtain ⟨yv, hyv⟩ := hlift_cov e.v ((hmark_iff e.v).mpr ⟨e, he, .inr rfl⟩)
    exact ⟨by dsimp only [compFn]; rw [← hyu, hlift_val yu]; exact yu.isLt,
      by dsimp only [compFn]; rw [← hyv, hlift_val yv]; exact yv.isLt⟩
  have hft_con := contractEdgesProg_spec h16 hwf₄ hin_s4 (by rw [hs4_fr]; omega)
    (fun _ => rfl) (by rw [hs4_fr]) hcomp_lt
    (by rw [hs4_fr]; exact hfit.of_le (by dsimp only [markBase]; omega))
  let Post : CompactResult → Memory.State → Prop := fun res s' =>
    res.liftBase = s.frontier ∧ res.edgeBase = s.frontier + n ∧ res.numVertices ≤ n ∧
    s'.frontier = s.frontier + n + 4 * m ∧ Memory.WellFormed w s' ∧
    ∃ (lift : Fin res.numVertices → Fin n) (esOut : List (IndexedEdge res.numVertices)),
      Function.Injective lift ∧ esOut.length = m ∧ HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
      (∀ y : Fin res.numVertices, s'.mem (res.liftBase + (lift y).val) = y.val) ∧
      (∀ y : Fin res.numVertices, ∃ e ∈ esOut, e.u = y ∨ e.v = y) ∧
      esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = es
  have hcon_pure : Memory.FramedTriple w s₄ (contractEdgesProg ⟨m, edgeBase, markBase⟩ >>=
      fun outBase => pure (⟨outBase, resA.count, markBase⟩ : CompactResult))
      (10 * m + 1 + 0) S_all Post := by
    refine framedTriple_seq_frame hft_con (Set.empty_subset _) (Set.empty_subset _) ?_
    rintro ⟨hout_eq, hfr_s', hwf_s', esOut, hlen_out, hout_mem, hel_out⟩
    set s' := (Memory.spec 0).clientState s₄ (contractEdgesProg ⟨m, edgeBase, markBase⟩)
    have hm_con := (framedTriple_iff_realization.mp hft_con).2.2.1
    refine Memory.FramedTriple.pure ⟨rfl, hout_eq.trans hs4_fr, hca_le, by rw [hfr_s', hs4_fr],
      hwf_s', lift, esOut, hlift_inj, hlen_out, hout_mem, fun y => ?_, fun y => ?_, ?_⟩
    · rw [hm_con.mem_eq_of_not_mem (a := markBase + (lift y).val)
        (by rw [hs4_fr]; have := (lift y).isLt; omega) (Set.notMem_empty _), hlift_val y]
    · obtain ⟨e, he, h_or⟩ := (hmark_iff _).mp (hlift_mem y)
      obtain ⟨i, hi, he_eq⟩ := List.mem_iff_getElem.mp he
      have hi_out : i < esOut.length := hlen_out.symm ▸ hi
      obtain ⟨hu, hv, _, _⟩ := hel_out i hi hi_out
      refine ⟨esOut[i]'hi_out, List.getElem_mem hi_out, h_or.elim
        (fun h_eq => .inl (Fin.ext (by rw [hu, show (es[i]'hi).u = lift y from he_eq ▸ h_eq,
          hlift_val y])))
        (fun h_eq => .inr (Fin.ext (by rw [hv, show (es[i]'hi).v = lift y from he_eq ▸ h_eq,
          hlift_val y])))⟩
    · refine List.ext_getElem (by simp [hlen_out]) fun i hi₁ hi₂ => ?_
      have hi_out : i < esOut.length := by simpa using hi₁
      obtain ⟨hu, hv, hw, hid⟩ := hel_out i hi₂ hi_out
      obtain ⟨yu, hyu⟩ :=
        hlift_cov _ ((hmark_iff _).mpr ⟨es[i]'hi₂, List.getElem_mem hi₂, .inl rfl⟩)
      obtain ⟨yv, hyv⟩ :=
        hlift_cov _ ((hmark_iff _).mpr ⟨es[i]'hi₂, List.getElem_mem hi₂, .inr rfl⟩)
      have hu_fin : lift (esOut[i]'hi_out).u = (es[i]'hi₂).u := by
        rw [show (esOut[i]'hi_out).u = yu from Fin.ext (by rw [hu, ← hyu, hlift_val yu]), hyu]
      have hv_fin : lift (esOut[i]'hi_out).v = (es[i]'hi₂).v := by
        rw [show (esOut[i]'hi_out).v = yv from Fin.ext (by rw [hv, ← hyv, hlift_val yv]), hyv]
      simp only [List.getElem_map]; cases h_es : es[i]'hi₂; rw [h_es] at hu_fin hv_fin hw hid
      simp only [IndexedEdge.mk.injEq]; exact ⟨hu_fin, hv_fin, hw, hid⟩
  have hsub_mn : Set.Ico markBase (markBase + n) ⊆ S_all := fun x hx => by
    simp only [Set.mem_Ico] at hx; simp only [S_all, Set.mem_Ico]; dsimp only [fEnd] at *; omega
  exact ((Memory.FramedTriple.allocBlockDirty_bind
    (hfit.of_le (by omega)) (framedTriple_seq_frame hft_fill hsub_mn le_rfl fun _ =>
      framedTriple_seq_frame hft_mark hsub_mn le_rfl fun ⟨ht, _⟩ => by
        rw [ht]; exact framedTriple_seq_frame hft_ass hsub_mn le_rfl fun ⟨hr, hs', _⟩ => by
          rw [hr, hs']; exact hcon_pure)).frame_empty_of_ge_frontier
    (S := Set.Ico s.frontier fEnd) fun _ ha => ha.1).mono (by omega) fun _ _ h => h

/-- Uniform `Realizes .exact` certificate for `compactVerticesProg` with `work = 0`. -/
theorem realizes_compactVerticesProg :
    Realizes .exact compactVerticesProg WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact compactVerticesProg WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let markBase := s.frontier; let s₁ : Memory.State := ⟨s.mem, markBase + g.numVertices⟩
        let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg markBase 0 g.numVertices)
        let s₃ := (Memory.spec 0).clientState s₂
          (iterate compactMarkStep ⟨g.edgeBase, markBase⟩ g.numEdges 0)
        let s₄ := (Memory.spec 0).clientState s₃
          (iterate compactAssignStep markBase g.numVertices ⟨0, 0⟩)
        Fits w 16 ∧ Fits w (s.frontier + (g.numVertices + 4 * g.numEdges + 1)) ∧
        iterationSafe compactMarkStep compactMarkStepSafe w
          ⟨g.edgeBase, markBase⟩ g.numEdges 0 s₂ ∧
        iterationSafe compactAssignStep compactAssignStepSafe w
          markBase g.numVertices ⟨0, 0⟩ s₃ ∧
        s₄.frontier = markBase + g.numVertices ∧
        ∀ j < g.numEdges,
          g.edgeBase + 4 * j + 3 < s₄.frontier ∧
          markBase + s₄.mem (g.edgeBase + 4 * j) < s₄.frontier ∧
          markBase + s₄.mem (g.edgeBase + 4 * j + 1) < s₄.frontier)
      (fun _ _ => 0) := by
    unfold compactVerticesProg
    realize [realizes_allocBlockDirty, realizes_fillConstProg, realizes_compactMarkStep,
      realizes_compactAssignStep, realizes_contractEdgesProg]
    all_goals
      rcases h with ⟨h16, hfit, hsafe_m, hsafe_a, hs4_fr, hbounds⟩
      first
      | exact h16.of_le (by decide) | exact hbounds
      | (rw [allocDirty_cr, allocDirty_cs]; done)
      | (rw [allocDirty_cr, allocDirty_cs]; dsimp only at *
         first
         | omega | exact hfit.of_le (by rw [hs4_fr]; omega)
         | exact iterationSafe_imp hsafe_m (fun _ => rfl) (fun _ _ hs => hs)
         | exact iterationSafe_imp hsafe_a (fun _ => rfl) (fun _ _ hs => hs))
  refine hraw.consequence (fun w g s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_) (fun _ _ => le_rfl)
  let es := edgesOfMem g.numVertices g.numEdges g.edgeBase s.mem hedges
  have hlen : es.length = g.numEdges := edgesOfMem_length _ _ _ _ _
  obtain ⟨hsafe_m, hsafe_a, hs4_fr, hs4_in, _⟩ := compactVerticesProg_word_spec h16 hmem
    (holdsIndexedEdges_edgesOfMem _ _ _ _ _) (by rw [hlen]; exact hin_lt) (by rw [hlen]; exact hfit)
  let s₁ : Memory.State := ⟨s.mem, s.frontier + g.numVertices⟩
  let s₂ := (Memory.spec 0).clientState s₁ (fillConstProg s.frontier 0 g.numVertices)
  let s₃ := (Memory.spec 0).clientState s₂
    (iterate compactMarkStep ⟨g.edgeBase, s.frontier⟩ g.numEdges 0)
  let s₄ := (Memory.spec 0).clientState s₃
    (iterate compactAssignStep s.frontier g.numVertices ⟨0, 0⟩)
  have hs4_fr' : s₄.frontier = s.frontier + g.numVertices := by simpa [es, hlen] using hs4_fr
  have hs4_in' : HoldsIndexedEdges g.edgeBase es s₄.mem := by simpa [es, hlen] using hs4_in
  refine ⟨h16, hfit, by simpa [es, hlen] using hsafe_m, by simpa [es, hlen] using hsafe_a,
    hs4_fr', fun j hj => ?_⟩
  obtain ⟨hu, hv, _, _⟩ := hs4_in' j (hlen.symm ▸ hj)
  exact ⟨by rw [hs4_fr']; omega,
    by rw [hs4_fr']; exact Nat.add_lt_add_left (hu ▸ (es[j]'(hlen.symm ▸ hj)).u.isLt) _,
    by rw [hs4_fr']; exact Nat.add_lt_add_left (hv ▸ (es[j]'(hlen.symm ▸ hj)).v.isLt) _⟩

/-- Framed specification for `compactVerticesProg`: removes isolated vertices from `es`,
returning `res = ⟨edgeBase, numVertices, liftBase⟩` with an injective vertex embedding `lift`,
remapped `esOut`, and table `s'.mem (res.liftBase + (lift y).val) = y.val`, in at most
`14 * es.length + 3 * n + 2` memory operations. -/
theorem compactVerticesProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (n + 4 * es.length + 1))) :
    Memory.FramedTriple w s (compactVerticesProg ⟨n, es.length, edgeBase⟩)
      (14 * es.length + 3 * n + 2) ∅ fun res s' =>
        res.liftBase = s.frontier ∧
        res.edgeBase = s.frontier + n ∧
        res.numVertices ≤ n ∧
        s'.frontier = s.frontier + n + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        ∃ (lift : Fin res.numVertices → Fin n) (esOut : List (IndexedEdge res.numVertices)),
          Function.Injective lift ∧
          esOut.length = es.length ∧
          HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
          (∀ y : Fin res.numVertices, s'.mem (res.liftBase + (lift y).val) = y.val) ∧
          (∀ y : Fin res.numVertices, ∃ e ∈ esOut, e.u = y ∨ e.v = y) ∧
          esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = es :=
  (compactVerticesProg_word_spec h16 hwf hin hin_lt hfit).2.2.2.2

/-- Vertex compaction preserves graph simplicity (`IsSimple`). -/
theorem compactVertices_isSimple {nOut n : ℕ} {lift : Fin nOut → Fin n}
    {esOut : List (IndexedEdge nOut)} {es : List (IndexedEdge n)}
    (hes : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = es)
    (hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted))) :
    IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) := by
  have hlen_es : es.length = esOut.length := by rw [← hes, List.length_map]
  have hget : ∀ k (hk1 : k < esOut.length) (hk2 : k < es.length),
      (es[k]'hk2).u = lift (esOut[k]'hk1).u ∧ (es[k]'hk2).v = lift (esOut[k]'hk1).v := by
    intro k hk1 hk2; have h := congrArg (fun l => l[k]?) hes
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2,
      Option.map_some, Option.some.injEq] at h
    exact ⟨congrArg IndexedEdge.u h.symm, congrArg IndexedEdge.v h.symm⟩
  rw [isSimple_iff] at hsimp ⊢; refine ⟨fun i hdiag => ?_, fun i₁ i₂ hij => ?_⟩
  · have hi_out : i.val < esOut.length := by simpa only [List.length_map] using i.isLt
    obtain ⟨hu, hv⟩ := hget i.val hi_out (hlen_es ▸ hi_out)
    refine hsimp.1 ⟨i.val, by simpa [hlen_es]⟩ ?_
    simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] at hdiag ⊢
    rw [hu, hv, hdiag]
  · have hi₁ : i₁.val < esOut.length := by simpa only [List.length_map] using i₁.isLt
    have hi₂ : i₂.val < esOut.length := by simpa only [List.length_map] using i₂.isLt
    obtain ⟨hu₁, hv₁⟩ := hget i₁.val hi₁ (hlen_es ▸ hi₁)
    obtain ⟨hu₂, hv₂⟩ := hget i₂.val hi₂ (hlen_es ▸ hi₂)
    have hij_es : edgeEnds (es.map IndexedEdge.toWeighted) ⟨i₁.val, by simpa [hlen_es]⟩ =
        edgeEnds (es.map IndexedEdge.toWeighted) ⟨i₂.val, by simpa [hlen_es]⟩ := by
      simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted] at hij ⊢
      rw [hu₁, hv₁, hu₂, hv₂]; exact congrArg (Sym2.map lift) hij
    exact Fin.ext (Fin.mk.inj (hsimp.2 hij_es))

/-- Vertex compaction along an injective `lift` lifts any MSF `L_out` of the compacted edge list
to an MSF `contractEdgeList lift L_out` of `es`. -/
theorem compactVertices_isMinSpanningForest {nOut n : ℕ}
    {lift : Fin nOut → Fin n} (hlift : Function.Injective lift)
    {esOut : List (IndexedEdge nOut)} {es : List (IndexedEdge n)}
    (hes : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = es)
    {L_out : List (WeightedEdge nOut ℕ)}
    (hL : IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) L_out) :
    IsMinSpanningForest (es.map IndexedEdge.toWeighted) (contractEdgeList lift L_out) := by
  have hcon_es : contractEdgeList lift (esOut.map IndexedEdge.toWeighted) =
      es.map IndexedEdge.toWeighted := by
    rw [← hes]; simp only [contractEdgeList, List.map_map, Function.comp_def, contractEdge,
      IndexedEdge.toWeighted]
  have hpart_con_eq : ∀ L₁ L₂ : List (WeightedEdge nOut ℕ),
      edgePartition L₁ = edgePartition L₂ →
      edgePartition (contractEdgeList lift L₁) = edgePartition (contractEdgeList lift L₂) := by
    intro L₁ L₂ heq; ext u v
    by_cases hu : ∃ x : Fin nOut, lift x = u
    · obtain ⟨x, rfl⟩ := hu; by_cases hv : ∃ y : Fin nOut, lift y = v
      · obtain ⟨y, rfl⟩ := hv
        rw [edgePartition_contractEdgeList_rel_inj hlift L₁ x y,
          edgePartition_contractEdgeList_rel_inj hlift L₂ x y, heq]
      · have hsym : ∀ (p : DisjointSet.Partition n) a b, p.rel a b = p.rel b a :=
          fun p a b => Bool.eq_iff_iff.mpr ⟨p.symm, p.symm⟩
        have hn : ∀ y : Fin nOut, lift y ≠ v := fun y hy => hv ⟨y, hy⟩
        rw [hsym _ (lift x) v, hsym _ (lift x) v,
          edgePartition_contractEdgeList_rel_of_not_mem lift L₁ hn,
          edgePartition_contractEdgeList_rel_of_not_mem lift L₂ hn]
    · have hn : ∀ x : Fin nOut, lift x ≠ u := fun x hx => hu ⟨x, hx⟩
      rw [edgePartition_contractEdgeList_rel_of_not_mem lift L₁ hn,
        edgePartition_contractEdgeList_rel_of_not_mem lift L₂ hn]
  rw [isMinSpanningForest_iff_threshold_partition] at hL ⊢
  refine ⟨⟨by rcases hL.1.1 with ⟨L', hperm, hsub⟩; rw [← hcon_es]
              exact ⟨L'.map (contractEdge lift), hperm.map _, hsub.map _⟩,
    (isAcyclic_contractEdgeList_iff_of_injective hlift L_out).mpr hL.1.2.1,
    hcon_es ▸ hpart_con_eq L_out (esOut.map IndexedEdge.toWeighted) hL.1.2.2⟩, fun t => by
      have hfilt (M : List (WeightedEdge nOut ℕ)) :
          (contractEdgeList lift M).filter (fun e => decide (e.weight ≤ t)) =
          contractEdgeList lift (M.filter fun e => decide (e.weight ≤ t)) := by
        simp only [contractEdgeList, List.filter_map]; rfl
      rw [← hcon_es, hfilt, hfilt]; exact hpart_con_eq _ _ (hL.2 t)⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
