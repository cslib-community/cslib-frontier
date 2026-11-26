/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth
public import CslibFrontier.Computability.Complexity.Classes.NP
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD

/-!
# Checking bandwidth orders of numbered constraint graphs

A witness lists a rank for each vertex in its original list order. The checker verifies the
rank permutation and the span of every pair of ports belonging to the same declared edge.
All scans use explicit input lists, with binary ranks and edge numbers.

## Main definitions

* `AndOrGraph.checkBandwidth`: check a supplied rank array.

## Main results

* `AndOrGraph.exists_checkBandwidth_iff`: accepted rank arrays characterize graph bandwidth.
* `AndOrGraph.computableInPolyTime_checkBandwidth`: the rank verifier is polynomial-time.
* `AndOrGraph.hasBandwidth_mem_NP`: existence of a bounded-bandwidth order is in NP.
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph
open _root_.Turing.MultiTapeTM

/-- Check a rank permutation and the spans of the graph's declared edges. -/
@[expose] def checkBandwidth (g : AndOrGraph) (bound : ℕ) (ranks : List ℕ) : Bool :=
  decide (ranks.length = g.vertices.length) && decide ranks.Nodup &&
    ranks.all (fun r => decide (r < g.vertices.length)) &&
      (g.vertices.zip ranks).all fun u => (g.vertices.zip ranks).all fun v =>
        u.1.ports.all fun p => v.1.ports.all fun q =>
          decide (p.port.edge = q.port.edge ∧ p.port.edge < g.edgeCount →
            u.2 ≤ v.2 + bound ∧ v.2 ≤ u.2 + bound)

private def Span (g : AndOrGraph) (bound : ℕ) (ranks : List ℕ) : Prop :=
  ∀ u v : Fin g.vertices.length, ∀ p ∈ (g.vertices.get u).ports,
    ∀ q ∈ (g.vertices.get v).ports, p.port.edge = q.port.edge →
      p.port.edge < g.edgeCount →
        ranks.getD u.val 0 ≤ ranks.getD v.val 0 + bound ∧
          ranks.getD v.val 0 ≤ ranks.getD u.val 0 + bound

private theorem checkSpan_eq_true_iff (g : AndOrGraph) (bound : ℕ) (ranks : List ℕ)
    (hlen : ranks.length = g.vertices.length) :
    ((g.vertices.zip ranks).all fun u => (g.vertices.zip ranks).all fun v =>
      u.1.ports.all fun p => v.1.ports.all fun q =>
        decide (p.port.edge = q.port.edge ∧ p.port.edge < g.edgeCount →
          u.2 ≤ v.2 + bound ∧ v.2 ≤ u.2 + bound)) = true ↔ Span g bound ranks := by
  have hz : g.vertices.zip ranks = List.ofFn fun i : Fin g.vertices.length =>
      (g.vertices.get i, ranks.getD i.val 0) := by
    refine List.ext_getElem (by simp [hlen]) fun i _ hj => ?_
    have hr : i < ranks.length := by simpa [hlen] using hj
    simp [hr]
  simp only [hz, Span, List.all_eq_true, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, decide_eq_true_eq, and_imp]

private theorem checkBandwidth_eq_true_iff (g : AndOrGraph) (bound : ℕ) (ranks : List ℕ) :
    g.checkBandwidth bound ranks = true ↔ ranks.length = g.vertices.length ∧ ranks.Nodup ∧
      (∀ r ∈ ranks, r < g.vertices.length) ∧ Span g bound ranks := by
  simp only [checkBandwidth, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨hlen, hd⟩, hb⟩, hs⟩ =>
      ⟨hlen, hd, hb, (checkSpan_eq_true_iff g bound ranks hlen).mp
        (by simpa only [List.all_eq_true, decide_eq_true_eq] using hs)⟩,
    fun ⟨hlen, hd, hb, hs⟩ => ⟨⟨⟨hlen, hd⟩, hb⟩,
      by simpa only [List.all_eq_true, decide_eq_true_eq] using
        (checkSpan_eq_true_iff g bound ranks hlen).mpr hs⟩⟩

private theorem hasBandwidth_of_check (g : AndOrGraph) (bound : ℕ) (ranks : List ℕ)
    (h : g.checkBandwidth bound ranks = true) : g.graph.HasBandwidth bound := by
  obtain ⟨hlen, hd, hb, hs⟩ := (checkBandwidth_eq_true_iff g bound ranks).mp h
  have hi (u : Fin g.vertices.length) : u.val < ranks.length := by omega
  let rank (u : Fin g.vertices.length) : Fin g.vertices.length :=
    ⟨ranks.getD u.val 0, by
      rw [List.getD_eq_getElem _ _ (hi u)]
      exact hb _ (List.getElem_mem _)⟩
  have hr : Function.Injective rank := by
    intro u v he
    have he' := congrArg Fin.val he
    change ranks.getD u.val 0 = ranks.getD v.val 0 at he'
    rw [List.getD_eq_getElem _ _ (hi u), List.getD_eq_getElem _ _ (hi v)] at he'
    exact Fin.ext (hd.getElem_inj_iff.mp he')
  refine ⟨{ size := g.vertices.length
            order := Equiv.ofBijective rank ⟨hr, Finite.surjective_of_injective hr⟩
            span := ?_ }⟩
  intro u v p hp q hq he
  have hspan := hs u v (p.map Fin.val) ((g.mem_graph_ports_iff u p).mp hp)
    (q.map Fin.val) ((g.mem_graph_ports_iff v q).mp hq)
    (congrArg Fin.val he) p.port.edge.isLt
  change Nat.dist (ranks.getD u.val 0) (ranks.getD v.val 0) ≤ bound
  simp only [Nat.dist]
  omega

private theorem check_of_certificate (g : AndOrGraph) (bound : ℕ)
    (C : ConstraintGraph.BandwidthCertificate g.graph bound) :
    g.checkBandwidth bound (List.ofFn fun u => (C.order u).val) = true := by
  let ranks := List.ofFn fun u => (C.order u).val
  have hsize : g.vertices.length = C.size := by
    simpa only [Fintype.card_fin] using Fintype.card_congr C.order
  have hget (u : Fin g.vertices.length) : ranks.getD u.val 0 = (C.order u).val := by
    rw [List.getD_eq_getElem _ _ (by simpa only [ranks, List.length_ofFn] using u.isLt)]
    simp only [ranks, List.getElem_ofFn, Fin.eta]
  apply (checkBandwidth_eq_true_iff g bound ranks).mpr
  refine ⟨List.length_ofFn, ?_, ?_, ?_⟩
  · exact List.nodup_ofFn.mpr (Fin.val_injective.comp C.order.injective)
  · intro r hr
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hr
    have hu := (C.order u).isLt
    omega
  · intro u v p hp q hq he hb
    let p' : WeightedPort (Fin g.edgeCount) := ⟨⟨⟨p.port.edge, hb⟩, p.port.dir⟩, p.weight⟩
    let q' : WeightedPort (Fin g.edgeCount) :=
      ⟨⟨⟨q.port.edge, he ▸ hb⟩, q.port.dir⟩, q.weight⟩
    have hp' : p' ∈ (g.graph u).ports := (g.mem_graph_ports_iff u p').mpr hp
    have hq' : q' ∈ (g.graph v).ports := (g.mem_graph_ports_iff v q').mpr hq
    have hspan := C.span u v p' hp' q' hq' (Fin.ext he)
    rw [hget, hget]
    simp only [Nat.dist] at hspan
    omega

/-- A numbered graph has the specified bandwidth exactly when some rank array is accepted. -/
theorem exists_checkBandwidth_iff (g : AndOrGraph) (bound : ℕ) :
    (∃ ranks, g.checkBandwidth bound ranks = true) ↔ g.graph.HasBandwidth bound :=
  ⟨fun ⟨ranks, h⟩ => hasBandwidth_of_check g bound ranks h,
    fun ⟨C⟩ => ⟨_, check_of_certificate g bound C⟩⟩

private theorem computableInPolyTime_spanTest {α : Type} {input : α ↪ List Bool}
    {count a b e f : α → ℕ} (bound : ℕ)
    (hc : ComputableInPolyTime count input encNat)
    (ha : ComputableInPolyTime a input encNat) (hb : ComputableInPolyTime b input encNat)
    (he : ComputableInPolyTime e input encNat) (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun x => decide (e x = f x ∧ e x < count x →
      a x ≤ b x + bound ∧ b x ≤ a x + bound)) input encBool :=
  (ComputableInPolyTime.bool_or'
    (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_and (he.decide_eq' hf) (he.binary_lt' hc)))
    (ComputableInPolyTime.decide_and
      (ha.binary_le' (hb.binary_add' (.const bound)))
      (hb.binary_le' (ha.binary_add' (.const bound))))).of_enc_eq fun _ => by
    simp only [Function.comp_apply, encBool_apply, imp_iff_not_or, Bool.decide_or, decide_not]

private theorem computableInPolyTime_portSpans {α : Type} {input : α ↪ List Bool}
    {left right : α → Vertex ℕ} {count a b : α → ℕ} (bound : ℕ)
    (hl : ComputableInPolyTime left input (encVertex encNat))
    (hr : ComputableInPolyTime right input (encVertex encNat))
    (hc : ComputableInPolyTime count input encNat)
    (ha : ComputableInPolyTime a input encNat) (hb : ComputableInPolyTime b input encNat) :
    ComputableInPolyTime (fun x => (left x).ports.all fun p => (right x).ports.all fun q =>
      decide (p.port.edge = q.port.edge ∧ p.port.edge < count x →
        a x ≤ b x + bound ∧ b x ≤ a x + bound)) input encBool := by
  have ht : ComputableInPolyTime
      (fun z : (α × WeightedPort ℕ) × WeightedPort ℕ =>
        decide (z.1.2.port.edge = z.2.port.edge ∧ z.1.2.port.edge < count z.1.1 →
          a z.1.1 ≤ b z.1.1 + bound ∧ b z.1.1 ≤ a z.1.1 + bound))
      (encPair (encPair input (encWeightedPort encNat)) (encWeightedPort encNat)) encBool :=
    computableInPolyTime_spanTest bound (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop)
  have hi : ComputableInPolyTime (fun z : α × WeightedPort ℕ =>
      (right z.1).ports.all fun q =>
        decide (z.2.port.edge = q.port.edge ∧ z.2.port.edge < count z.1 →
          a z.1 ≤ b z.1 + bound ∧ b z.1 ≤ a z.1 + bound))
      (encPair input (encWeightedPort encNat)) encBool :=
    ComputableInPolyTime.allWithEncoding ht (by fun_prop) (by fun_prop)
  exact ComputableInPolyTime.allWithEncoding hi (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_rankRange :
    ComputableInPolyTime (fun p : AndOrGraph × List ℕ =>
      p.2.all fun r => decide (r < p.1.vertices.length))
      (encPair encAndOrGraph (encList encNat)) encBool := by
  have hn : ComputableInPolyTime (fun p : AndOrGraph × List ℕ => p.1.vertices.length)
      (encPair encAndOrGraph (encList encNat)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have ht : ComputableInPolyTime
      (fun p : (AndOrGraph × List ℕ) × ℕ => decide (p.2 < p.1.1.vertices.length))
      (encPair (encPair encAndOrGraph (encList encNat)) encNat) encBool :=
    ComputableInPolyTime.binary_lt' (by fun_prop) (hn.comp (by fun_prop))
  exact ComputableInPolyTime.allWithEncoding ht (by fun_prop) (by fun_prop)

/-- Checking a supplied array of binary vertex ranks runs in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_checkBandwidth (bound : ℕ) :
    ComputableInPolyTime (fun p : AndOrGraph × List ℕ => p.1.checkBandwidth bound p.2)
      (encPair encAndOrGraph (encList encNat)) encBool := by
  have hd : ComputableInPolyTime (fun p : AndOrGraph × List ℕ => decide p.2.Nodup)
      (encPair encAndOrGraph (encList encNat)) encBool :=
    ComputableInPolyTime.decide_nodup (by fun_prop)
  have hb := computableInPolyTime_rankRange
  let encInput := encPair encAndOrGraph (encList encNat)
  let encRanked := encPair (encVertex encNat) encNat
  let test := fun (x : AndOrGraph × List ℕ) (u v : Vertex ℕ × ℕ) =>
    u.1.ports.all fun p => v.1.ports.all fun q =>
      decide (p.port.edge = q.port.edge ∧ p.port.edge < x.1.edgeCount →
        u.2 ≤ v.2 + bound ∧ v.2 ≤ u.2 + bound)
  have ht : ComputableInPolyTime
      (fun p : ((AndOrGraph × List ℕ) × (Vertex ℕ × ℕ)) × (Vertex ℕ × ℕ) =>
        test p.1.1 p.1.2 p.2)
      (encPair (encPair encInput encRanked) encRanked) encBool :=
    computableInPolyTime_portSpans bound (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop)
  have hz : ComputableInPolyTime (fun p : AndOrGraph × List ℕ => p.1.vertices.zip p.2)
      encInput (encList encRanked) := by fun_prop
  have hi : ComputableInPolyTime
      (fun p : (AndOrGraph × List ℕ) × (Vertex ℕ × ℕ) =>
        (p.1.1.vertices.zip p.1.2).all (test p.1 p.2))
      (encPair encInput encRanked) encBool :=
    ComputableInPolyTime.allWithEncoding ht (by fun_prop) (hz.comp (by fun_prop))
  have hs : ComputableInPolyTime (fun p : AndOrGraph × List ℕ =>
      (p.1.vertices.zip p.2).all fun u => (p.1.vertices.zip p.2).all (test p u))
      encInput encBool :=
    ComputableInPolyTime.allWithEncoding hi (by fun_prop) hz
  unfold checkBandwidth
  fun_prop

/-- Recognizing a bandwidth bound is in NP under the ordinary numbered graph encoding. -/
theorem hasBandwidth_mem_NP (bound : ℕ) :
    {g : AndOrGraph | g.graph.HasBandwidth bound} ∈ NP encAndOrGraph := by
  have heq : {g : AndOrGraph | g.graph.HasBandwidth bound} =
      {g | ∃ ranks, g.checkBandwidth bound ranks = true} :=
    Set.ext fun g => (g.exists_checkBandwidth_iff bound).symm
  rw [heq]
  refine mem_NP_of_witness (p := 2 * Polynomial.X ^ 2 + Polynomial.X) (.list .nat)
    (computableInPolyTime_checkBandwidth bound) (fun _ _ => Iff.rfl) ?_
  intro g ranks h
  obtain ⟨hlen, _, hb, _⟩ := (checkBandwidth_eq_true_iff g bound ranks).mp h
  have hn : g.vertices.length ≤ (encAndOrGraph g).length :=
    (SizedListEncoding.length_le (encA := encVertex encNat) g.vertices).trans
      (encAndOrGraph_vertices_length_le g)
  have hl := length_encList_le encNat ranks fun r hr =>
    (length_encNat_le_self r).trans ((hb r hr).le.trans hn)
  refine ⟨ranks, h, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  rw [hlen] at hl
  nlinarith

end Cslib.Complexity.NCL.AndOrGraph
