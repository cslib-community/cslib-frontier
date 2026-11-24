/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.FineGrained.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Tactic.PolyTime

/-!
# Clause-Grouping Reduction from 3-SAT to Parameterized Clique

This file formalizes the clause-grouping reduction from `ThreeSAT` to `Clique` of Cygan et al.,
*Parameterized Algorithms* (2016-05-30 companion PDF,
https://parameterized-algorithms.mimuw.edu.pl/parameterized-algorithms.pdf).
The nice-tree definitions and Lemma 7.4 are at printed p.161; Theorem 14.21
and its proof are at pp.485–487.
The source proof of Theorem 14.21 groups 3-Coloring vertices; this formalization adapts the
grouping to 3-CNF clauses.
Given a grouping parameter `r ≥ 1` and a 3-CNF formula `φ` with `m = φ.length` clauses,
partitioning `φ` into `r` blocks of at most
`⌈m / r⌉ = (m + r - 1) / r` clauses yields a graph `G` with at most `r * 2 ^ (3 * ⌈m / r⌉)`
vertices (one vertex per satisfying partial assignment to a block, with edges between compatible
assignments in distinct blocks) such that `⟨G, r⟩ ∈ Clique ↔ φ ∈ ThreeSAT`.

Uniformity of the padded polynomial-time reduction over `(r, φ)` gives an
`O(2 ^ (O(m / r)) * poly)` construction whose polynomial exponent `D` is independent of `r`.
The source chooses `r` large to turn an `f(k) * n ^ o(k)` algorithm for `Clique` into a
subexponential-time algorithm for 3-SAT, and so rules out such algorithms under the exponential
time hypothesis. That hypothesis is refuted (`CountingNativeEndpoint.not_ETH`), and `ThreeSAT` is
already decidable in subexponential time in `φ.length`
(`ETH_iff_not_decidableInSubexpTime_length`), so this module states no such transfer. A transfer
to a quantitative rate below the known one is tracked in #5342.

## Main definitions

* `Cslib.Complexity.SAT.groupClique`: the clause-grouping reduction mapping `(r, φ)` to
  `CliqueInstance` with graph `G` and target `r`.

## Main results

* `Cslib.Complexity.SAT.groupClique_mem_Clique_iff`: correctness for all `r ≥ 1` and `φ : CNF ℕ`.
* `Cslib.Complexity.SAT.length_groupClique_vertices_le`:
  `|V(G)| ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r))`.
* `Cslib.Complexity.SAT.exists_computableInO_groupClique`: uniform runtime/size bound in
  `(r, φ)` via `ComputableInPolyTime.exists_computableInO_pad`.

## References

* Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk,
  Michał Pilipczuk, and Saket Saurabh, *Parameterized Algorithms* (2015).
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM

namespace Cslib.Complexity

namespace SAT

namespace GroupClique

/-- Upper bound on the number of clauses in each of `r` contiguous blocks of `φ`. -/
@[expose] def blockSize (φ : CNF ℕ) (r : ℕ) : ℕ :=
  (φ.length + r - 1) / r

/-- The `i`-th contiguous block of at most `blockSize φ r` clauses of `φ`. -/
@[expose] def block (φ : CNF ℕ) (r i : ℕ) : CNF ℕ :=
  (φ.drop (i * blockSize φ r)).take (blockSize φ r)

/-- Compatibility check between partial assignments `a₁` on `vs₁` and `a₂` on `vs₂`. -/
@[expose] def compat (vs₁ vs₂ : List ℕ) (a₁ a₂ : ℕ) : Bool :=
  vs₁.all fun x => !vs₂.contains x || (bitsAssignment vs₁ a₁ x == bitsAssignment vs₂ a₂ x)

/-- Encodes `(i, a)` as a vertex `i * bound + a`. -/
@[expose] def vertex (bound i a : ℕ) : ℕ :=
  i * bound + a

/-- Vertices for block assignments satisfying each block within `bound` codes per block. -/
@[expose] def verticesOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : List ℕ :=
  (List.range r).flatMap fun i =>
    let b := block φ r i
    let vs := b.distinctVars
    ((List.range bound).filter fun a => b.eval (bitsAssignment vs a)).map (vertex bound i)

/-- Edges between compatible satisfying assignments in distinct blocks. -/
@[expose] def edgesOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : List (ℕ × ℕ) :=
  (List.range r).flatMap fun i =>
    let b₁ := block φ r i
    let vs₁ := b₁.distinctVars
    (List.range bound).flatMap fun a =>
      if !b₁.eval (bitsAssignment vs₁ a) then []
      else
        (List.range r).flatMap fun j =>
          if j == i then []
          else
            let b₂ := block φ r j
            let vs₂ := b₂.distinctVars
            ((List.range bound).filter fun b =>
              b₂.eval (bitsAssignment vs₂ b) && compat vs₁ vs₂ a b).map
                fun b => (vertex bound i a, vertex bound j b)

/-- Clique instance with graph and target `r`, using an explicit code bound `bound`. -/
@[expose] def graphOfBound (r : ℕ) (φ : CNF ℕ) (bound : ℕ) : CliqueInstance :=
  if r == 0 then
    ⟨⟨[], []⟩, 1⟩
  else if !φ.all (fun c => decide (c.length ≤ 3)) then
    ⟨⟨[], []⟩, r⟩
  else
    ⟨⟨verticesOfBound r φ bound, edgesOfBound r φ bound⟩, r⟩

end GroupClique

/-- Clause-grouping reduction from `ThreeSAT` to `Clique` with block count `r`. -/
@[expose] def groupClique (r : ℕ) (φ : CNF ℕ) : CliqueInstance :=
  GroupClique.graphOfBound r φ (2 ^ (3 * GroupClique.blockSize φ r))

/-! ### Block cover and variable-count bounds -/

private lemma blockSize_mul_ge {m r : ℕ} (hr : 1 ≤ r) :
    m ≤ r * ((m + r - 1) / r) := by
  have hr0 : 0 < r := hr
  have hdiv := Nat.div_add_mod (m + r - 1) r
  have hmod : (m + r - 1) % r ≤ r - 1 := Nat.lt_succ_iff.mp (by
    have hlt := Nat.mod_lt (m + r - 1) hr0
    omega)
  omega

private lemma mem_block_of_mem {φ : CNF ℕ} {r : ℕ} (hr : 1 ≤ r) {c : Clause ℕ} (hc : c ∈ φ) :
    ∃ i < r, c ∈ GroupClique.block φ r i := by
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨k, hk, rfl⟩
  set B := GroupClique.blockSize φ r
  have hcov : φ.length ≤ r * B := blockSize_mul_ge hr
  have hB : 0 < B := by
    by_contra hB0
    have h0 : B = 0 := Nat.eq_zero_of_not_pos hB0
    rw [h0, Nat.mul_zero] at hcov
    omega
  refine ⟨k / B, ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hk (by simpa [Nat.mul_comm] using hcov))
  · have hk_eq : k / B * B + k % B = k := by
      have hdiv := Nat.div_add_mod k B
      rw [Nat.mul_comm] at hdiv
      exact hdiv
    have hk_mod : k % B < B := Nat.mod_lt k hB
    have hlt_len : k / B * B + k % B < φ.length := by
      rw [hk_eq]
      exact hk
    have hdrop_len : k % B < (φ.drop (k / B * B)).length := by
      rw [List.length_drop]
      omega
    have htake_len : k % B < ((φ.drop (k / B * B)).take B).length := by
      rw [List.length_take]
      exact lt_min hk_mod hdrop_len
    refine List.mem_iff_getElem.mpr ⟨k % B, htake_len, ?_⟩
    dsimp only [GroupClique.block]
    rw [List.getElem_take, List.getElem_drop]
    congr 1

private lemma mem_of_mem_block {φ : CNF ℕ} {r i : ℕ} {c : Clause ℕ}
    (hc : c ∈ GroupClique.block φ r i) : c ∈ φ :=
  List.mem_of_mem_drop (List.mem_of_mem_take hc)

private lemma length_distinctVars_block_le {φ : CNF ℕ} {r i : ℕ}
    (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (GroupClique.block φ r i).distinctVars.length ≤ 3 * GroupClique.blockSize φ r := by
  have h1 := (GroupClique.block φ r i).length_distinctVars
  have h2 := (GroupClique.block φ r i).numVars_le_length_vars
  have h3b : ∀ c ∈ GroupClique.block φ r i, c.length ≤ 3 :=
    fun c hc => h3 c (mem_of_mem_block hc)
  have h4 := CNF.length_vars_le_mul_length h3b
  have h5 : (GroupClique.block φ r i).length ≤ GroupClique.blockSize φ r := by
    dsimp only [GroupClique.block]
    exact List.length_take_le _ _
  omega

/-! ### Vertex and edge characterization -/

private lemma vertex_div {bound i a : ℕ} (ha : a < bound) :
    GroupClique.vertex bound i a / bound = i := by
  rw [GroupClique.vertex, Nat.mul_comm, Nat.mul_add_div (lt_of_le_of_lt (Nat.zero_le a) ha),
    Nat.div_eq_of_lt ha, Nat.add_zero]

private lemma vertex_mod {bound i a : ℕ} (ha : a < bound) :
    GroupClique.vertex bound i a % bound = a := by
  rw [GroupClique.vertex, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

private lemma vertex_inj {bound i₁ a₁ i₂ a₂ : ℕ} (ha₁ : a₁ < bound) (ha₂ : a₂ < bound)
    (h : GroupClique.vertex bound i₁ a₁ = GroupClique.vertex bound i₂ a₂) :
    i₁ = i₂ ∧ a₁ = a₂ := by
  refine ⟨?_, ?_⟩
  · calc
      i₁ = GroupClique.vertex bound i₁ a₁ / bound := (vertex_div ha₁).symm
      _ = GroupClique.vertex bound i₂ a₂ / bound := by rw [h]
      _ = i₂ := vertex_div ha₂
  · calc
      a₁ = GroupClique.vertex bound i₁ a₁ % bound := (vertex_mod ha₁).symm
      _ = GroupClique.vertex bound i₂ a₂ % bound := by rw [h]
      _ = a₂ := vertex_mod ha₂

private lemma mem_verticesOfBound_iff {r : ℕ} {φ : CNF ℕ} {bound v : ℕ} :
    v ∈ GroupClique.verticesOfBound r φ bound ↔
      ∃ i < r, ∃ a < bound,
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
        v = GroupClique.vertex bound i a := by
  simp only [GroupClique.verticesOfBound, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter]
  constructor
  · rintro ⟨i, hi, a, ⟨ha, heval⟩, rfl⟩
    exact ⟨i, hi, a, ha, heval, rfl⟩
  · rintro ⟨i, hi, a, ha, heval, rfl⟩
    exact ⟨i, hi, a, ⟨ha, heval⟩, rfl⟩

/-- `compat vs₁ vs₂ a₁ a₂` holds when the two partial assignments agree on shared variables. -/
private lemma compat_iff {vs₁ vs₂ : List ℕ} {a₁ a₂ : ℕ} :
    GroupClique.compat vs₁ vs₂ a₁ a₂ = true ↔
      ∀ x ∈ vs₁, x ∈ vs₂ → bitsAssignment vs₁ a₁ x = bitsAssignment vs₂ a₂ x := by
  simp only [GroupClique.compat, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, beq_iff_eq, imp_iff_not_or]

private lemma compat_symm {vs₁ vs₂ : List ℕ} {a₁ a₂ : ℕ} :
    GroupClique.compat vs₁ vs₂ a₁ a₂ = true ↔ GroupClique.compat vs₂ vs₁ a₂ a₁ = true := by
  simp only [compat_iff]
  exact ⟨fun h x hx₂ hx₁ => (h x hx₁ hx₂).symm, fun h x hx₁ hx₂ => (h x hx₂ hx₁).symm⟩

private lemma mem_edgesOfBound_iff {r : ℕ} {φ : CNF ℕ} {bound : ℕ} {e : ℕ × ℕ} :
    e ∈ GroupClique.edgesOfBound r φ bound ↔
      ∃ i < r, ∃ a < bound, ∃ j < r, ∃ b < bound,
        j ≠ i ∧
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
        (GroupClique.block φ r j).eval
          (bitsAssignment (GroupClique.block φ r j).distinctVars b) = true ∧
        GroupClique.compat (GroupClique.block φ r i).distinctVars
          (GroupClique.block φ r j).distinctVars a b = true ∧
        e = (GroupClique.vertex bound i a, GroupClique.vertex bound j b) := by
  simp only [GroupClique.edgesOfBound, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, a, ha, ha_mem⟩
    cases he₁ :
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a)
    · simp [he₁] at ha_mem
    · simp only [he₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
        List.mem_range] at ha_mem
      rcases ha_mem with ⟨j, hj, hj_mem⟩
      by_cases hji : j = i
      · simp [hji] at hj_mem
      · have hbeq : (j == i) = false := beq_false_of_ne hji
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter,
          List.mem_range, Bool.and_eq_true] at hj_mem
        rcases hj_mem with ⟨b, ⟨hb, he₂, hcomp⟩, rfl⟩
        exact ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
  · rintro ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
    refine ⟨i, hi, a, ha, ?_⟩
    simp only [he₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
      List.mem_range]
    refine ⟨j, hj, ?_⟩
    have hbeq : (j == i) = false := beq_false_of_ne hji
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter,
      List.mem_range, Bool.and_eq_true]
    exact ⟨b, ⟨hb, he₂, hcomp⟩, rfl⟩

/-- Adjacency between two vertices of the bounded graph: their blocks differ and their partial
assignments are compatible. -/
private lemma adj_vertex_iff {r : ℕ} {φ : CNF ℕ} {bound i j a b : ℕ}
    (ha : a < bound) (hb : b < bound) (hi : i < r) (hj : j < r)
    (hea : (GroupClique.block φ r i).eval
      (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true)
    (heb : (GroupClique.block φ r j).eval
      (bitsAssignment (GroupClique.block φ r j).distinctVars b) = true) :
    (Graph.mk (GroupClique.verticesOfBound r φ bound)
        (GroupClique.edgesOfBound r φ bound)).toSimpleGraph.Adj
        (GroupClique.vertex bound i a) (GroupClique.vertex bound j b) ↔
      i ≠ j ∧ GroupClique.compat (GroupClique.block φ r i).distinctVars
        (GroupClique.block φ r j).distinctVars a b = true := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨-, hedge | hedge⟩
    · obtain ⟨p, -, a', ha', q, -, b', hb', hqp, -, -, hc, he⟩ := mem_edgesOfBound_iff.mp hedge
      obtain ⟨rfl, rfl⟩ := vertex_inj ha ha' (Prod.mk.inj he).1
      obtain ⟨rfl, rfl⟩ := vertex_inj hb hb' (Prod.mk.inj he).2
      exact ⟨Ne.symm hqp, hc⟩
    · obtain ⟨p, -, a', ha', q, -, b', hb', hqp, -, -, hc, he⟩ := mem_edgesOfBound_iff.mp hedge
      obtain ⟨rfl, rfl⟩ := vertex_inj hb ha' (Prod.mk.inj he).1
      obtain ⟨rfl, rfl⟩ := vertex_inj ha hb' (Prod.mk.inj he).2
      exact ⟨hqp, compat_symm.mp hc⟩
  · rintro ⟨hij, hc⟩
    refine ⟨fun h => hij (vertex_inj ha hb h).1, Or.inl ?_⟩
    exact mem_edgesOfBound_iff.mpr ⟨i, hi, a, ha, j, hj, b, hb, Ne.symm hij, hea, heb, hc, rfl⟩

/-- A clique of size `r` in the bounded graph picks one compatible satisfying partial assignment
per block, and these glue to a satisfying assignment of `φ`. -/
private lemma satisfiable_of_mem_Clique {r : ℕ} (hr : 1 ≤ r) {φ : CNF ℕ} {bound : ℕ}
    (h : (⟨⟨GroupClique.verticesOfBound r φ bound, GroupClique.edgesOfBound r φ bound⟩, r⟩ :
      CliqueInstance) ∈ Clique) :
    φ.Satisfiable := by
  rw [mem_Clique_iff_mk] at h
  obtain ⟨S, hSV, hclique⟩ := h
  have hV := fun v hv => mem_verticesOfBound_iff.mp (hSV v hv)
  have hinj : Set.InjOn (fun v => v / bound) S := by
    intro v₁ hv₁ v₂ hv₂ hdiv
    by_contra hne
    obtain ⟨i, hi, a, ha, hea, rfl⟩ := hV v₁ hv₁
    obtain ⟨j, hj, b, hb, heb, rfl⟩ := hV v₂ hv₂
    have hij := ((adj_vertex_iff ha hb hi hj hea heb).mp (hclique.1 hv₁ hv₂ hne)).1
    simp only [vertex_div ha, vertex_div hb] at hdiv
    exact hij hdiv
  have himg : S.image (fun v => v / bound) = Finset.range r := by
    refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨i', hi', a', ha', -, rfl⟩ := hV v hv
      simpa only [vertex_div ha', Finset.mem_range] using hi'
    · rw [Finset.card_image_of_injOn hinj, hclique.2, Finset.card_range]
  have hpick : ∀ i < r, ∃ a < bound, (GroupClique.block φ r i).eval
      (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
      GroupClique.vertex bound i a ∈ S := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (himg ▸ Finset.mem_range.mpr hi)
    obtain ⟨i', -, a, ha, hea, rfl⟩ := hV v hv
    rw [vertex_div ha] at hvi
    subst hvi
    exact ⟨a, ha, hea, hv⟩
  choose! code hcode_lt hcode_eval hcode_mem using hpick
  have hagree : ∀ i < r, ∀ j < r, ∀ x ∈ (GroupClique.block φ r i).distinctVars,
      x ∈ (GroupClique.block φ r j).distinctVars →
      bitsAssignment (GroupClique.block φ r i).distinctVars (code i) x =
        bitsAssignment (GroupClique.block φ r j).distinctVars (code j) x := by
    intro i hi j hj x hxi hxj
    by_cases hij : i = j
    · subst hij
      rfl
    · have hne : GroupClique.vertex bound i (code i) ≠ GroupClique.vertex bound j (code j) :=
        fun h => hij (vertex_inj (hcode_lt i hi) (hcode_lt j hj) h).1
      have hc := ((adj_vertex_iff (hcode_lt i hi) (hcode_lt j hj) hi hj (hcode_eval i hi)
        (hcode_eval j hj)).mp (hclique.1 (hcode_mem i hi) (hcode_mem j hj) hne)).2
      exact compat_iff.mp hc x hxi hxj
  classical
  let τ : ℕ → Bool := fun x =>
    if hx : ∃ i < r, x ∈ (GroupClique.block φ r i).distinctVars then
      bitsAssignment (GroupClique.block φ r (Nat.find hx)).distinctVars (code (Nat.find hx)) x
    else false
  have hτ : ∀ i < r, ∀ x ∈ (GroupClique.block φ r i).distinctVars,
      bitsAssignment (GroupClique.block φ r i).distinctVars (code i) x = τ x := by
    intro i hi x hx
    have hex : ∃ i < r, x ∈ (GroupClique.block φ r i).distinctVars := ⟨i, hi, hx⟩
    simp only [τ, hex, ↓reduceDIte]
    exact hagree i hi _ (Nat.find_spec hex).1 x hx (Nat.find_spec hex).2
  refine ⟨τ, (CNF.eval_eq_true_iff _ _).mpr fun c hc => ?_⟩
  obtain ⟨i, hi, hci⟩ := mem_block_of_mem hr hc
  have hblock : (GroupClique.block φ r i).eval τ = true :=
    (CNF.eval_congr fun x hx => hτ i hi x (CNF.mem_distinctVars.mpr hx)).symm.trans
      (hcode_eval i hi)
  exact (CNF.eval_eq_true_iff _ _).mp hblock c hci

/-- A satisfying assignment of `φ` restricts to one satisfying code per block; these `r`
vertices form a clique in the bounded graph once `bound` covers every block's codes. -/
private lemma mem_Clique_of_satisfiable {r : ℕ} {φ : CNF ℕ} {bound : ℕ}
    (hbound : ∀ i, 2 ^ (GroupClique.block φ r i).distinctVars.length ≤ bound)
    (hφ : φ.Satisfiable) :
    (⟨⟨GroupClique.verticesOfBound r φ bound, GroupClique.edgesOfBound r φ bound⟩, r⟩ :
      CliqueInstance) ∈ Clique := by
  obtain ⟨τ, hτ⟩ := hφ
  choose code hcode_lt hcode_eq using fun i =>
    exists_lt_two_pow_bitsAssignment_eq (vs := (GroupClique.block φ r i).distinctVars) τ
  have hcode_bound : ∀ i, code i < bound := fun i => (hcode_lt i).trans_le (hbound i)
  have hcode_eval : ∀ i, (GroupClique.block φ r i).eval
      (bitsAssignment (GroupClique.block φ r i).distinctVars (code i)) = true := fun i =>
    (CNF.eval_congr fun x hx => hcode_eq i x (CNF.mem_distinctVars.mpr hx)).trans
      ((CNF.eval_eq_true_iff _ _).mpr fun c hc =>
        (CNF.eval_eq_true_iff _ _).mp hτ c (mem_of_mem_block hc))
  let f : ℕ → ℕ := fun i => GroupClique.vertex bound i (code i)
  have hf_inj : Set.InjOn f (Finset.range r) := fun i _ j _ hij =>
    (vertex_inj (hcode_bound i) (hcode_bound j) hij).1
  rw [mem_Clique_iff_mk]
  refine ⟨(Finset.range r).image f, fun v hv => ?_, ⟨fun u hu v hv huv => ?_, ?_⟩⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact mem_verticesOfBound_iff.mpr
      ⟨i, Finset.mem_range.mp hi, code i, hcode_bound i, hcode_eval i, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    refine (adj_vertex_iff (hcode_bound i) (hcode_bound j) (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) (hcode_eval i) (hcode_eval j)).mpr
      ⟨fun h => huv (by rw [h]), compat_iff.mpr fun x hxi hxj => ?_⟩
    rw [hcode_eq i x hxi, hcode_eq j x hxj]
  · rw [Finset.card_image_of_injOn hf_inj, Finset.card_range]

/-! ### Correctness and vertex-count bounds -/

/-- For every `r ≥ 1` and `φ : CNF ℕ`, `SAT.groupClique r φ` sets target clique size `r`. -/
theorem groupClique_snd {r : ℕ} (hr : 1 ≤ r) (φ : CNF ℕ) :
    (groupClique r φ).m = r := by
  have hr0 : (r == 0) = false := beq_false_of_ne (by omega)
  simp only [groupClique, GroupClique.graphOfBound, hr0, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

/-- Vertex list length bound: `|V(SAT.groupClique r φ)| ≤ r * 2 ^ (3 * ⌈|φ| / r⌉)`. -/
theorem length_groupClique_vertices_le (r : ℕ) (φ : CNF ℕ) :
    let graph := (groupClique r φ).graph
    let verts := graph.vertices
    verts.length ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r)) := by
  dsimp only
  rw [groupClique, GroupClique.graphOfBound]
  by_cases hr0 : (r == 0) = true
  · simp [hr0]
  · simp only [hr0, Bool.false_eq_true, ↓reduceIte]
    by_cases h3 : (!φ.all fun c => decide (c.length ≤ 3)) = true
    · simp [h3]
    · simp only [h3, Bool.false_eq_true, ↓reduceIte]
      have hlen : (GroupClique.verticesOfBound r φ
          (2 ^ (3 * GroupClique.blockSize φ r))).length ≤
          (List.range r).length * 2 ^ (3 * GroupClique.blockSize φ r) := by
        apply List.length_flatMap_le
        intro i _
        rw [List.length_map]
        calc
          ((List.range (2 ^ (3 * GroupClique.blockSize φ r))).filter _).length ≤
              (List.range (2 ^ (3 * GroupClique.blockSize φ r))).length :=
            List.length_filter_le _ _
          _ = 2 ^ (3 * GroupClique.blockSize φ r) := List.length_range
      simpa [List.length_range, GroupClique.blockSize] using hlen

/-- Vertex finset cardinality bound for `SAT.groupClique r φ`. -/
theorem card_groupClique_vertices_le (r : ℕ) (φ : CNF ℕ) :
    let graph := (groupClique r φ).graph
    let verts := graph.vertices
    verts.toFinset.card ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r)) :=
  le_trans (List.toFinset_card_le _) (length_groupClique_vertices_le r φ)

/-- Soundness and completeness of `SAT.groupClique`: for every `r ≥ 1` and `φ : CNF ℕ`,
`SAT.groupClique r φ ∈ Clique ↔ φ ∈ ThreeSAT`. -/
theorem groupClique_mem_Clique_iff {r : ℕ} (hr : 1 ≤ r) (φ : CNF ℕ) :
    groupClique r φ ∈ Clique ↔ φ ∈ ThreeSAT := by
  have hr0 : (r == 0) = false := beq_false_of_ne (by omega)
  by_cases h3 : ∀ c ∈ φ, c.length ≤ 3
  · have hnot : (!φ.all fun c => decide (c.length ≤ 3)) = false := by
      simpa only [Bool.not_eq_false', List.all_eq_true, decide_eq_true_eq] using h3
    simp only [groupClique, GroupClique.graphOfBound, hr0, hnot, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun h => ⟨h3, satisfiable_of_mem_Clique hr h⟩,
      fun h => mem_Clique_of_satisfiable (fun i => ?_) h.2⟩
    exact Nat.pow_le_pow_right (by omega) (length_distinctVars_block_le h3)
  · have hnot : (!φ.all fun c => decide (c.length ≤ 3)) = true := by
      simpa only [Bool.not_eq_true', List.all_eq_false, decide_eq_true_eq, not_le,
        not_forall, not_le, exists_prop] using h3
    simp only [groupClique, GroupClique.graphOfBound, hr0, hnot, Bool.false_eq_true, ↓reduceIte,
      mem_Clique_iff_mk]
    refine ⟨fun ⟨S, hSV, hclique⟩ => ?_, fun h => absurd h.1 h3⟩
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (hclique.2 ▸ hr)
    exact absurd (hSV v hv) List.not_mem_nil

/-! ### Polynomial-time computability of the bounded builder -/

@[local program_certificate]
private theorem computableInPolyTime_blockSize {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.blockSize (φ g) (r g)) encIn encUnary := by
  have hlen := SAT.computableInPolyTime_length hφ
  polytime [GroupClique.blockSize]

@[local program_certificate]
private theorem computableInPolyTime_block {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r i : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.block (φ g) (r g) (i g)) encIn encCNF := by
  polytime [GroupClique.block]

@[local program_certificate]
private theorem computableInPolyTime_compat {γ : Type} {encIn : γ ↪ List Bool}
    {vs₁ vs₂ : γ → List ℕ} {a₁ a₂ : γ → ℕ}
    (hvs₁ : ComputableInPolyTime vs₁ encIn (encList encNat))
    (hvs₂ : ComputableInPolyTime vs₂ encIn (encList encNat))
    (ha₁ : ComputableInPolyTime a₁ encIn encNat)
    (ha₂ : ComputableInPolyTime a₂ encIn encNat) :
    ComputableInPolyTime
      (fun g => GroupClique.compat (vs₁ g) (vs₂ g) (a₁ g) (a₂ g)) encIn encBool := by
  polytime [GroupClique.compat, bitsAssignment]

@[local program_certificate]
private theorem computableInPolyTime_evalBlock {γ : Type} {encIn : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {r i a : γ → ℕ}
    (hφ : ComputableInPolyTime φ encIn encCNF)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime
      (fun g =>
        (GroupClique.block (φ g) (r g) (i g)).eval
          (bitsAssignment (GroupClique.block (φ g) (r g) (i g)).distinctVars (a g)))
      encIn encBool :=
  computableInPolyTime_eval_bitsAssignment.comp
    (((computableInPolyTime_block hφ hr hi).prod
      (SAT.computableInPolyTime_distinctVars.comp (computableInPolyTime_block hφ hr hi))).prod
      (ComputableInPolyTime.unary_to_binary.comp ha))

@[local program_certificate]
private theorem computableInPolyTime_vertex {γ : Type} {encIn : γ ↪ List Bool}
    {bound i a : γ → ℕ}
    (hb : ComputableInPolyTime bound encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun g => GroupClique.vertex (bound g) (i g) (a g)) encIn encNat :=
  ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.unary_to_binary.comp hi)
      (ComputableInPolyTime.unary_to_binary.comp hb))
    (ComputableInPolyTime.unary_to_binary.comp ha)

@[local program_certificate]
private theorem computableInPolyTime_verticesOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.verticesOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) (encList encNat) := by
  polytime [GroupClique.verticesOfBound]

@[local program_certificate]
private theorem computableInPolyTime_edgesOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.edgesOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) (encList (encPair encNat encNat)) := by
  polytime [GroupClique.edgesOfBound]

private theorem computableInPolyTime_graphOfBound :
    ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => GroupClique.graphOfBound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encCNF) encUnary) encCliqueInstance := by
  unfold GroupClique.graphOfBound
  have h3 : ComputableInPolyTime
      (fun p : (ℕ × CNF ℕ) × ℕ => !p.1.2.all fun c => decide (c.length ≤ 3))
      (encPair (encPair encUnary encCNF) encUnary) encBool :=
    ComputableInPolyTime.bool_not.comp ((computableInPolyTime_all_length_le 3).comp (by polytime))
  refine ComputableInPolyTime.ite_decide
    (by simpa only [Bool.decide_eq_true] using
      (by polytime : ComputableInPolyTime (fun p : (ℕ × CNF ℕ) × ℕ => p.1.1 == 0) _ encBool))
    (ComputableInPolyTime.const _)
    (ComputableInPolyTime.ite_decide (by simpa only [Bool.decide_eq_true] using h3) ?_ ?_)
  · exact encCliqueInstance_mk_polyTime (ComputableInPolyTime.const _) (by polytime)
  · exact encCliqueInstance_mk_polyTime
      (encGraph_mk_polyTime computableInPolyTime_verticesOfBound computableInPolyTime_edgesOfBound)
      (by polytime)

/-- Uniform runtime and output-size bound for `(r, φ) ↦ SAT.groupClique r φ`: the exponential
exponent scales linearly in `3 * ((φ.length + r - 1) / r)` with polynomial degree `D` independent
of `r`. -/
theorem exists_computableInO_groupClique :
    ∃ C D : ℕ,
      ComputableInO (fun p : ℕ × CNF ℕ => groupClique p.1 p.2)
        (encPair encUnary encCNF) encCliqueInstance
        (fun p => C * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
          ((encPair encUnary encCNF p).length + 1) ^ D)
        (fun p => C * 2 ^ (D * (3 * GroupClique.blockSize p.2 p.1)) *
          ((encPair encUnary encCNF p).length + 1) ^ D) := by
  let encBase := encPair encUnary encCNF
  have hν :
      ComputableInPolyTime (fun p : ℕ × CNF ℕ => 3 * GroupClique.blockSize p.2 p.1)
        encBase encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 3)
      (computableInPolyTime_blockSize
        (ComputableInPolyTime.snd encUnary encCNF)
        (ComputableInPolyTime.fst encUnary encCNF))
  exact ComputableInPolyTime.exists_computableInO_pad computableInPolyTime_graphOfBound hν

end SAT

end Cslib.Complexity
