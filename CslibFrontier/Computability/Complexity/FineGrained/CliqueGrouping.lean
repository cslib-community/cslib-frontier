/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.LogTwoRpow
import CslibFrontier.Logics.Propositional.CNF.ModelCount.DenseRelabel
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime

/-!
# Clause-Grouping Reduction from 3-SAT to Parameterized Clique

This file formalizes the clause-grouping reduction from `ThreeSAT` to `Clique` of Cygan et al.,
*Parameterized Algorithms* (2016-05-30 companion PDF,
https://parameterized-algorithms.mimuw.edu.pl/parameterized-algorithms.pdf).
The proof of Theorem 14.21 (printed pp. 485–487) groups 3-Coloring vertices. Here the reduction
groups 3-CNF clauses.
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
Under `SH`, an input-dependent block count rules out a fixed power saving in the target exponent
when the prefactor is exponential in a fixed power of the target clique size.

## Main definitions

* `Cslib.Complexity.SAT.groupClique`: the clause-grouping reduction mapping `(r, φ)` to
  `CliqueInstance` with graph `G` and target `r`.

## Main results

* `Cslib.Complexity.SAT.groupClique_mem_Clique_iff`: correctness for all `r ≥ 1` and `φ : CNF ℕ`.
* `Cslib.Complexity.SAT.length_groupClique_vertices_le`:
  `|V(G)| ≤ r * 2 ^ (3 * ((φ.length + r - 1) / r))`.
* `Cslib.Complexity.SAT.exists_computableInO_groupClique`: uniform runtime/size bound in
  `(r, φ)` via `ComputableInPolyTime.exists_computableInO_pad`.

* `Cslib.Complexity.SH.not_clique_powerEnc`, `Cslib.Complexity.SH.not_clique_powerVertex`:
  fixed-power lower bounds under SH in the encoded-length and vertex-count formulations.

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
  have := Nat.div_add_mod (m + r - 1) r
  have := Nat.mod_lt (m + r - 1) hr
  omega

private lemma mem_block_of_mem {φ : CNF ℕ} {r : ℕ} (hr : 1 ≤ r) {c : Clause ℕ} (hc : c ∈ φ) :
    ∃ i < r, c ∈ GroupClique.block φ r i := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  set B := GroupClique.blockSize φ r with hB_def
  have hcov : φ.length ≤ r * B := blockSize_mul_ge hr
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hcov; omega
  have hk_eq : k / B * B + k % B = k := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod k B
  have htake_len : k % B < ((φ.drop (k / B * B)).take B).length := by
    rw [List.length_take, List.length_drop]
    exact lt_min (Nat.mod_lt k hB) (by omega)
  refine ⟨k / B, Nat.div_lt_of_lt_mul (hk.trans_le (by simpa [Nat.mul_comm] using hcov)),
    List.mem_iff_getElem.mpr ⟨k % B, htake_len, ?_⟩⟩
  simp only [GroupClique.block, ← hB_def, List.getElem_take, List.getElem_drop, hk_eq]

private lemma mem_of_mem_block {φ : CNF ℕ} {r i : ℕ} {c : Clause ℕ}
    (hc : c ∈ GroupClique.block φ r i) : c ∈ φ :=
  List.mem_of_mem_drop (List.mem_of_mem_take hc)

private lemma length_distinctVars_block_le {φ : CNF ℕ} {r i : ℕ}
    (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (GroupClique.block φ r i).distinctVars.length ≤ 3 * GroupClique.blockSize φ r := by
  have h1 := (GroupClique.block φ r i).length_distinctVars
  have h2 := (GroupClique.block φ r i).numVars_le_length_vars
  have h4 := CNF.length_vars_le_mul_length (φ := GroupClique.block φ r i)
    fun c hc => h3 c (mem_of_mem_block hc)
  have h5 : (GroupClique.block φ r i).length ≤ GroupClique.blockSize φ r :=
    List.length_take_le _ _
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
    i₁ = i₂ ∧ a₁ = a₂ :=
  ⟨by rw [← vertex_div (i := i₁) ha₁, h, vertex_div ha₂],
    by rw [← vertex_mod (i := i₁) ha₁, h, vertex_mod ha₂]⟩

private lemma mem_verticesOfBound_iff {r : ℕ} {φ : CNF ℕ} {bound v : ℕ} :
    v ∈ GroupClique.verticesOfBound r φ bound ↔
      ∃ i < r, ∃ a < bound,
        (GroupClique.block φ r i).eval
          (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
        v = GroupClique.vertex bound i a := by
  simp only [GroupClique.verticesOfBound, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter]
  exact ⟨fun ⟨i, hi, a, ⟨ha, heval⟩, hv⟩ => ⟨i, hi, a, ha, heval, hv.symm⟩,
    fun ⟨i, hi, a, ha, heval, hv⟩ => ⟨i, hi, a, ⟨ha, heval⟩, hv.symm⟩⟩

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
      · simp only [beq_false_of_ne hji, Bool.false_eq_true, ↓reduceIte, List.mem_map,
          List.mem_filter, List.mem_range, Bool.and_eq_true] at hj_mem
        rcases hj_mem with ⟨b, ⟨hb, he₂, hcomp⟩, rfl⟩
        exact ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
  · rintro ⟨i, hi, a, ha, j, hj, b, hb, hji, he₁, he₂, hcomp, rfl⟩
    refine ⟨i, hi, a, ha, ?_⟩
    simp only [he₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
      List.mem_range]
    refine ⟨j, hj, ?_⟩
    simp only [beq_false_of_ne hji, Bool.false_eq_true, ↓reduceIte, List.mem_map,
      List.mem_filter, List.mem_range, Bool.and_eq_true]
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
  obtain ⟨S, hSV, hclique⟩ := mem_Clique_iff_mk.mp h
  have hV := fun v hv => mem_verticesOfBound_iff.mp (hSV v hv)
  have hinj : Set.InjOn (fun v => v / bound) S := by
    intro v₁ hv₁ v₂ hv₂ hdiv
    by_contra hne
    obtain ⟨i, hi, a, ha, hea, rfl⟩ := hV v₁ hv₁
    obtain ⟨j, hj, b, hb, heb, rfl⟩ := hV v₂ hv₂
    exact ((adj_vertex_iff ha hb hi hj hea heb).mp (hclique.isClique hv₁ hv₂ hne)).1
      (by simpa only [vertex_div ha, vertex_div hb] using hdiv)
  have himg : S.image (fun v => v / bound) = Finset.range r := by
    refine Finset.eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨i', hi', a', ha', -, rfl⟩ := hV v hv
      simpa only [vertex_div ha', Finset.mem_range] using hi'
    · rw [Finset.card_image_of_injOn hinj, hclique.card_eq, Finset.card_range]
  have hpick : ∀ i < r, ∃ a < bound, (GroupClique.block φ r i).eval
      (bitsAssignment (GroupClique.block φ r i).distinctVars a) = true ∧
      GroupClique.vertex bound i a ∈ S := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (himg ▸ Finset.mem_range.mpr hi)
    obtain ⟨i', -, a, ha, hea, rfl⟩ := hV v hv
    exact (vertex_div ha ▸ hvi) ▸ ⟨a, ha, hea, hv⟩
  choose! code hcode_lt hcode_eval hcode_mem using hpick
  have hagree : ∀ i < r, ∀ j < r, ∀ x ∈ (GroupClique.block φ r i).distinctVars,
      x ∈ (GroupClique.block φ r j).distinctVars →
      bitsAssignment (GroupClique.block φ r i).distinctVars (code i) x =
        bitsAssignment (GroupClique.block φ r j).distinctVars (code j) x := by
    intro i hi j hj x hxi hxj
    by_cases hij : i = j
    · exact hij ▸ rfl
    · have hne : GroupClique.vertex bound i (code i) ≠ GroupClique.vertex bound j (code j) :=
        fun h => hij (vertex_inj (hcode_lt i hi) (hcode_lt j hj) h).1
      have hc := ((adj_vertex_iff (hcode_lt i hi) (hcode_lt j hj) hi hj (hcode_eval i hi)
        (hcode_eval j hj)).mp (hclique.isClique (hcode_mem i hi) (hcode_mem j hj) hne)).2
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
  split_ifs
  · simp
  · simp
  · have hlen : (GroupClique.verticesOfBound r φ
        (2 ^ (3 * GroupClique.blockSize φ r))).length ≤
        (List.range r).length * 2 ^ (3 * GroupClique.blockSize φ r) :=
      List.length_flatMap_le fun i _ => by
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
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (hclique.card_eq ▸ hr)
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

private lemma blockSize_real_le {m r : ℕ} (hr : 1 ≤ r) :
    (((m + r - 1) / r : ℕ) : ℝ) ≤ (m : ℝ) / (r : ℝ) + 1 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_add_one hr0.ne', le_div_iff₀ hr0]
  exact_mod_cast (Nat.div_mul_le_self (m + r - 1) r).trans (by omega)

end SAT

/-- A graph instance has no more declared vertices than the length of its encoding. -/
private lemma length_vertices_le_encCliqueInstance (x : CliqueInstance) :
    x.graph.vertices.length ≤ (encCliqueInstance x).length := by
  have h := length_le_encPair_left encGraph encNat (x.graph, x.m)
  rw [encCliqueInstance_apply]
  exact x.graph.length_vertices_le_encGraph.trans h

/-! ### Fixed-power bounds for parameterized Clique under SH -/

namespace SAT

/-- Relabel valid width-three formulas densely. Replace rejected widths with an empty clause so
both the input to the grouping compiler and its output have size controlled by the clause count. -/
private def prepareCliqueCNF (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then φ.denseRelabel else [[]]

private theorem prepareCliqueCNF_mem_iff (φ : CNF ℕ) :
    prepareCliqueCNF φ ∈ ThreeSAT ↔ φ ∈ ThreeSAT := by
  unfold prepareCliqueCNF
  split_ifs with hw
  · simp only [ThreeSAT, Set.mem_ofPred_eq, CNF.all_length_le_denseRelabel,
      CNF.satisfiable_denseRelabel]
  · have hwidth : ¬∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
    have hfalse : ([[]] : CNF ℕ) ∉ ThreeSAT := by
      rintro ⟨_, σ, hσ⟩
      simp at hσ
    exact ⟨fun h => (hfalse h).elim, fun h => (hwidth h.1).elim⟩

private theorem computableInPolyTime_prepareCliqueCNF :
    ComputableInPolyTime prepareCliqueCNF encCNF encCNF :=
  ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
    computableInPolyTime_denseRelabel (ComputableInPolyTime.const _)

private theorem length_enc_prepareCliqueCNF_le (φ : CNF ℕ) :
    (encCNF (prepareCliqueCNF φ)).length + 1 ≤ 128 * (φ.length + 1) ^ 2 := by
  unfold prepareCliqueCNF
  split_ifs with hw
  · have hwidth : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
    have hv := φ.numVars_le_length_vars.trans (CNF.length_vars_le_mul_length hwidth)
    let n := φ.length + 1
    have hclause (c : Clause ℕ) (hc : c ∈ φ.denseRelabel) :
        (encList (encPair encNat encBool) c).length ≤ 51 * n := by
      have hlen := (CNF.all_length_le_denseRelabel φ).mpr hwidth c hc
      have henc := length_encList_le (encPair encNat encBool) c (b := 6 * n + 2)
        fun l hl => by
          have hvar := φ.mem_vars_denseRelabel_lt (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)
          have hbits := (Nat.size_le_self l.1).trans (hvar.le.trans hv)
          rw [length_encPair, length_encNat_eq_size, encBool_apply, List.length_singleton]
          omega
      exact henc.trans (by
        have := Nat.mul_le_mul_right (2 * (6 * n + 2) + 1) hlen
        dsimp only [n] at *
        omega)
    have henc := length_encList_le (encList (encPair encNat encBool)) φ.denseRelabel hclause
    change (encList (encList (encPair encNat encBool)) φ.denseRelabel).length + 1 ≤ _
    rw [CNF.length_denseRelabel] at henc
    dsimp only [n] at henc
    nlinarith only [henc, Nat.zero_le φ.length, Nat.zero_le (φ.length ^ 2)]
  · have hconst : (encCNF ([[]] : CNF ℕ)).length + 1 ≤ 128 := by decide
    calc
      _ ≤ 128 * 1 := hconst
      _ ≤ _ := Nat.mul_le_mul_left 128 (Nat.one_le_pow _ _ (by omega))

/-- Round a fixed small power of the positive clause count upward to a power of two. -/
private def powerBlockCount (d m : ℕ) : ℕ := 2 ^ Nat.clog (2 ^ d) (m + 1)

private theorem one_le_powerBlockCount (d m : ℕ) : 1 ≤ powerBlockCount d m :=
  Nat.one_le_two_pow

private theorem powerBlockCount_bounds {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (m + 1 : ℝ) ^ (1 / (d : ℝ)) ≤ 2 * powerBlockCount d m ∧
    (powerBlockCount d m : ℝ) ≤ 2 * (m + 1 : ℝ) ^ (1 / (d : ℝ)) := by
  have hb : 1 < (2 : ℕ) ^ d := (by decide : 1 < (2 : ℕ) ^ 1).trans_le
    (Nat.pow_le_pow_right two_pos (by omega))
  have hlog : Real.logb (((2 : ℕ) ^ d : ℕ) : ℝ) ((2 : ℕ) : ℝ) = 1 / (d : ℝ) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb, Real.log_pow]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have htwo : ((2 : ℕ) : ℝ) = 2 := by norm_num
  constructor
  · have hlower := Nat.rpow_logb_le_mul_pow_log (a := 2) hb (by decide) (m + 1)
    rw [hlog, htwo, Nat.cast_succ] at hlower
    refine hlower.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have hbound : (2 : ℕ) ^ Nat.log (2 ^ d) (m + 1) ≤ powerBlockCount d m :=
      Nat.pow_le_pow_right two_pos (Nat.log_le_clog (2 ^ d) (m + 1))
    exact_mod_cast hbound
  · have hupper := Nat.pow_clog_le_mul_rpow_logb (a := 2) (n := m + 1) hb (by decide)
      (Nat.succ_ne_zero _)
    rw [hlog, htwo, Nat.cast_succ] at hupper
    exact hupper

private theorem computableInPolyTime_powerBlockCount (d : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => powerBlockCount d φ.length) encCNF encUnary := by
  have hlen := SAT.computableInPolyTime_length
    (show ComputableInPolyTime (fun φ : CNF ℕ => φ) encCNF encCNF from ComputableInPolyTime.id')
  exact ComputableInPolyTime.unary_pow_clog_const
    (ComputableInPolyTime.unary_add' hlen (ComputableInPolyTime.const 1)) 2 (2 ^ d)

private def powerGroupingInput (d : ℕ) (φ : CNF ℕ) : ℕ × CNF ℕ :=
  (powerBlockCount d φ.length, prepareCliqueCNF φ)

private def powerGrouping (d : ℕ) (φ : CNF ℕ) : CliqueInstance :=
  groupClique (powerGroupingInput d φ).1 (powerGroupingInput d φ).2

private theorem powerGrouping_mem_iff (d : ℕ) (φ : CNF ℕ) :
    φ ∈ ThreeSAT ↔ powerGrouping d φ ∈ Clique :=
  (prepareCliqueCNF_mem_iff φ).symm.trans
    (groupClique_mem_Clique_iff (one_le_powerBlockCount d φ.length) (prepareCliqueCNF φ)).symm

private theorem powerGrouping_m (d : ℕ) (φ : CNF ℕ) :
    (powerGrouping d φ).m = powerBlockCount d φ.length :=
  groupClique_snd (one_le_powerBlockCount d φ.length) _

private theorem powerGroupingInput_blockSize_le {d : ℕ} (hd : 2 ≤ d) (φ : CNF ℕ) :
    (GroupClique.blockSize (powerGroupingInput d φ).2 (powerGroupingInput d φ).1 : ℝ) ≤
      3 * (φ.length + 1 : ℝ) ^ (1 - 1 / (d : ℝ)) := by
  let x : ℝ := φ.length + 1
  let r := powerBlockCount d φ.length
  let δ : ℝ := 1 / (d : ℝ)
  have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hr : (0 : ℝ) < r := by exact_mod_cast one_le_powerBlockCount d φ.length
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ : δ ≤ 1 := by dsimp only [δ]; apply div_le_one_of_le₀ <;> linarith
  have hq : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (sub_nonneg.mpr hδ)
  have hlen : (prepareCliqueCNF φ).length ≤ φ.length + 1 := by
    unfold prepareCliqueCNF
    split_ifs <;> simp [CNF.length_denseRelabel]
  have hdiv : x / r ≤ 2 * x ^ (1 - δ) := by
    rw [Real.rpow_sub (by positivity : 0 < x), Real.rpow_one, ← mul_div_assoc]
    apply (div_le_div_iff₀ hr (by positivity)).mpr
    have h := (powerBlockCount_bounds hd φ.length).1
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ x)).trans_eq (by ring)
  have h₁ := blockSize_real_le (m := (prepareCliqueCNF φ).length)
    (one_le_powerBlockCount d φ.length)
  have h₂ : ((prepareCliqueCNF φ).length : ℝ) / r ≤ x / r :=
    div_le_div_of_nonneg_right (by dsimp only [x]; exact_mod_cast hlen) hr.le
  change (GroupClique.blockSize (prepareCliqueCNF φ) r : ℝ) ≤ 3 * x ^ (1 - δ)
  exact h₁.trans (by linarith)

private theorem length_powerGroupingInput_le {d : ℕ} (hd : 2 ≤ d) (φ : CNF ℕ) :
    ((encPair encUnary encCNF (powerGroupingInput d φ)).length + 1 : ℝ) ≤
      134 * (φ.length + 1 : ℝ) ^ 2 := by
  have hx : (1 : ℝ) ≤ φ.length + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hδ : 1 / (d : ℝ) ≤ 1 := by apply div_le_one_of_le₀ <;> linarith
  have hr : (powerBlockCount d φ.length : ℝ) ≤ 2 * (φ.length + 1 : ℝ) :=
    (powerBlockCount_bounds hd φ.length).2.trans (mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le hx hδ).trans_eq (Real.rpow_one _)) (by norm_num))
  have hcnf : ((encCNF (prepareCliqueCNF φ)).length : ℝ) + 1 ≤
      128 * (φ.length + 1 : ℝ) ^ 2 := by exact_mod_cast length_enc_prepareCliqueCNF_le φ
  have hlen : (encPair encUnary encCNF (powerGroupingInput d φ)).length =
      2 * powerBlockCount d φ.length + 1 + (encCNF (prepareCliqueCNF φ)).length := by
    enc_len [powerGroupingInput]
  rw [hlen]
  push_cast
  nlinarith

/-- A polynomial in the clause count can be absorbed into any positive power in the exponent. -/
private theorem logb_poly_le {x q : ℝ} (hx : 1 ≤ x) (hq : 0 < q) :
    Real.logb 2 (134 * x ^ (2 : ℕ)) ≤
      (Real.logb 2 134 + 2 / (q * Real.log 2)) * x ^ q := by
  have hlog : Real.logb 2 x ≤ x ^ q / (q * Real.log 2) := by
    rw [Real.logb, ← div_div]
    exact div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hq)
      (Real.log_pos (by norm_num)).le
  have hc : 0 ≤ Real.logb 2 134 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hxq := Real.one_le_rpow hx hq.le
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, Nat.cast_ofNat]
  calc
    _ ≤ Real.logb 2 134 * x ^ q + 2 * (x ^ q / (q * Real.log 2)) :=
      add_le_add (le_mul_of_one_le_right hc hxq)
        (mul_le_mul_of_nonneg_left hlog (by norm_num))
    _ = _ := by ring

private theorem powerGrouping_resources {d : ℕ} (hd : 2 ≤ d) :
    ∃ A e : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ComputableInTimeO (powerGrouping d) encCNF encCliqueInstance
        (fun φ => (2 : ℝ) ^ (A * (φ.length + 1 : ℝ) ^ (1 - 1 / (d : ℝ))) *
          ((encCNF φ).length + 1) ^ e) ∧
      ∀ φ, Real.logb 2 ((encCliqueInstance (powerGrouping d φ)).length + 1 : ℝ) ≤
        B * (φ.length + 1 : ℝ) ^ (1 - 1 / (d : ℝ)) := by
  let q : ℝ := 1 - 1 / (d : ℝ)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < q := by
    unfold q
    exact sub_pos.mpr ((div_lt_iff₀ (by linarith)).mpr (by linarith))
  have hprep : ComputableInPolyTime (powerGroupingInput d) encCNF (encPair encUnary encCNF) :=
    (computableInPolyTime_powerBlockCount d).prod computableInPolyTime_prepareCliqueCNF
  obtain ⟨e, _, hprep⟩ := hprep.exists_degree
  obtain ⟨C, D, hgroup⟩ := exists_computableInO_groupClique
  obtain ⟨l, hlength⟩ := hgroup.length_le_time
  let H : ℝ := Real.logb 2 134 + 2 / (q * Real.log 2)
  have hH : 0 ≤ H := add_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
    (by positivity)
  let Y : ℝ := 9 * D + H * D
  have hY : 0 ≤ Y := by unfold Y; positivity
  let K : ℝ := (l + 1 : ℝ) * (C + 1 : ℝ)
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_left (Nat.cast_nonneg l)) (le_add_of_nonneg_left (Nat.cast_nonneg C))
  let groupTime (φ : CNF ℕ) : ℕ :=
    let input := powerGroupingInput d φ
    C * 2 ^ (D * (3 * GroupClique.blockSize input.2 input.1)) *
      ((encPair encUnary encCNF input).length + 1) ^ D
  have hGroupTime (φ : CNF ℕ) :
      (groupTime φ : ℝ) ≤ C * (2 : ℝ) ^ (Y * (φ.length + 1 : ℝ) ^ q) := by
    let x : ℝ := φ.length + 1
    let input := powerGroupingInput d φ
    let N := (encPair encUnary encCNF input).length
    let s := GroupClique.blockSize input.2 input.1
    have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hlog₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < N + 1) (length_powerGroupingInput_le hd φ)
    have hlog₂ : Real.logb 2 (N + 1 : ℝ) ≤ H * x ^ q := hlog₁.trans (logb_poly_le hx hq)
    have hP : (N + 1 : ℝ) ≤ 2 ^ (H * x ^ q) :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm.trans_le
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog₂)
    have hs : (s : ℝ) ≤ 3 * x ^ q := powerGroupingInput_blockSize_le hd φ
    have hT : (2 : ℝ) ^ (D * (3 * s) : ℕ) ≤ 2 ^ (9 * D * x ^ q) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) D)]
    change ((C * 2 ^ (D * (3 * s)) * (N + 1) ^ D : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (C : ℝ) * ((2 : ℝ) ^ (9 * D * x ^ q) * ((2 : ℝ) ^ (H * x ^ q)) ^ D) := by
        rw [mul_assoc]
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (H * x ^ q)) D, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 2
        dsimp only [Y, x]
        ring
  have hlogK := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hK
  refine ⟨⌈Y⌉₊, e, Real.logb 2 K + Y, add_nonneg hlogK hY, ?_, ?_⟩
  · let envelope (φ : CNF ℕ) : ℝ :=
      (2 : ℝ) ^ ((⌈Y⌉₊ : ℝ) * (φ.length + 1 : ℝ) ^ q) * ((encCNF φ).length + 1) ^ e
    refine (ComputableInTimeO.of_computableInO (hgroup.comp hprep.inO)
      (T := fun φ => (C + 1 : ℝ) * envelope φ) (fun φ => ?_)).mono (C + 1)
      (fun φ => by push_cast; exact le_add_of_nonneg_right (by positivity))
      (fun _ => by positivity)
    let P : ℝ := ((encCNF φ).length + 1 : ℝ) ^ e
    let X : ℝ := (2 : ℝ) ^ ((⌈Y⌉₊ : ℝ) * (φ.length + 1 : ℝ) ^ q)
    have hP : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
    have ht : (groupTime φ : ℝ) ≤ C * X := (hGroupTime φ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (Nat.le_ceil Y) (by positivity))) (Nat.cast_nonneg C))
    change ((((encCNF φ).length + 1) ^ e + groupTime φ : ℕ) : ℝ) ≤ (C + 1 : ℝ) * (X * P)
    push_cast
    change P + (groupTime φ : ℝ) ≤ (C + 1 : ℝ) * (X * P)
    calc
      _ ≤ X * P + C * (X * P) := add_le_add
        (le_mul_of_one_le_left (zero_le_one.trans hP) hX)
        (ht.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (zero_le_one.trans hX) hP)
          (Nat.cast_nonneg C)))
      _ = _ := by ring
  · intro φ
    let x : ℝ := φ.length + 1
    let X : ℝ := (2 : ℝ) ^ (Y * x ^ q)
    have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hxq := Real.one_le_rpow hx hq.le
    have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
    have hlen : ((encCliqueInstance (powerGrouping d φ)).length : ℝ) ≤
        l * ((groupTime φ : ℝ) + 1) := by
      exact_mod_cast hlength (powerGroupingInput d φ)
    have ht := hGroupTime φ
    change (groupTime φ : ℝ) ≤ C * X at ht
    have hTX : (groupTime φ : ℝ) + 1 ≤ (C + 1 : ℝ) * X := by linarith
    have hpos : (0 : ℝ) < X := zero_lt_one.trans_le hX
    have hLX : ((encCliqueInstance (powerGrouping d φ)).length : ℝ) + 1 ≤ K * X := by
      calc
        _ ≤ l * ((C + 1 : ℝ) * X) + 1 :=
          add_le_add (hlen.trans (mul_le_mul_of_nonneg_left hTX (Nat.cast_nonneg l))) le_rfl
        _ ≤ l * ((C + 1 : ℝ) * X) + (C + 1 : ℝ) * X := add_le_add le_rfl
          (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg C)) hX)
        _ = _ := by unfold K; ring
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hLX
    rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le hK)) hpos.ne',
      show Real.logb 2 X = Y * x ^ q from Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    exact hlog.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hxq hlogK])

end SAT

open SAT in
/-- Under SH, parameterized Clique admits no deterministic multitape algorithm in time
`2 ^ O((k + 1) ^ a) * (L + 1) ^ O((k + 1) ^ p)` for fixed `a > 0` and `0 < p < 1`,
where `L` is the length of the binary graph and target-size encoding. The clause grouping
chooses `k` within a constant factor of a small fixed power of the clause count. -/
theorem SH.not_clique_powerEnc (hSH : SH) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1)
    (C D : ℕ) :
    ¬DecidableInTimeO Clique encCliqueInstance (fun x =>
      (2 : ℝ) ^ (C * (x.m + 1 : ℝ) ^ a) *
        ((encCliqueInstance x).length + 1 : ℝ) ^ (D * (x.m + 1 : ℝ) ^ p)) := by
  intro h
  obtain ⟨d, hd⟩ := exists_nat_gt (max a 2)
  have hd₂ : 2 ≤ d := by
    exact_mod_cast ((le_max_right a 2).trans hd.le : (2 : ℝ) ≤ d)
  have hdpos : (0 : ℝ) < d := (by norm_num : (0 : ℝ) < 2).trans_le
    ((le_max_right a 2).trans hd.le)
  let δ : ℝ := 1 / (d : ℝ)
  let q := 1 - δ
  let b := max (δ * a) (δ * p + q)
  have hδ : 0 < δ := one_div_pos.mpr hdpos
  have hq : q < 1 := sub_lt_self _ hδ
  have hb : 0 < b := (mul_pos hδ ha).trans_le (le_max_left _ _)
  have hb₁ : b < 1 := by
    apply max_lt_iff.mpr
    constructor
    · dsimp only [δ]
      rw [one_div_mul_eq_div, div_lt_iff₀ hdpos, one_mul]
      exact (le_max_left a 2).trans_lt hd
    · dsimp only [q]
      linarith [mul_lt_mul_of_pos_left hp1 hδ]
  let budget (x : CliqueInstance) : ℝ :=
    (x.m + 1 : ℝ) ^ a + (x.m + 1 : ℝ) ^ p * Real.logb 2 ((encCliqueInstance x).length + 1 : ℝ)
  let μ (x : CliqueInstance) : ℕ := ⌈budget x⌉₊
  have hbudget (x : CliqueInstance) : 0 ≤ budget x := by
    have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (le_add_of_nonneg_left (Nat.cast_nonneg (encCliqueInstance x).length))
    unfold budget
    positivity
  have hfast : DecidableInPowerExpTime Clique encCliqueInstance μ 1 := by
    refine ⟨C + D, 0, h.mono 1 (fun x => ?_) (fun _ => by positivity)⟩
    simp only [Real.rpow_one, pow_zero, mul_one, Nat.cast_one, one_mul]
    let k : ℝ := x.m + 1
    let L : ℝ := (encCliqueInstance x).length + 1
    have hL : 1 ≤ L := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hlog : 0 ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) hL
    have hK : k ^ a ≤ (μ x : ℝ) + 1 :=
      (le_add_of_nonneg_right (mul_nonneg (by positivity) hlog)).trans
        ((Nat.le_ceil (budget x)).trans (le_add_of_nonneg_right zero_le_one))
    have hP : k ^ p * Real.logb 2 L ≤ (μ x : ℝ) + 1 :=
      (le_add_of_nonneg_left (show 0 ≤ k ^ a by positivity)).trans
        ((Nat.le_ceil (budget x)).trans (le_add_of_nonneg_right zero_le_one))
    have hEq : L ^ (D * k ^ p) = (2 : ℝ) ^ ((D * k ^ p) * Real.logb 2 L) := by
      rw [mul_comm (D * k ^ p), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hL)]
    change (2 : ℝ) ^ (C * k ^ a) * L ^ (D * k ^ p) ≤ 2 ^ _ + 1
    rw [hEq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans
      (le_add_of_nonneg_right zero_le_one)
    push_cast
    rw [mul_assoc (D : ℝ)]
    linarith [mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℝ) C),
      mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg (α := ℝ) D)]
  obtain ⟨A, e, B, hB, hred, hlen⟩ := powerGrouping_resources hd₂
  apply hSH.not_decidableInPowerExpTime_of_reduction (q := q) (b := b) (p := 1)
    hq hb zero_lt_one (by rw [mul_one]; exact hb₁) _ (powerGrouping_mem_iff d) _ hfast
  · refine ⟨A, e, hred.mono 1 (fun φ => ?_) (fun _ => by positivity)⟩
    have hbase : (φ.length + 1 : ℝ) ≤ ((φ.numVars + φ.length : ℕ) + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_left φ.length φ.numVars) 1
    have hq₀ : 0 ≤ q := by
      dsimp only [q, δ]
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hdpos).mpr (by linarith [(le_max_right a 2).trans hd.le])
    simp only [Nat.cast_one, one_mul]
    refine (two_rpow_mul_pow_le_two_rpow_mul_pow
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hq₀)
        (Nat.cast_nonneg A)) le_rfl).trans (le_add_of_nonneg_right zero_le_one)
  · intro η hη
    let W : ℝ := (3 : ℝ) ^ a + (3 : ℝ) ^ p * B + 2
    refine ⟨⌈W⌉₊, fun φ => ?_⟩
    let x : ℝ := φ.length + 1
    let y := powerGrouping d φ
    let z : ℝ := (φ.numVars + φ.length : ℕ) + 1
    have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hxz : x ≤ z := by
      dsimp only [x, z]
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_left φ.length φ.numVars) 1
    have hk : (y.m + 1 : ℝ) ≤ 3 * x ^ δ := by
      change ((powerGrouping d φ).m + 1 : ℝ) ≤ _
      rw [powerGrouping_m]
      have h := (powerBlockCount_bounds hd₂ φ.length).2
      have hxδ := Real.one_le_rpow hx hδ.le
      change (powerBlockCount d φ.length : ℝ) ≤ 2 * x ^ δ at h
      linarith
    have hka := Real.rpow_le_rpow (by positivity) hk ha.le
    have hkp := Real.rpow_le_rpow (by positivity) hk hp.le
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)] at hka hkp
    have hA : (y.m + 1 : ℝ) ^ a ≤ (3 : ℝ) ^ a * x ^ b :=
      hka.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)) (by positivity))
    have hlog : 0 ≤ Real.logb 2 ((encCliqueInstance y).length + 1 : ℝ) :=
      Real.logb_nonneg (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hP : (y.m + 1 : ℝ) ^ p * Real.logb 2 ((encCliqueInstance y).length + 1 : ℝ) ≤
        (3 : ℝ) ^ p * B * x ^ b := by
      calc
        _ ≤ ((3 : ℝ) ^ p * x ^ (δ * p)) * (B * x ^ q) :=
          mul_le_mul hkp (hlen φ) hlog (by positivity)
        _ = (3 : ℝ) ^ p * B * x ^ (δ * p + q) := by
          rw [Real.rpow_add (by positivity)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ (δ * p + q))) (by positivity)
    have hceil := Nat.ceil_lt_add_one (hbudget y)
    have hsum : budget y ≤ ((3 : ℝ) ^ a + (3 : ℝ) ^ p * B) * x ^ b := by
      unfold budget
      rw [add_mul]
      exact add_le_add hA hP
    have hsmall : (μ y + 1 : ℝ) ≤ W * x ^ b := by
      dsimp only [μ, W]
      nlinarith [Real.one_le_rpow hx hb.le]
    have hpow : x ^ b ≤ z ^ (b + η) :=
      (Real.rpow_le_rpow (by positivity) hxz hb.le).trans
        (Real.rpow_le_rpow_of_exponent_le (hx.trans hxz) (le_add_of_nonneg_right hη.le))
    exact hsmall.trans (mul_le_mul (Nat.le_ceil W |>.trans (le_add_of_nonneg_right zero_le_one))
      hpow (by positivity) (by positivity))

/-- Under SH, parameterized Clique admits no deterministic multitape algorithm in time
`2 ^ O((k + 1) ^ a) * (|V| + 1) ^ O((k + 1) ^ p) * (L + 1) ^ O(1)` for fixed
`a > 0` and `0 < p < 1`. The vertex-count factor uses the length of the declared vertex list,
and `L` is the length of the binary graph and target-size encoding. -/
theorem SH.not_clique_powerVertex (hSH : SH) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1)
    (C D e : ℕ) :
    ¬DecidableInTimeO Clique encCliqueInstance (fun x =>
      (2 : ℝ) ^ (C * (x.m + 1 : ℝ) ^ a) *
        (x.graph.vertices.length + 1 : ℝ) ^ (D * (x.m + 1 : ℝ) ^ p) *
        ((encCliqueInstance x).length + 1) ^ e) := by
  intro h
  apply hSH.not_clique_powerEnc ha hp hp1 C (D + e)
  refine h.mono 1 (fun x => ?_) (fun _ => by positivity)
  let L : ℝ := (encCliqueInstance x).length + 1
  let k : ℝ := x.m + 1
  have hL : 1 ≤ L := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hk : 1 ≤ k := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hVL : (x.graph.vertices.length + 1 : ℝ) ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.add_le_add_right (length_vertices_le_encCliqueInstance x) 1
  have hV := Real.rpow_le_rpow (by positivity) hVL (by positivity : 0 ≤ (D : ℝ) * k ^ p)
  have he : D * k ^ p + e ≤ (D + e : ℕ) * k ^ p := by
    push_cast
    rw [add_mul]
    exact add_le_add le_rfl (le_mul_of_one_le_right (Nat.cast_nonneg e) (Real.one_le_rpow hk hp.le))
  simp only [Nat.cast_one, one_mul]
  change (2 : ℝ) ^ (C * k ^ a) * (x.graph.vertices.length + 1 : ℝ) ^ (D * k ^ p) * L ^ e ≤
    2 ^ (C * k ^ a) * L ^ ((D + e : ℕ) * k ^ p) + 1
  calc
    _ ≤ (2 : ℝ) ^ (C * k ^ a) * L ^ (D * k ^ p) * L ^ e := by gcongr
    _ = (2 : ℝ) ^ (C * k ^ a) * L ^ (D * k ^ p + e) := by
      rw [Real.rpow_add (by positivity), Real.rpow_natCast, mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he)
      (by positivity)).trans (le_add_of_nonneg_right zero_le_one)

end Cslib.Complexity
