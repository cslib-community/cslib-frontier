/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Computability.Circuit.Rectifier.Basic
public import CslibFrontier.Computability.Circuit.Simulation
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Matrix.Basic
import CslibFrontier.Foundations.Data.BitString.Parity
import Mathlib.Data.Fintype.EquivFin

/-!
# Depth-two rectifier synthesis

A Boolean matrix with `p` rows and `q` columns specifies a map from `p` input bits to `q`
output bits: output `j` is the disjunction of those inputs `i` for which `A i j` is true.
Rows index input poles and columns index output poles, as in the matrix `αᵢⱼ = (aᵢ, bⱼ)`
implemented by a rectifier `(p, q)`-circuit in [Lupanov, section 2°][Lupanov1956].

## The circuit model and its relation to `RectifierCircuit`

The library's rectifier circuits are the directed graphs `Cslib.Circuits.RectifierCircuit`, with
the measures `Cslib.Circuits.orComplexity` and `Cslib.Circuits.orDepthComplexity`. This file uses
a second model, the native `Circuit` syntax over a signature with only disjunction gates,
because a syntactic circuit can also be evaluated under other interpretations of its gates and
translated gate by gate into other bases, which a reachability graph does not support. An
operation is its arity, and `Program.cost id` counts wires, including wires entering output
gates. Output pointers themselves are free. A nullary disjunction is an output with no incoming
path.

`IsTwoLayer` singles out the compositions of two matrix layers. Such a circuit is a graph on
the `p` inputs, its inner gates and `q` distinct output gates, with one edge for each wire, from
an input to an inner gate or from an inner gate to an output. No chain joins two inputs or two
outputs or leads from an output to an input, and no chain has more than two edges, so it is a
rectifier `(p, q)`-circuit of rank at most two in the sense of [Lupanov1956], section 2°. A
two-layer circuit with `w` wires that computes `matrixAction A` therefore shows `B₂(A) ≤ w` for
Lupanov's measure `B₂`.

The two models use transposed conventions: `RectifierCircuit.Computes` indexes rows by outputs
and columns by inputs, so the matrix `A` of this file is `Aᵀ` there.
`IsTwoLayer.orDepthComplexity_two_le` turns a two-layer circuit with `w` wires into
`orDepthComplexity 2 Aᵀ ≤ w`. That bound is weaker than `B₂(A) ≤ w`. A `(p, q)`-circuit of rank
at most two contains a `RectifierCircuit` of depth two for the same matrix (keep one chain for
each true entry), so `orDepthComplexity 2 Aᵀ ≤ B₂(A)`. The inequality can be strict, because a
`RectifierCircuit` may have edges into input poles and out of output poles, which the conditions
on a `(p, q)`-circuit exclude: for the all-true matrix with two inputs and three outputs, the
four edges `a₁ → a₂` and `a₂ → b₁, b₂, b₃` form a `RectifierCircuit` of depth two, while a
`(2, 3)`-circuit needs five rectifiers. The measure `B₂` itself is not defined in the library.

## The row-pattern construction

The construction groups inputs with identical matrix rows. Its first layer has one gate for
every row pattern; its second layer sends each pattern to the columns in its support. It has
exactly `p + q * 2 ^ (q - 1)` wires. Empty row classes are permitted and contribute no
first-layer wires.

## Main definitions

* `Cslib.Circuits.Boolean.Rectifier.signature`: disjunction gates, indexed by their arity.
* `Cslib.Circuits.Boolean.Rectifier.matrixAction`: the Boolean map specified by a matrix.
* `Cslib.Circuits.Boolean.Rectifier.layer`: one layer of disjunctions specified by a matrix.
* `Cslib.Circuits.Boolean.Rectifier.IsTwoLayer`: a composition of two matrix layers, with a
  distinct terminal gate for every output.
* `Cslib.Circuits.Boolean.Rectifier.rowPatternCircuit`: the two-layer row-pattern construction.

## Main results

* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two`: Lupanov's finite row-pattern bound.
* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two_blocked_exact`: the wire count after
  splitting the columns into blocks of a freely chosen positive width.
* `Cslib.Circuits.Boolean.Rectifier.IsTwoLayer.orDepthComplexity_two_le`: a two-layer circuit
  bounds `orDepthComplexity 2` of the transposed matrix by its wire count.
* `Cslib.Circuits.orDepthComplexity_two_le_add_mul_two_pow`: the row-pattern bound for
  `orDepthComplexity 2`, a weaker statement than Lupanov's.

## References

* [O. B. Lupanov, *On rectifier and switching-and-rectifier circuits*][Lupanov1956],
  section 2°: the definition of a `(p, q)`-circuit and the unnumbered Lemma (English
  translation, PDF pp. 1–2).
-/

public section

namespace Cslib.Circuits.Boolean.Rectifier

open Finset
open scoped Matrix

/-- The pure disjunction signature: the operation `m` is disjunction of `m` arguments. -/
abbrev signature : Signature where
  Op := ℕ
  Arity := id

/-- The Boolean meaning of a rectifier gate. The nullary gate is `false`. -/
@[expose] def interpretation : Interpretation signature Bool :=
  fun m => Unbounded.interpretation (.or m)

variable {p q : ℕ}

/-- The map whose `j`th output is the disjunction of inputs in the support of column `j`.
Rows index inputs and columns index outputs, as in Lupanov's rectifier matrix convention. -/
@[expose] def matrixAction (A : Matrix (Fin p) (Fin q) Bool)
    (x : Fin p → Bool) (j : Fin q) : Bool :=
  decide (∃ i, A i j = true ∧ x i = true)

/-- One disjunction per matrix column, with one wire per true entry. -/
@[expose] noncomputable def layer (A : Matrix (Fin p) (Fin q) Bool) : Circuit signature p q :=
  Circuit.pi fun j =>
    let inputs := univ.filter fun i => A i j = true
    Circuit.oneGate inputs.card fun k => (inputs.equivFin.symm k).val

/-- A disjunction layer computes its matrix action. -/
theorem eval_layer (A : Matrix (Fin p) (Fin q) Bool) (x : Fin p → Bool) :
    (layer A).eval interpretation x = matrixAction A x := by
  funext j
  simp only [layer, Circuit.eval_pi, Circuit.eval_oneGate, interpretation,
    Unbounded.interpretation_or, matrixAction]
  congr 1
  apply propext
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, (mem_filter.mp ((univ.filter fun i => A i j = true).equivFin.symm k).property).2,
      hk⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨(univ.filter fun i => A i j = true).equivFin ⟨i, by simp [hi]⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hx

/-- The wire count of a disjunction layer is the number of true matrix entries. -/
theorem cost_layer (A : Matrix (Fin p) (Fin q) Bool) :
    (layer A).program.cost id = ∑ j, #{i | A i j = true} := by
  simp only [layer, Circuit.cost_program_pi, Circuit.cost_program_oneGate, id_eq]

/-- A disjunction layer has depth at most one, including when there are no outputs. -/
theorem depth_layer_le (A : Matrix (Fin p) (Fin q) Bool) : (layer A).depth ≤ 1 := by
  exact Circuit.depth_pi_le _ fun _ => (Circuit.depth_oneGate _ _).le

/-- A rectifier realization by two matrix layers. Every output has its own terminal gate,
and every wire belongs to one of the two layers. This excludes free aliases among outputs or
between an input and an output, which would not be distinct poles in the source model. With
the wires as edges, from inputs to inner gates and from inner gates to outputs, the circuit is a
rectifier `(p, q)`-circuit of rank at most two in the sense of [Lupanov1956], section 2°;
`IsTwoLayer.orDepthComplexity_two_le` builds the corresponding `RectifierCircuit`. -/
@[expose] def IsTwoLayer (c : Circuit signature p q) : Prop :=
  ∃ (k : ℕ) (inputs : Matrix (Fin p) (Fin k) Bool) (outputs : Matrix (Fin k) (Fin q) Bool),
    c = (layer outputs).comp (layer inputs)

/-- Two matrix layers have native circuit depth at most two. -/
theorem IsTwoLayer.depth_le {c : Circuit signature p q} (hc : IsTwoLayer c) : c.depth ≤ 2 := by
  obtain ⟨k, inputs, outputs, rfl⟩ := hc
  exact (Circuit.depth_comp_le _ _).trans
    (Nat.add_le_add (depth_layer_le _) (depth_layer_le _))

/-! ### Comparison with the rectifier-graph model -/

/-- The rectifier graph of two matrix layers: the `p` input poles, `k` inner vertices and the `q`
output poles, with one edge for each true entry of either matrix. -/
private def twoLayerGraph {k : ℕ} (inputs : Matrix (Fin p) (Fin k) Bool)
    (outputs : Matrix (Fin k) (Fin q) Bool) :
    RectifierCircuit (Fin q) (Fin p) (Fin p ⊕ Fin k ⊕ Fin q) where
  edges :=
    (univ.filter fun e : Fin k × Fin p => inputs e.2 e.1 = true).image
        (fun e => (Sum.inl e.2, Sum.inr (Sum.inl e.1))) ∪
      (univ.filter fun e : Fin q × Fin k => outputs e.2 e.1 = true).image
        (fun e => (Sum.inr (Sum.inl e.2), Sum.inr (Sum.inr e.1)))
  inp := Function.Embedding.inl
  out := Function.Embedding.inr.trans Function.Embedding.inr
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    nomatch h

private theorem mem_edges_twoLayerGraph {k : ℕ} {inputs : Matrix (Fin p) (Fin k) Bool}
    {outputs : Matrix (Fin k) (Fin q) Bool} {u v : Fin p ⊕ Fin k ⊕ Fin q} :
    (u, v) ∈ (twoLayerGraph inputs outputs).edges ↔
      (∃ m i, inputs i m = true ∧ Sum.inl i = u ∧ Sum.inr (Sum.inl m) = v) ∨
        ∃ j m, outputs m j = true ∧ Sum.inr (Sum.inl m) = u ∧ Sum.inr (Sum.inr j) = v := by
  simp only [twoLayerGraph, mem_union, mem_image, mem_filter, mem_univ, true_and, Prod.exists,
    Prod.mk.injEq]

private theorem size_twoLayerGraph_le {k : ℕ} (inputs : Matrix (Fin p) (Fin k) Bool)
    (outputs : Matrix (Fin k) (Fin q) Bool) :
    (twoLayerGraph inputs outputs).size ≤
      ((layer outputs).comp (layer inputs)).program.cost id := by
  rw [Circuit.cost_program_comp, cost_layer, cost_layer]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact card_image_le.trans (boolMatrixWeight_eq_sum_row inputsᵀ).le
  · exact card_image_le.trans (boolMatrixWeight_eq_sum_row outputsᵀ).le

private theorem hasDepthLE_two_twoLayerGraph {k : ℕ} (inputs : Matrix (Fin p) (Fin k) Bool)
    (outputs : Matrix (Fin k) (Fin q) Bool) : (twoLayerGraph inputs outputs).HasDepthLE 2 := by
  refine RectifierCircuit.hasDepthLE_of_layer
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) fun _ => 2)) ?_ ?_
  · intro u v h
    rcases mem_edges_twoLayerGraph.mp h with ⟨m, i, -, rfl, rfl⟩ | ⟨j, m, -, rfl, rfl⟩ <;> rfl
  · rintro (i | m | j) <;> simp

private theorem computes_twoLayerGraph {k : ℕ} {inputs : Matrix (Fin p) (Fin k) Bool}
    {outputs : Matrix (Fin k) (Fin q) Bool} {A : Matrix (Fin p) (Fin q) Bool}
    (hA : ∀ i j, A i j = true ↔ ∃ m, outputs m j = true ∧ inputs i m = true) :
    (twoLayerGraph inputs outputs).Computes Aᵀ := by
  intro j i
  rw [Matrix.transpose_apply, hA]
  constructor
  · rintro ⟨m, ho, hi⟩
    exact ⟨.cons (mem_edges_twoLayerGraph.mpr (.inl ⟨m, i, hi, rfl, rfl⟩))
      (.cons (mem_edges_twoLayerGraph.mpr (.inr ⟨j, m, ho, rfl, rfl⟩)) (.nil _))⟩
  · rintro ⟨w⟩
    obtain ⟨v, he, ⟨w⟩⟩ := w.uncons (fun h => by nomatch h)
    rcases mem_edges_twoLayerGraph.mp he with ⟨m, i', hi, hu, rfl⟩ | ⟨_, _, -, hu, -⟩
    swap
    · nomatch hu
    cases hu
    obtain ⟨v, he, ⟨w⟩⟩ := w.uncons (fun h => by nomatch h)
    rcases mem_edges_twoLayerGraph.mp he with ⟨_, _, -, hu, -⟩ | ⟨j', m', ho, hu, rfl⟩
    · nomatch hu
    cases hu
    by_cases hj : j' = j
    · exact ⟨m, hj ▸ ho, hi⟩
    · obtain ⟨v, he, -⟩ := w.uncons (fun h => hj (Sum.inr.inj (Sum.inr.inj h)))
      rcases mem_edges_twoLayerGraph.mp he with ⟨_, _, -, hu, -⟩ | ⟨_, _, -, hu, -⟩ <;>
        nomatch hu

/-- **Two matrix layers as a rectifier graph.** If a two-layer circuit computes the action of
`A`, then the depth-two rectifier complexity of the transpose `Aᵀ`, in the graph model
`Cslib.Circuits.RectifierCircuit`, is at most its number of wires. The transpose appears because
rows index inputs here and outputs there. The graph has the inputs, the inner gates and the
output gates as vertices and the wires as edges. -/
theorem IsTwoLayer.orDepthComplexity_two_le {c : Circuit signature p q} (hc : IsTwoLayer c)
    {A : Matrix (Fin p) (Fin q) Bool} (hA : c.Computes interpretation (matrixAction A)) :
    orDepthComplexity 2 Aᵀ ≤ (c.program.cost id : ℕ∞) := by
  obtain ⟨k, inputs, outputs, rfl⟩ := hc
  have h (i : Fin p) (j : Fin q) :
      A i j = true ↔ ∃ m, outputs m j = true ∧ inputs i m = true := by
    have hx := congrFun (hA fun i' => decide (i' = i)) j
    rw [Circuit.eval_comp, eval_layer, eval_layer] at hx
    simp only [matrixAction, decide_eq_true_eq, exists_eq_right, decide_eq_decide] at hx
    exact hx.symm
  exact ((computes_twoLayerGraph h).orDepthComplexity_le (hasDepthLE_two_twoLayerGraph _ _)).trans
    (Nat.cast_le.mpr (size_twoLayerGraph_le _ _))

private def rowClasses (A : Matrix (Fin p) (Fin q) Bool) :
    Matrix (Fin p) (Fin (2 ^ q)) Bool :=
  Matrix.of fun i r => decide (BitString.equivFin q (A i) = r)

private def patterns (q : ℕ) : Matrix (Fin (2 ^ q)) (Fin q) Bool :=
  Matrix.of fun r j => (BitString.equivFin q).symm r j

/-- Group equal input rows, then connect each row pattern to the columns in its support. -/
noncomputable def rowPatternCircuit (A : Matrix (Fin p) (Fin q) Bool) :
    Circuit signature p q :=
  (layer (patterns q)).comp (layer (rowClasses A))

/-- The row-pattern construction realizes distinct input and output poles in two layers. -/
theorem isTwoLayer_rowPatternCircuit (A : Matrix (Fin p) (Fin q) Bool) :
    IsTwoLayer (rowPatternCircuit A) :=
  ⟨2 ^ q, rowClasses A, patterns q, rfl⟩

/-- The row-pattern circuit computes the map specified by the matrix. -/
theorem eval_rowPatternCircuit (A : Matrix (Fin p) (Fin q) Bool) (x : Fin p → Bool) :
    (rowPatternCircuit A).eval interpretation x = matrixAction A x := by
  rw [rowPatternCircuit, Circuit.eval_comp, eval_layer, eval_layer]
  funext j
  simp only [matrixAction, rowClasses, patterns, Matrix.of_apply, decide_eq_true_eq]
  congr 1
  apply propext
  constructor
  · rintro ⟨r, hr, i, hi, hx⟩
    subst r
    exact ⟨i, by simpa only [Equiv.symm_apply_apply] using hr, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨BitString.equivFin q (A i), by simpa only [Equiv.symm_apply_apply] using hi,
      i, rfl, hx⟩

private theorem cost_rowClasses (A : Matrix (Fin p) (Fin q) Bool) :
    (layer (rowClasses A)).program.cost id = p := by
  rw [cost_layer]
  simp only [rowClasses, Matrix.of_apply, decide_eq_true_eq]
  rw [sum_card_fiberwise_eq_card_filter]
  simp

private theorem card_patterns (j : Fin q) :
    #{r : Fin (2 ^ q) | patterns q r j = true} = 2 ^ (q - 1) := by
  have h := Cslib.card_filter_parityOn_eq (singleton_nonempty j) true
  simp only [Cslib.parityOn_singleton, Fintype.card_fin] at h
  rw [← h]
  apply Finset.card_equiv (BitString.equivFin q).symm
  intro r
  change (r ∈ univ.filter (fun t : Fin (2 ^ q) => (BitString.equivFin q).symm t j = true)) ↔
    (BitString.equivFin q).symm r ∈ univ.filter (fun x : BitString q => x j = true)
  simp only [mem_filter, mem_univ, true_and]

/-- The row-pattern construction has exactly `p + q * 2 ^ (q - 1)` wires. -/
theorem cost_rowPatternCircuit (A : Matrix (Fin p) (Fin q) Bool) :
    (rowPatternCircuit A).program.cost id = p + q * 2 ^ (q - 1) := by
  rw [rowPatternCircuit, Circuit.cost_program_comp, cost_rowClasses, cost_layer]
  simp only [card_patterns, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Lupanov's row-pattern bound** ([Lupanov1956], section 2°, the unnumbered Lemma
`B₂(p, q) ≤ p + q · 2^(q−1)`; English translation, PDF p. 2): every Boolean matrix with `p`
input rows and `q` output columns is computed by a two-layer rectifier circuit with at most
`p + q * 2 ^ (q - 1)` wires. A two-layer circuit has edges only from inputs to inner gates and
from inner gates to distinct output gates, so it is a `(p, q)`-circuit of rank at most two in
Lupanov's sense and the statement bounds his `B₂`; its native depth is at most two by
`IsTwoLayer.depth_le`. Both dimensions may be zero; nullary disjunctions represent outputs with
no incoming paths. -/
theorem exists_depth_two (A : Matrix (Fin p) (Fin q) Bool) :
    ∃ c : Circuit signature p q,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧
        c.program.cost id ≤ p + q * 2 ^ (q - 1) :=
  ⟨rowPatternCircuit A, isTwoLayer_rowPatternCircuit A, eval_rowPatternCircuit A,
    (cost_rowPatternCircuit A).le⟩

private def blockSlice {b s : ℕ} (A : Matrix (Fin p) (Fin (b * s)) Bool) (t : Fin b) :
    Matrix (Fin p) (Fin s) Bool :=
  Matrix.of fun i j => A i (finProdFinEquiv (t, j))

private def blockClasses {b s : ℕ} (A : Matrix (Fin p) (Fin (b * s)) Bool) :
    Matrix (Fin p) (Fin (b * 2 ^ s)) Bool :=
  Matrix.of fun i r => rowClasses (blockSlice A (finProdFinEquiv.symm r).1) i
    (finProdFinEquiv.symm r).2

private def blockPatterns (b s : ℕ) : Matrix (Fin (b * 2 ^ s)) (Fin (b * s)) Bool :=
  Matrix.of fun r j => decide ((finProdFinEquiv.symm r).1 = (finProdFinEquiv.symm j).1) &&
    patterns s (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm j).2

private noncomputable def blockCircuit {b s : ℕ}
    (A : Matrix (Fin p) (Fin (b * s)) Bool) (select : Fin q → Fin (b * s)) :
    Circuit signature p q :=
  (layer ((blockPatterns b s).submatrix id select)).comp (layer (blockClasses A))

private theorem eval_blockCircuit {b s : ℕ} (A : Matrix (Fin p) (Fin (b * s)) Bool)
    (select : Fin q → Fin (b * s)) (x : Fin p → Bool) :
    (blockCircuit A select).eval interpretation x = fun j => matrixAction A x (select j) := by
  rw [blockCircuit, Circuit.eval_comp, eval_layer, eval_layer]
  funext j
  simp only [matrixAction, Matrix.submatrix_apply, id_eq, blockClasses, blockPatterns,
    rowClasses, patterns, Matrix.of_apply, Bool.and_eq_true, decide_eq_true_eq]
  congr 1
  apply propext
  constructor
  · rintro ⟨r, ⟨hb, hr⟩, i, hi, hx⟩
    refine ⟨i, ?_, hx⟩
    rw [← hi, Equiv.symm_apply_apply, blockSlice, Matrix.of_apply, hb] at hr
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using hr
  · rintro ⟨i, hi, hx⟩
    refine ⟨finProdFinEquiv ((finProdFinEquiv.symm (select j)).1,
      BitString.equivFin s (blockSlice A (finProdFinEquiv.symm (select j)).1 i)), ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply, true_and, blockSlice, Matrix.of_apply]
      simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using hi
    · exact ⟨i, by simp only [Equiv.symm_apply_apply], hx⟩

private theorem cost_blockClasses {b s : ℕ} (A : Matrix (Fin p) (Fin (b * s)) Bool) :
    (layer (blockClasses A)).program.cost id = b * p := by
  rw [cost_layer, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [blockClasses, Matrix.of_apply, Equiv.symm_apply_apply]
  have h (t : Fin b) : ∑ r, #{i | rowClasses (blockSlice A t) i r = true} = p := by
    have ht := cost_rowClasses (blockSlice A t)
    rw [cost_layer] at ht
    exact ht
  simp only [h, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

private theorem card_blockPatterns {b s : ℕ} (j : Fin (b * s)) :
    #{r : Fin (b * 2 ^ s) | blockPatterns b s r j = true} = 2 ^ (s - 1) := by
  rw [← card_patterns (finProdFinEquiv.symm j).2]
  apply Finset.card_bij (fun r _ => (finProdFinEquiv.symm r).2)
  · intro r hr
    simp only [mem_filter, mem_univ, true_and, blockPatterns, Matrix.of_apply, Bool.and_eq_true,
      decide_eq_true_eq] at hr ⊢
    exact hr.2
  · intro r hr t ht hrt
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · simp only [mem_filter, mem_univ, true_and, blockPatterns, Matrix.of_apply, Bool.and_eq_true,
        decide_eq_true_eq] at hr ht
      exact hr.1.trans ht.1.symm
    · exact hrt
  · intro r hr
    refine ⟨finProdFinEquiv ((finProdFinEquiv.symm j).1, r), ?_, ?_⟩
    · simpa only [mem_filter, mem_univ, true_and, blockPatterns, Matrix.of_apply, Bool.and_eq_true,
        decide_eq_true_eq, Equiv.symm_apply_apply, true_and] using hr
    · simp only [Equiv.symm_apply_apply]

private theorem cost_blockCircuit {b s : ℕ}
    (A : Matrix (Fin p) (Fin (b * s)) Bool) (select : Fin q → Fin (b * s)) :
    (blockCircuit A select).program.cost id = b * p + q * 2 ^ (s - 1) := by
  rw [blockCircuit, Circuit.cost_program_comp, cost_blockClasses, cost_layer]
  congr 1
  calc
    _ = ∑ _ : Fin q, 2 ^ (s - 1) := by
      apply sum_congr rfl
      intro j _
      exact card_blockPatterns (select j)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

private theorem isTwoLayer_blockCircuit {b s : ℕ}
    (A : Matrix (Fin p) (Fin (b * s)) Bool) (select : Fin q → Fin (b * s)) :
    IsTwoLayer (blockCircuit A select) :=
  ⟨b * 2 ^ s, blockClasses A, (blockPatterns b s).submatrix id select, rfl⟩

/-- Block synthesis, the finite construction behind the upper bound of [Lupanov1956],
section 2°, Theorem 1 (proof, part 1; English translation, PDF p. 3). Splitting the `q` columns
into `⌈q / s⌉` blocks of width `s`, the last one padded with zero columns, and applying the
row-pattern construction to each block gives a two-layer circuit in which `⌈q / s⌉ * p` wires
enter the row classes and `q * 2 ^ (s - 1)` wires enter the outputs. No wire enters a padded
column, so the count is at most `⌈q / s⌉ * (p + s * 2 ^ (s - 1))`, which is at most the
source's `(⌊q / s⌋ + 1) * (p + s * 2 ^ (s - 1))`. As for `exists_depth_two`, the witness is a
`(p, q)`-circuit of rank at most two in Lupanov's sense. -/
theorem exists_depth_two_blocked_exact (A : Matrix (Fin p) (Fin q) Bool) {s : ℕ} (hs : 0 < s) :
    ∃ c : Circuit signature p q,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧
        c.program.cost id = (q ⌈/⌉ s) * p + q * 2 ^ (s - 1) := by
  have hq : q ≤ (q ⌈/⌉ s) * s := by
    simpa only [smul_eq_mul, Nat.mul_comm] using (le_smul_ceilDiv hs : q ≤ s • (q ⌈/⌉ s))
  let padded : Matrix (Fin p) (Fin ((q ⌈/⌉ s) * s)) Bool :=
    Matrix.of fun i j => if h : j.val < q then A i ⟨j.val, h⟩ else false
  refine ⟨blockCircuit padded (Fin.castLE hq), isTwoLayer_blockCircuit _ _, ?_,
    cost_blockCircuit _ _⟩
  intro x
  rw [eval_blockCircuit]
  funext j
  simp only [matrixAction, padded, Matrix.of_apply, Fin.val_castLE, j.isLt, dite_true]

end Cslib.Circuits.Boolean.Rectifier

namespace Cslib.Circuits

open Boolean.Rectifier
open scoped Matrix

/-- The row-pattern bound for the library's graph measure. This is a weaker statement than the
Lemma of [Lupanov1956], section 2°, and is not that result: a `RectifierCircuit` may have edges
into input poles and out of output poles, which a `(p, q)`-circuit may not, so a bound on
`orDepthComplexity 2` does not bound Lupanov's `B₂`. The cited bound is
`Cslib.Circuits.Boolean.Rectifier.exists_depth_two`.

A matrix with `q` output rows and `p` input columns, the convention of
`RectifierCircuit.Computes`, has depth-two rectifier complexity at most `p + q * 2 ^ (q - 1)`. -/
theorem orDepthComplexity_two_le_add_mul_two_pow {p q : ℕ} (A : Matrix (Fin q) (Fin p) Bool) :
    orDepthComplexity 2 A ≤ ((p + q * 2 ^ (q - 1) : ℕ) : ℕ∞) :=
  ((isTwoLayer_rowPatternCircuit Aᵀ).orDepthComplexity_two_le (eval_rowPatternCircuit Aᵀ)).trans
    (Nat.cast_le.mpr (cost_rowPatternCircuit Aᵀ).le)

end Cslib.Circuits
