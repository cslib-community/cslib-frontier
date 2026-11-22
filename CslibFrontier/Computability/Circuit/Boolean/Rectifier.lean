/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
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
This is the input-to-output reachability convention of [Lupanov, §2][Lupanov1956].

Rectifier circuits use the native `Circuit` syntax with only disjunction gates. An operation
is its arity, and `Program.cost id` counts wires, including wires entering output gates.
Output pointers themselves are free. A nullary disjunction is an output with no incoming path.
The signature embeds into the existing unbounded Boolean basis through `toUnbounded`.

The row-pattern construction groups inputs with identical matrix rows. Its first layer has
one gate for every row pattern; its second layer sends each pattern to the columns in its
support. It has depth at most two and exactly `p + q * 2 ^ (q - 1)` wires. Empty row classes
are permitted and contribute no first-layer wires.

## Main definitions

* `Cslib.Circuits.Boolean.Rectifier.signature`: disjunction gates, indexed by their arity.
* `Cslib.Circuits.Boolean.Rectifier.matrixAction`: the Boolean map specified by a matrix.
* `Cslib.Circuits.Boolean.Rectifier.layer`: one layer of disjunctions specified by a matrix.
* `Cslib.Circuits.Boolean.Rectifier.IsTwoLayer`: a composition of two matrix layers, with a
  distinct terminal gate for every output.
* `Cslib.Circuits.Boolean.Rectifier.rowPatternCircuit`: the two-layer row-pattern construction.

## Main results

* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two`: Lupanov's finite row-pattern bound.
* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two_blocked`: the bound after splitting the
  columns into blocks of a freely chosen positive width.

## References

* [O. B. Lupanov, *On rectifier and switching-and-rectifier circuits*][Lupanov1956],
  §2, the unnamed lemma, pp. 1171–1172 (English translation, pp. 2–3).
-/

public section

namespace Cslib.Circuits.Boolean.Rectifier

open Finset

/-- The pure disjunction signature: the operation `m` is disjunction of `m` arguments. -/
abbrev signature : Signature where
  Op := ℕ
  Arity := id

/-- The Boolean meaning of a rectifier gate. The nullary gate is `false`. -/
@[expose] def interpretation : Interpretation signature Bool :=
  fun m => Unbounded.interpretation (.or m)

/-- The arity-preserving inclusion of rectifier gates into the unbounded Boolean basis. -/
@[expose] def toUnbounded : signature.Hom Unbounded.signature :=
  ⟨Unbounded.Op.or, fun _ => rfl⟩

/-- The inclusion into the unbounded Boolean basis preserves gate meanings. -/
instance : toUnbounded.Preserves interpretation Unbounded.interpretation where
  interpret_eq _ _ := rfl

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
between an input and an output, which would not be distinct poles in the source model. -/
@[expose] def IsTwoLayer (c : Circuit signature p q) : Prop :=
  ∃ (k : ℕ) (inputs : Matrix (Fin p) (Fin k) Bool) (outputs : Matrix (Fin k) (Fin q) Bool),
    c = (layer outputs).comp (layer inputs)

/-- Two matrix layers have native circuit depth at most two. -/
theorem IsTwoLayer.depth_le {c : Circuit signature p q} (hc : IsTwoLayer c) : c.depth ≤ 2 := by
  obtain ⟨k, inputs, outputs, rfl⟩ := hc
  exact (Circuit.depth_comp_le _ _).trans
    (Nat.add_le_add (depth_layer_le _) (depth_layer_le _))

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

/-- The row-pattern construction has depth at most two. -/
theorem depth_rowPatternCircuit_le (A : Matrix (Fin p) (Fin q) Bool) :
    (rowPatternCircuit A).depth ≤ 2 :=
  (isTwoLayer_rowPatternCircuit A).depth_le

/-- **Lupanov's row-pattern bound** [Lupanov1956, §2, unnamed lemma, pp. 1171–1172]: every
Boolean `p × q` matrix has a rectifier circuit of depth at most two using at most
`p + q * 2 ^ (q - 1)` wires. The matrix convention is `p` inputs and `q` outputs. Both dimensions
may be zero; nullary disjunctions represent outputs with no incoming paths. -/
theorem exists_depth_two (A : Matrix (Fin p) (Fin q) Bool) :
    ∃ c : Circuit signature p q,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧ c.depth ≤ 2 ∧
        c.program.cost id ≤ p + q * 2 ^ (q - 1) :=
  ⟨rowPatternCircuit A, isTwoLayer_rowPatternCircuit A, eval_rowPatternCircuit A,
    depth_rowPatternCircuit_le A, (cost_rowPatternCircuit A).le⟩

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

/-- Block synthesis with no wires to the padded columns: `⌈q / s⌉ * p` wires enter the row
classes and `q * 2 ^ (s - 1)` wires enter the original outputs. This strengthens the uniform
block budget in Lupanov's construction by omitting unused terminal gates. -/
theorem exists_depth_two_blocked_exact (A : Matrix (Fin p) (Fin q) Bool) {s : ℕ} (hs : 0 < s) :
    ∃ c : Circuit signature p q,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧ c.depth ≤ 2 ∧
        c.program.cost id = (q ⌈/⌉ s) * p + q * 2 ^ (s - 1) := by
  have hq : q ≤ (q ⌈/⌉ s) * s := by
    simpa only [smul_eq_mul, Nat.mul_comm] using (le_smul_ceilDiv hs : q ≤ s • (q ⌈/⌉ s))
  let padded : Matrix (Fin p) (Fin ((q ⌈/⌉ s) * s)) Bool :=
    Matrix.of fun i j => if h : j.val < q then A i ⟨j.val, h⟩ else false
  refine ⟨blockCircuit padded (Fin.castLE hq), isTwoLayer_blockCircuit _ _, ?_,
    (isTwoLayer_blockCircuit _ _).depth_le, cost_blockCircuit _ _⟩
  intro x
  rw [eval_blockCircuit]
  funext j
  simp only [matrixAction, padded, Matrix.of_apply, Fin.val_castLE, j.isLt, dite_true]

/-- The finite block construction underlying [Lupanov1956, §2, Theorem 1, p. 1172]. Splitting
the `q` columns into `⌈q / s⌉` blocks and applying the row-pattern construction to each block
gives a depth-two rectifier circuit with at most `⌈q / s⌉ * (p + s * 2 ^ (s - 1))` wires.
The last block is padded with zero columns. This is the finite construction used in the
asymptotic theorem; the statement makes no asymptotic or optimality claim. -/
theorem exists_depth_two_blocked (A : Matrix (Fin p) (Fin q) Bool) {s : ℕ} (hs : 0 < s) :
    ∃ c : Circuit signature p q,
      IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧ c.depth ≤ 2 ∧
        c.program.cost id ≤ (q ⌈/⌉ s) * (p + s * 2 ^ (s - 1)) := by
  obtain ⟨c, hl, hc, hd, hw⟩ := exists_depth_two_blocked_exact A hs
  refine ⟨c, hl, hc, hd, ?_⟩
  rw [hw, Nat.mul_add, ← Nat.mul_assoc]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  have hq : q ≤ (q ⌈/⌉ s) * s := by
    simpa only [smul_eq_mul, Nat.mul_comm] using (le_smul_ceilDiv hs : q ≤ s • (q ⌈/⌉ s))
  exact hq

end Cslib.Circuits.Boolean.Rectifier
