/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.MapLines
public import CslibFrontier.Computability.Circuit.SimulationDepth
import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Unfolding
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Simulating unbounded fan-in with fan-in two

A disjunction of `k ≥ 1` arguments is a balanced tree of `k - 1` disjunctions of fan-in two, of
depth `⌈log₂ k⌉` (`Formula.size_orList_add_one`, `Formula.depthWith_orList_le`), and so is a
conjunction. Replacing every gate of a circuit over the unbounded fan-in basis by such a tree
gives a De Morgan circuit for the same function. A gate may read one wire many times, so its
fan-in is not bounded by the size of the circuit; but a conjunction or a disjunction keeps its
value when it reads each of its wires once, so every circuit with `n` inputs and `s` gates has an
equivalent circuit of the same size and no larger depth whose gates have fan-in at most `n + s`
(`Unbounded.dedup`). Unfolding it gives a formula of the same depth with at most
`(10 (n + s)) ^ d` nodes (`Unbounded.exists_formula_size_add_leafSize_le`). Replacing the gates of
`dedup C` by balanced trees gives a De Morgan circuit with at most `s (n + s)` gates and depth
at most `max 1 ⌈log₂ (n + s)⌉ · d` (`Unbounded.exists_deMorgan_simulation`).

For circuits of polynomial size `log (n + s)` is `O(log n)`, so polynomial-size circuits of depth
`O((log n) ^ i)` and unbounded fan-in become polynomial-size circuits of fan-in two and depth
`O((log n) ^ (i + 1))`: **ACⁱ ⊆ NCⁱ⁺¹** (`AC_subset_NC_succ`)
[Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]. With
`NCⁱ ⊆ ACⁱ`, the two hierarchies have the same union (`iUnion_NC_eq_iUnion_AC`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.dedupLine`, `Cslib.Circuits.Boolean.Unbounded.dedup`: the line
  and circuit whose gates read their distinct wires, each once.
* `Cslib.Circuits.Boolean.Unbounded.Op.deMorganFormula`: a De Morgan formula for each operation of
  the unbounded fan-in basis.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_dedup`, `Cslib.Circuits.Boolean.Unbounded.depth_dedup_le`,
  `Cslib.Circuits.Boolean.Unbounded.fanInAtMost_dedup`: reading every wire once keeps the function
  and the size, makes no gate deeper, and bounds the fan-in by the number of inputs and gates.
* `Cslib.Circuits.Boolean.Unbounded.exists_formula_size_add_leafSize_le`: a circuit with `S` nodes
  and depth `d` unfolds into a formula of depth `d` with at most `(10 S) ^ d` nodes
  [Arora and Barak, Exercise 13.2].
* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation`: a circuit of unbounded fan-in
  with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan circuit with at most
  `s (n + s)` gates and depth at most `max 1 ⌈log₂ (n + s)⌉ · d`.
* `Cslib.Circuits.Boolean.AC_subset_NC_succ`: **ACⁱ ⊆ NCⁱ⁺¹**.
* `Cslib.Circuits.Boolean.AC0_subset_NC_one`: **AC⁰ ⊆ NC¹**.
* `Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC`: **NC = AC**.
* `Cslib.Circuits.Boolean.AC_subset_PPoly`: **ACⁱ ⊆ P/poly**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean

namespace Unbounded

variable {n g m : ℕ}

/-! ### Reading every wire once -/

private theorem forall_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∀ j, P ((List.ofFn w).dedup.get j)) ↔ ∀ j, P (w j) := by
  rw [← List.forall_mem_iff_get, ← List.forall_mem_ofFn_iff]
  simp only [List.mem_dedup]

private theorem exists_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∃ j, P ((List.ofFn w).dedup.get j)) ↔ ∃ j, P (w j) := by
  rw [← List.exists_mem_iff_get]
  simp [List.mem_dedup, List.mem_ofFn']

/-- The line reading the distinct wires of `line`, each once. A conjunction or a disjunction does
not depend on how often it reads a wire, so this keeps the value of the line. -/
def dedupLine : Line signature n g → Line signature n g
  | ⟨.not, w⟩ => ⟨.not, w⟩
  | ⟨.and _, w⟩ => ⟨.and (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩
  | ⟨.or _, w⟩ => ⟨.or (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩

/-- Reading every wire once keeps the value of a line. -/
theorem eval_dedupLine (line : Line signature n g) (x : Fin n → Bool) (gates : Fin g → Bool) :
    (dedupLine line).eval interpretation x gates = line.eval interpretation x gates := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => rfl
  | and k =>
    exact decide_eq_decide.2 (forall_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)
  | or k =>
    exact decide_eq_decide.2 (exists_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)

/-- Reading every wire once makes no line deeper. -/
theorem depth_dedupLine_le (line : Line signature n g) (depths : Wire n g → ℕ) :
    (dedupLine line).depth depths ≤ line.depth depths := by
  have hpos := line.depth_pos depths
  have hle : ∀ a, depths (line.wires a) ≤ line.depth depths - 1 := fun a => by
    have := line.wireDepth_lt_depth depths a
    omega
  refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 ?_).trans
    (by omega)
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact hle
  | and _ | or _ => exact (forall_get_dedup_ofFn_iff w fun a => depths a ≤ _).2 hle

/-- A line reading every wire once reads at most all `n + g` wires. -/
theorem arity_dedupLine_le (line : Line signature n g) :
    signature.Arity (dedupLine line).op ≤ n + g := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact (Fintype.card_pos_iff.2 ⟨w 0⟩).trans_eq Wire.card
  | and _ | or _ => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card

/-- The gates of a program reading every wire once read at most all wires. -/
private theorem arity_lines_mapLines_dedupLine_le (p : Program signature n g) (k : Fin g) :
    signature.Arity ((p.mapLines dedupLine).lines k).op ≤ n + g := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapLines_gate, Program.lines_gate_last, Line.mapWires_op]
      exact (arity_dedupLine_le line).trans (Nat.le_succ _)
    | cast k =>
      rw [Program.mapLines_gate, Program.lines_gate_castSucc, Line.mapWires_op]
      exact (ih k).trans (Nat.le_succ _)

/-- The circuit whose gates read their distinct wires, each once. It computes the same function
(`eval_dedup`) with the same size and no larger depth (`depth_dedup_le`), and its gates have
fan-in at most the number of inputs and gates (`fanInAtMost_dedup`). -/
def dedup (C : Circuit signature n m) : Circuit signature n m :=
  C.mapLines dedupLine

/-- Reading every wire once keeps the size. -/
@[simp] theorem size_dedup (C : Circuit signature n m) : (dedup C).size = C.size :=
  rfl

/-- Reading every wire once keeps the function computed. -/
@[simp] theorem eval_dedup (C : Circuit signature n m) :
    (dedup C).eval interpretation = C.eval interpretation :=
  Circuit.eval_mapLines eval_dedupLine C

/-- Reading every wire once makes no gate deeper. -/
theorem depth_dedup_le (C : Circuit signature n m) : (dedup C).depth ≤ C.depth :=
  Circuit.depth_mapLines_le depth_dedupLine_le C

/-- Every gate of `dedup C` reads at most all `n + C.size` wires. -/
theorem arity_lines_dedup_le (C : Circuit signature n m) (k : Fin C.size) :
    signature.Arity ((dedup C).program.lines k).op ≤ n + C.size :=
  arity_lines_mapLines_dedupLine_le C.program k

/-- **Fan-in reduction**: the gates of `dedup C` have fan-in at most the number of inputs and
gates of `C`. -/
theorem fanInAtMost_dedup (C : Circuit signature n m) : (dedup C).FanInAtMost (n + C.size) :=
  Program.fanInAtMost_iff.2 (arity_lines_dedup_le C)

/-- **Circuits to formulas in AC⁰** [Arora and Barak, Exercise 13.2][AroraBarak09]. An output of
a circuit of unbounded fan-in with `n` inputs, `s` gates and depth `d` is computed by a formula
over the same basis, a circuit in which every gate has fan-out one, of depth at most `d` and with
at most `(10 S) ^ d` nodes, operations and input leaves together, where `S = n + s` is the number
of nodes of the circuit, the size in the draft's Definition 6.1.

The formula unfolds `dedup C`, whose gates have fan-in at most `S`. -/
theorem exists_formula_size_add_leafSize_le (C : Circuit signature n m) (j : Fin m) :
    ∃ F : Formula signature n, (∀ x, F.eval interpretation x = C.eval interpretation x j) ∧
      F.depth ≤ C.depth ∧ F.size + F.leafSize ≤ (10 * (n + C.size)) ^ C.depth := by
  set S := n + C.size
  set F := (dedup C).toFormula j
  have hS : 1 ≤ S := by
    cases C.outputs j with
    | input i => have := i.pos; omega
    | gate k => have := k.pos; omega
  have hD : F.depth ≤ C.depth := ((dedup C).depth_toFormula_le j).trans (depth_dedup_le C)
  refine ⟨F, fun x => by rw [Circuit.eval_toFormula, eval_dedup], hD, ?_⟩
  set r := max 2 S
  have hF : F.FanInAtMost r :=
    (dedup C).fanInAtMost_toFormula j
      (Program.fanInAtMost_iff.2 fun k => (arity_lines_dedup_le C k).trans (le_max_right _ _))
  have hsize := Formula.size_lt_pow_depth hF (le_max_left _ _)
  have hleaf := Formula.leafSize_le_pow_depth hF
  have h10 : 1 ≤ 10 * S := by omega
  rcases Nat.eq_zero_or_pos F.depth with h0 | hpos
  · rw [h0, pow_zero] at hsize hleaf
    exact (by omega : F.size + F.leafSize ≤ 1).trans (Nat.one_le_pow _ _ h10)
  calc F.size + F.leafSize ≤ 2 * r ^ F.depth := by omega
    _ ≤ 2 ^ F.depth * r ^ F.depth := Nat.mul_le_mul_right _ (Nat.le_self_pow hpos.ne' 2)
    _ = (2 * r) ^ F.depth := (Nat.mul_pow _ _ _).symm
    _ ≤ (10 * S) ^ F.depth := Nat.pow_le_pow_left (by omega) _
    _ ≤ (10 * S) ^ C.depth := Nat.pow_le_pow_right h10 hD

/-! ### Balanced trees for the gates -/

/-- A De Morgan formula for each operation of the unbounded fan-in basis: the negation of the
input, and the balanced conjunction and disjunction of the inputs. -/
def Op.deMorganFormula : (op : Op) → Formula Boolean.signature op.arity
  | .not => (Formula.input 0).not
  | .and _ => Formula.andList (List.ofFn Formula.input)
  | .or _ => Formula.orList (List.ofFn Formula.input)

/-- The De Morgan formula of an operation computes it. -/
theorem Op.computes_deMorganFormula (op : Op) :
    op.deMorganFormula.Computes Boolean.interpretation (interpretation op) := fun x => by
  cases op with
  | not => rfl
  | and k =>
    rw [deMorganFormula, Formula.eval_andList, interpretation_and, Bool.eq_iff_iff,
      List.all_eq_true]
    simp
  | or k =>
    rw [deMorganFormula, Formula.eval_orList, interpretation_or, Bool.eq_iff_iff,
      List.any_eq_true]
    simp

/-- The De Morgan formula of an operation of `k` arguments has at most `max 1 k` nodes: one
negation, a constant for no arguments, and `k - 1` binary gates for `k ≥ 1` arguments. -/
theorem Op.size_deMorganFormula_le (op : Op) : op.deMorganFormula.size ≤ max 1 op.arity := by
  have step {k : ℕ} {f : Formula Boolean.signature k}
      (h : f.size + 1 = ((List.ofFn (Formula.input (σ := Boolean.signature) (n := k))).map
        Formula.size).sum + (List.ofFn (Formula.input (σ := Boolean.signature) (n := k))).length) :
      f.size ≤ max 1 k := by
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Formula.size_input,
      Finset.sum_const_zero, List.length_ofFn, zero_add] at h
    omega
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · exact step (Formula.size_andList_add_one (by simpa using hk.ne'))
  | or k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · exact step (Formula.size_orList_add_one (by simpa using hk.ne'))

/-- The De Morgan formula of an operation of `k` arguments has depth at most `max 1 ⌈log₂ k⌉`:
one for a negation or a constant, and `⌈log₂ k⌉` for a balanced tree of `k ≥ 1` arguments. -/
theorem Op.depth_deMorganFormula_le (op : Op) :
    op.deMorganFormula.depth ≤ max 1 (Nat.clog 2 op.arity) := by
  have step {k : ℕ} {f : Formula Boolean.signature k} {op' : Boolean.signature.Op}
      (h : f.depthWith 1 ≤ 0 + (1 : Boolean.signature.Op → ℕ) op' *
        Nat.clog 2 (List.ofFn (Formula.input (σ := Boolean.signature) (n := k))).length) :
      f.depth ≤ max 1 (Nat.clog 2 k) := by
    simp only [Formula.depthWith_one, List.length_ofFn, Pi.one_apply, one_mul, zero_add] at h
    exact h.trans (le_max_right _ _)
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · exact step (Formula.depthWith_andList_le (cost := 1) (d := 0) (by simp)
        (by simpa using hk.ne'))
  | or k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · exact step (Formula.depthWith_orList_le (cost := 1) (d := 0) (by simp)
        (by simpa using hk.ne'))

/-! ### Simulation -/

/-- **Fan-in two simulates unbounded fan-in** [Arora and Barak, Section 6.7][AroraBarak09]: a
circuit of unbounded fan-in with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan
circuit with at most `s (n + s)` gates and depth at most `max 1 ⌈log₂ (n + s)⌉ · d`. Its gates are
first made to read every wire once (`dedup`), and then replaced by balanced trees. -/
theorem exists_deMorgan_simulation (C : Circuit signature n m) :
    ∃ D : Circuit Boolean.signature n m, D.eval Boolean.interpretation = C.eval interpretation ∧
      D.size ≤ C.size * (n + C.size) ∧
      D.depth ≤ max 1 (Nat.clog 2 (n + C.size)) * C.depth := by
  refine ⟨(dedup C).simulate fun op => op.deMorganFormula.toCircuit, ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ fun op => (Op.computes_deMorganFormula op).toCircuit, eval_dedup]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => n + C.size) fun k _ => ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_dedup])
    rw [Formula.size_toCircuit]
    have hk : 1 ≤ n + C.size := by have := k.pos; simp only [size_dedup] at this; omega
    exact (Op.size_deMorganFormula_le _).trans
      (max_le hk (arity_lines_dedup_le C k))
  · refine (Circuit.depth_simulate_le _ _).trans
      ((Circuit.depthWith_le_mul_depth _ fun k => ?_).trans
        (Nat.mul_le_mul_left _ (depth_dedup_le C)))
    exact (Formula.depth_toCircuit_le _).trans ((Op.depth_deMorganFormula_le _).trans
      (max_le_max le_rfl (Nat.clog_mono_right 2 (arity_lines_dedup_le C k))))

end Unbounded

/-! ### ACⁱ ⊆ NCⁱ⁺¹ -/

/-- **ACⁱ ⊆ NCⁱ⁺¹** [Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]:
polynomial-size circuits of depth `O((log n) ^ i)` and unbounded fan-in are simulated by
polynomial-size circuits of depth `O((log n) ^ (i + 1))` and fan-in two. -/
theorem AC_subset_NC_succ (i : ℕ) : AC i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log (s := fun n => n + s n)
    (by fun_prop)
  refine ⟨c * (e + 1), fun n => s n * (n + s n), by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hlog : max 1 (Nat.clog 2 (n + C.size)) ≤ (e + 1) * (Nat.log 2 n + 1) := by
      have := (Nat.clog_mono_right 2 (Nat.add_le_add_left hCs n)).trans (he n)
      rw [add_one_mul]
      exact max_le (Nat.le_add_left_of_le (Nat.le_add_left 1 _)) (this.trans (Nat.le_add_right _ _))
    calc D.depth ≤ max 1 (Nat.clog 2 (n + C.size)) * C.depth := hDd
      _ ≤ ((e + 1) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := Nat.mul_le_mul hlog hCd
      _ = c * (e + 1) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · calc D.size ≤ C.size * (n + C.size) := hDs
      _ ≤ s n * (n + s n) := by gcongr

/-- **AC⁰ ⊆ NC¹.** -/
theorem AC0_subset_NC_one : AC0 ⊆ NC 1 :=
  AC_zero.symm.subset.trans (AC_subset_NC_succ 0)

/-- **NC = AC**: the NC and AC hierarchies have the same union. -/
theorem iUnion_NC_eq_iUnion_AC : ⋃ i, NC i = ⋃ i, AC i :=
  (Set.iUnion_mono NC_subset_AC).antisymm <| Set.iUnion_subset fun i =>
    (AC_subset_NC_succ i).trans (Set.subset_iUnion NC (i + 1))

/-- **`ACⁱ ⊆ P/poly`** for every `i`. -/
theorem AC_subset_PPoly (i : ℕ) : AC i ⊆ PPoly :=
  (AC_subset_NC_succ i).trans (NC_subset_PPoly (i + 1))

end Boolean

end Cslib.Circuits
