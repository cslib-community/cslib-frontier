/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnceParity
public import CslibFrontier.Computability.Circuit.Arithmetic.SyntacticMultilinear
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Data.Fin.VecNotation
import CslibFrontier.Foundations.Data.List.Filter

/-!
# Arithmetizing read-once parity branching programs

Over a commutative ring, a contact testing `x i = true` becomes the variable `X i`, a contact
testing `x i = false` becomes `1 - X i`, and a rectifier becomes `1`. Summing over the paths from a
node to the target the products of these *literals* (`Cslib.BranchingPrograms.NBP.litValue`) gives,
at a point of the Boolean cube, the number of paths that the point switches on [Volk, Section
2][Volk2026].

`Cslib.BranchingPrograms.NBP.toArith` computes these sums with an arithmetic circuit, one node
after the other: the value of a node is `0` plus, for each of its wires, the literal of the wire
times the value of its head (`Cslib.BranchingPrograms.NBP.termCircuit`). A wire is *kept*
(`Cslib.BranchingPrograms.NBP.Keeps`) when some path leads from its head to the target and the
coordinate it tests is tested on no such path. Dropping the other wires makes the circuit
syntactically multilinear (`Cslib.BranchingPrograms.NBP.isDecomposableAt_toArith`), and drops
nothing that matters in a read-once program: there the source computes the number of paths an input
switches on (`Cslib.BranchingPrograms.NBP.eval_toArith_bitPoint`). So the circuit computes the
multilinear extension of the path count (`Cslib.BranchingPrograms.NBP.eval_toArith_X`). It has at
most five gates for each wire and one for each node (`Cslib.BranchingPrograms.NBP.size_toArith_le`).

## Main definitions

* `Cslib.BranchingPrograms.NBP.litValue`: the literal of a wire.
* `Cslib.BranchingPrograms.NBP.termCircuit`: the gates adding the term of one wire.
* `Cslib.BranchingPrograms.NBP.Keeps`: the wires kept in the arithmetic circuit.
* `Cslib.BranchingPrograms.NBP.toArith`: the arithmetic circuit of a branching program.

## Main results

* `Cslib.BranchingPrograms.NBP.size_toArith_le`: its size.
* `Cslib.BranchingPrograms.NBP.isDecomposableAt_toArith`: it is syntactically multilinear.
* `Cslib.BranchingPrograms.NBP.eval_toArith_bitPoint`: for a read-once program it counts the
  switched-on paths at the Boolean points.
* `Cslib.BranchingPrograms.NBP.eval_toArith_X`: it computes the multilinear extension of the path
  count.
* `Cslib.BranchingPrograms.NBP.exists_syntacticallyMultilinear`: in characteristic two, read-once
  parity programs simulate syntactically multilinear circuits.

## References

* [B. L. Volk, *A Lower Bound for Read-Once Parity Branching Programs*][Volk2026]
-/

public section

namespace Cslib.BranchingPrograms

namespace NBP

open Cslib.Circuits MvPolynomial BitString

universe u

variable {N : ℕ}

/-! ### Literals and term circuits -/

/-- The literal of a wire at the point `x`: `1` for a rectifier, `x i` for a contact testing
`x i = true`, and `1 - x i` for a contact testing `x i = false`. -/
@[expose]
def litValue {A : Type*} [CommRing A] (x : Fin N → A) : Option (Fin N × Bool) → A
  | none => 1
  | some (i, true) => x i
  | some (i, false) => 1 - x i

/-- At a Boolean point the literal of a wire is `1` when the point switches the wire on, and `0`
otherwise. -/
theorem litValue_bitPoint {A : Type*} [CommRing A] {n : ℕ} (x : Fin N → Bool)
    (w : Wire (Fin N) Bool n) : litValue (bitPoint x : Fin N → A) w.label = bitVal A (w.on x) := by
  obtain ⟨_, _ | ⟨i, b⟩⟩ := w
  · simp [litValue, Wire.on, bitVal]
  · cases b <;> cases hx : x i <;> simp [litValue, Wire.on, bitVal, hx]

/-- The coordinates tested by a wire label. -/
@[expose]
def litVars : Option (Fin N × Bool) → Finset (Fin N)
  | none => ∅
  | some (i, _) => {i}

variable (R : Type u) [CommRing R]

/-- The input of a term circuit carrying the variable `X i`. -/
abbrev varIn (i : Fin N) : Fin (N + 2) := Fin.castAdd 2 i

/-- The input of a term circuit carrying the sum so far. -/
abbrev accIn : Fin (N + 2) := Fin.natAdd N 0

/-- The input of a term circuit carrying the value of the head of the wire. -/
abbrev headIn : Fin (N + 2) := Fin.natAdd N 1

/-- The gates adding to the sum so far the literal of a wire times the value of its head: one
addition for a rectifier, a multiplication and an addition for a positive contact, and five gates
computing `acc + (head + (-1) * (x i * head))` for a negative contact. -/
@[expose]
def termCircuit : Option (Fin N × Bool) → Circuit (arithSignature R) (N + 2) 1
  | none => ⟨(Program.empty : Program (arithSignature R) (N + 2) 0).gate
      ⟨ArithOp.add, ![Wire.input accIn, Wire.input headIn]⟩, fun _ => Wire.gate 0⟩
  | some (i, true) => ⟨((Program.empty : Program (arithSignature R) (N + 2) 0).gate
      ⟨ArithOp.mul, ![Wire.input (varIn i), Wire.input headIn]⟩).gate
      ⟨ArithOp.add, ![Wire.input accIn, Wire.gate 0]⟩, fun _ => Wire.gate 1⟩
  | some (i, false) => ⟨(((((Program.empty : Program (arithSignature R) (N + 2) 0).gate
      ⟨ArithOp.mul, ![Wire.input (varIn i), Wire.input headIn]⟩).gate
      ⟨ArithOp.const (-1), Fin.elim0⟩).gate ⟨ArithOp.mul, ![Wire.gate 1, Wire.gate 0]⟩).gate
      ⟨ArithOp.add, ![Wire.input headIn, Wire.gate 2]⟩).gate
      ⟨ArithOp.add, ![Wire.input accIn, Wire.gate 3]⟩, fun _ => Wire.gate 4⟩

/-- A term circuit has at most five gates. -/
theorem size_termCircuit_le (l : Option (Fin N × Bool)) : (termCircuit R l).size ≤ 5 := by
  rcases l with _ | ⟨i, _ | _⟩ <;> simp [termCircuit]

/-- A term circuit adds the literal times the head to the sum, in every `R`-algebra. -/
theorem eval_termCircuit (A : Type*) [CommRing A] [Algebra R A] (l : Option (Fin N × Bool))
    (y : Fin (N + 2) → A) :
    (termCircuit R l).eval (arithInterpretationWith R (algebraMap R A)) y 0 =
      y accIn + litValue (fun i => y (varIn i)) l * y headIn := by
  rcases l with _ | ⟨i, _ | _⟩
  · change y accIn + y headIn = _
    simp [litValue]
  · change y accIn + (y headIn + algebraMap R A (-1) * (y (varIn i) * y headIn)) = _
    simp only [litValue, map_neg, map_one]
    ring
  · change y accIn + y (varIn i) * y headIn = _
    rfl

/-- The output of a term circuit is reached by the sum so far, the head, and the variable tested
by the wire. -/
theorem wireSupport_termCircuit_subset (l : Option (Fin N × Bool)) :
    (termCircuit R l).program.wireSupport ((termCircuit R l).outputs 0) ⊆
      {accIn, headIn} ∪ (litVars l).image varIn := by
  rcases l with _ | ⟨i, _ | _⟩
  · change Finset.univ.biUnion ![{accIn}, {headIn}] ⊆ _
    intro j
    simp [Fin.exists_fin_two]
    tauto
  · change Finset.univ.biUnion ![{accIn}, Finset.univ.biUnion ![{headIn},
      Finset.univ.biUnion ![Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin (N + 2))),
        Finset.univ.biUnion ![{varIn i}, {headIn}]]]] ⊆ _
    intro j
    simp [Fin.exists_fin_two, litVars]
    tauto
  · change Finset.univ.biUnion ![{accIn}, Finset.univ.biUnion ![{varIn i}, {headIn}]] ⊆ _
    intro j
    simp [Fin.exists_fin_two, litVars]
    tauto

/-- The multiplications of a term circuit are decomposable when the variable tested by the wire does
not reach the head. -/
theorem decomposesOver_termCircuit {n' : ℕ} (l : Option (Fin N × Bool))
    (S : Fin (N + 2) → Finset (Fin n')) (hS : ∀ i ∈ litVars l, Disjoint (S (varIn i)) (S headIn)) :
    (termCircuit R l).program.DecomposesOver (· = .mul) S := by
  rcases l with _ | ⟨i, _ | _⟩
  · simp [termCircuit]
  · have h1 : (((Program.empty : Program (arithSignature R) (N + 2) 0).gate
        ⟨ArithOp.mul, ![Wire.input (varIn i), Wire.input headIn]⟩).gate
        ⟨ArithOp.const (-1), Fin.elim0⟩).wireSupport (Wire.gate 1) = ∅ := by
      change Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin (N + 2))) = ∅
      simp
    have hi := hS i (by simp [litVars])
    simp [termCircuit, Program.decomposesOver_gate_iff, Pairwise, Fin.forall_fin_two, h1, hi,
      hi.symm]
  · have hi := hS i (by simp [litVars])
    simp [termCircuit, Program.decomposesOver_gate_iff, Pairwise, Fin.forall_fin_two, hi, hi.symm]

/-! ### Appending terms -/

/-- The wires feeding a term circuit: the inputs for the variables, then the sum so far and the
head. -/
@[expose]
def termFeed {g : ℕ} (acc head : Circuits.Wire N g) : Fin (N + 2) → Circuits.Wire N g :=
  Fin.addCases (fun i => Circuits.Wire.input i) ![acc, head]

@[simp] theorem termFeed_varIn {g : ℕ} (acc head : Circuits.Wire N g) (i : Fin N) :
    termFeed acc head (varIn i) = Circuits.Wire.input i := by
  simp [termFeed, varIn]

@[simp] theorem termFeed_accIn {g : ℕ} (acc head : Circuits.Wire N g) :
    termFeed acc head accIn = acc := by
  simp [termFeed, accIn]

@[simp] theorem termFeed_headIn {g : ℕ} (acc head : Circuits.Wire N g) :
    termFeed acc head headIn = head := by
  simp [termFeed, headIn]

/-- A program continuing a program with `g` gates: its gates, the wire carrying a sum, and the
embedding of the wires of the original program. -/
structure TermExtension (N g : ℕ) where
  /-- The number of gates. -/
  {size : ℕ}
  /-- The continued program. -/
  program : Program (arithSignature R) N size
  /-- The wire carrying the sum. -/
  sum : Circuits.Wire N size
  /-- The wire of the continued program carrying each wire of the original one. -/
  embed : Circuits.Wire N g → Circuits.Wire N size

/-- Append to `p` the term circuits of the terms `ts`. Each term is a wire label and a wire of a
base program, embedded into `p` by `emb`; its circuit adds the literal of the label times the value
of the wire to the sum so far, starting from `acc`. Returns the new program, the wire carrying the
final sum, and the embedding of the wires of `p`. -/
@[expose]
def appendTerms {g₀ : ℕ} : List (Option (Fin N × Bool) × Circuits.Wire N g₀) →
    {g : ℕ} → Program (arithSignature R) N g → Circuits.Wire N g →
      (Circuits.Wire N g₀ → Circuits.Wire N g) → TermExtension R N g
  | [], _, p, acc, _ => ⟨p, acc, id⟩
  | (l, h) :: ts, _, p, acc, emb =>
    let c := termCircuit R l
    let feed := termFeed acc (emb h)
    let r := appendTerms ts (p.append feed c.program) (Program.appendedWire feed (c.outputs 0))
      fun w => (emb w).castAdd c.size
    ⟨r.program, r.sum, r.embed ∘ fun w => w.castAdd c.size⟩

variable {R}

/-- Appending terms keeps the values of the wires of `p`. -/
theorem trace_appendTerms_embed {g₀ : ℕ} {U : Type*} (I : Interpretation (arithSignature R) U)
    (x : Fin N → U) : ∀ (ts : List (Option (Fin N × Bool) × Circuits.Wire N g₀)) {g : ℕ}
      (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
      (emb : Circuits.Wire N g₀ → Circuits.Wire N g) (w : Circuits.Wire N g),
      (appendTerms R ts p acc emb).program.trace I x ((appendTerms R ts p acc emb).embed w) =
        p.trace I x w
  | [], _, _, _, _, _ => rfl
  | (_, _) :: ts, _, p, _, _, w =>
    (trace_appendTerms_embed I x ts _ _ _ _).trans (Program.trace_append_castAdd p _ I x _ w)

/-- Appending terms keeps the supports of the wires of `p`. -/
theorem wireSupport_appendTerms_embed {g₀ : ℕ} (ts : List (Option (Fin N × Bool) ×
    Circuits.Wire N g₀)) {g : ℕ} (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
    (emb : Circuits.Wire N g₀ → Circuits.Wire N g) (w : Circuits.Wire N g) :
    (appendTerms R ts p acc emb).program.wireSupport ((appendTerms R ts p acc emb).embed w) =
      p.wireSupport w :=
  trace_appendTerms_embed _ _ ts p acc emb w

/-- Appending terms adds at most five gates for each term. -/
theorem size_appendTerms_le {g₀ : ℕ} : ∀ (ts : List (Option (Fin N × Bool) ×
    Circuits.Wire N g₀)) {g : ℕ} (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
    (emb : Circuits.Wire N g₀ → Circuits.Wire N g),
    (appendTerms R ts p acc emb).size ≤ g + 5 * ts.length
  | [], _, _, _, _ => by simp [appendTerms]
  | (l, h) :: ts, g, p, acc, emb => by
    have := size_appendTerms_le ts (p.append (termFeed acc (emb h)) (termCircuit R l).program)
      (Program.appendedWire (termFeed acc (emb h)) ((termCircuit R l).outputs 0))
      fun w => (emb w).castAdd _
    have hl := size_termCircuit_le R l
    simp only [appendTerms, List.length_cons] at this ⊢
    omega

/-- **The value of the sum.** In every `R`-algebra, the final sum is the initial one plus, for each
term, the literal of its label times the value of its wire. -/
theorem trace_appendTerms_acc {g₀ : ℕ} (A : Type*) [CommRing A] [Algebra R A] (x : Fin N → A) :
    ∀ (ts : List (Option (Fin N × Bool) × Circuits.Wire N g₀)) {g : ℕ}
      (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
      (emb : Circuits.Wire N g₀ → Circuits.Wire N g),
      (appendTerms R ts p acc emb).program.trace (arithInterpretationWith R (algebraMap R A)) x
          (appendTerms R ts p acc emb).sum =
        p.trace (arithInterpretationWith R (algebraMap R A)) x acc + (ts.map fun t =>
          litValue x t.1 * p.trace (arithInterpretationWith R (algebraMap R A)) x (emb t.2)).sum
  | [], _, _, _, _ => by simp [appendTerms]
  | (l, h) :: ts, _, p, acc, emb => by
    rw [appendTerms, trace_appendTerms_acc A x ts, List.map_cons, List.sum_cons,
      Program.trace_append_appendedWire]
    change (termCircuit R l).eval _ _ 0 + _ = _
    rw [eval_termCircuit]
    simp only [termFeed_accIn, termFeed_headIn, termFeed_varIn, Program.trace_input,
      Program.trace_append_castAdd]
    ring

/-- The final sum is reached only by inputs reaching the initial sum, the wires of the terms, or the
variables of their labels. -/
theorem wireSupport_appendTerms_acc_subset {g₀ : ℕ} (T : Finset (Fin N)) :
    ∀ (ts : List (Option (Fin N × Bool) × Circuits.Wire N g₀)) {g : ℕ}
      (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
      (emb : Circuits.Wire N g₀ → Circuits.Wire N g), p.wireSupport acc ⊆ T →
      (∀ t ∈ ts, litVars t.1 ⊆ T ∧ p.wireSupport (emb t.2) ⊆ T) →
      (appendTerms R ts p acc emb).program.wireSupport (appendTerms R ts p acc emb).sum ⊆ T
  | [], _, _, _, _, hacc, _ => hacc
  | (l, h) :: ts, _, p, acc, emb, hacc, hts => by
    have hlh := hts (l, h) List.mem_cons_self
    dsimp only [appendTerms]
    refine wireSupport_appendTerms_acc_subset T ts _ _ _ ?_ fun t ht => ?_
    · rw [Program.wireSupport_append_appendedWire]
      intro j hj
      obtain ⟨a, ha, hja⟩ := Finset.mem_biUnion.mp hj
      rcases Finset.mem_union.mp (wireSupport_termCircuit_subset R l ha) with ha | ha
      · rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hacc (by simpa using hja)
        · rw [Finset.mem_singleton.mp ha] at hja
          exact hlh.2 (by simpa using hja)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        simp only [termFeed_varIn, Program.wireSupport_input, Finset.mem_singleton] at hja
        exact hlh.1 (hja ▸ hi)
    · refine ⟨(hts t (List.mem_cons_of_mem _ ht)).1, ?_⟩
      rw [Program.wireSupport_append_castAdd]
      exact (hts t (List.mem_cons_of_mem _ ht)).2

/-- Appending terms keeps a program syntactically multilinear when the variable of each label does
not reach the wire of its term. -/
theorem isDecomposableAt_appendTerms {g₀ : ℕ} :
    ∀ (ts : List (Option (Fin N × Bool) × Circuits.Wire N g₀)) {g : ℕ}
      (p : Program (arithSignature R) N g) (acc : Circuits.Wire N g)
      (emb : Circuits.Wire N g₀ → Circuits.Wire N g), p.IsDecomposableAt (· = .mul) →
      (∀ t ∈ ts, ∀ i ∈ litVars t.1, i ∉ p.wireSupport (emb t.2)) →
      (appendTerms R ts p acc emb).program.IsDecomposableAt (· = .mul)
  | [], _, _, _, _, hp, _ => hp
  | (l, h) :: ts, _, p, acc, emb, hp, hts => by
    dsimp only [appendTerms]
    refine isDecomposableAt_appendTerms ts _ _ _ ?_ fun t ht i hi => ?_
    · rw [Program.isDecomposableAt_append_iff]
      refine ⟨hp, decomposesOver_termCircuit R l _ fun i hi => ?_⟩
      simp only [termFeed_varIn, Program.wireSupport_input, termFeed_headIn,
        Finset.disjoint_singleton_left]
      exact hts (l, h) List.mem_cons_self i hi
    · rw [Program.wireSupport_append_castAdd]
      exact hts t (List.mem_cons_of_mem _ ht) i hi

/-! ### The circuit of a branching program -/

variable {n : ℕ}

/-- The source of a program: its last node. -/
@[expose]
def source : {n : ℕ} → NBP (Fin N) Bool n → Fin n
  | _, target => 0
  | _, node _ _ => Fin.last _

/-- The routes of a program are the paths from its source. -/
theorem routes_eq_tests_source (P : NBP (Fin N) Bool n) : P.routes = P.tests P.source := by
  cases P with
  | target => rfl
  | node P wires => exact routes_node P wires

/-- The path count of a program is the number of switched-on paths from its source. -/
theorem pathCount_eq_paths_source (P : NBP (Fin N) Bool n) (x : Fin N → Bool) :
    P.pathCount x = P.paths x P.source := by
  cases P with
  | target => rfl
  | node P wires => exact (paths_node_last P wires x).symm

/-- The coordinates tested on the paths from `v` to the target. -/
@[expose]
def testVars (P : NBP (Fin N) Bool n) (v : Fin n) : Finset (Fin N) :=
  ((P.tests v).flatMap fun l => l.map Prod.fst).toFinset

/-- No coordinate is tested twice on a path from `v` to the target. -/
def ReadOnceFrom (P : NBP (Fin N) Bool n) (v : Fin n) : Prop :=
  ∀ l ∈ P.tests v, (l.map Prod.fst).Nodup

/-- A program is read-once when no coordinate is tested twice on a path from its source. -/
theorem isReadOnce_iff_readOnceFrom_source (P : NBP (Fin N) Bool n) :
    P.IsReadOnce ↔ P.ReadOnceFrom P.source := by
  rw [IsReadOnce, ReadOnceFrom, routes_eq_tests_source]

/-- The arithmetic circuit *keeps* a wire of `P` when some path leads from its head to the target
and the coordinate it tests is tested on no such path. -/
def Keeps (P : NBP (Fin N) Bool n) (w : Wire (Fin N) Bool n) : Prop :=
  P.tests w.head ≠ [] ∧ ∀ i ∈ litVars w.label, i ∉ P.testVars w.head

instance (P : NBP (Fin N) Bool n) : DecidablePred P.Keeps := fun w =>
  inferInstanceAs (Decidable (P.tests w.head ≠ [] ∧ ∀ i ∈ litVars w.label, i ∉ P.testVars w.head))

variable (R)

/-- An arithmetic program with a wire for each of `n` nodes. -/
structure NodeCircuit (N n : ℕ) where
  /-- The number of gates. -/
  {size : ℕ}
  /-- The program. -/
  program : Program (arithSignature R) N size
  /-- The wire carrying the value of each node. -/
  node : Fin n → Circuits.Wire N size

/-- The arithmetic program of a branching program and the wire carrying the value of each node:
`1` at the target, and at each later node `0` plus the terms of its kept wires. -/
@[expose]
def build : {n : ℕ} → NBP (Fin N) Bool n → NodeCircuit R N n
  | _, target => ⟨(Program.empty : Program (arithSignature R) N 0).gate
      ⟨ArithOp.const 1, Fin.elim0⟩, fun _ => Circuits.Wire.gate 0⟩
  | _, node P wires =>
    let b := build P
    let r := appendTerms R ((wires.filter fun w => decide (P.Keeps w)).map
      fun w => (w.label, b.node w.head)) (b.program.gate ⟨ArithOp.const 0, Fin.elim0⟩)
      (Circuits.Wire.gate (Fin.last _)) Circuits.Wire.castSucc
    ⟨r.program, Fin.lastCases r.sum fun v => r.embed (b.node v).castSucc⟩

/-- The *arithmetic circuit* of a branching program, read at its source. -/
@[expose]
def toArith (P : NBP (Fin N) Bool n) : Circuit (arithSignature R) N 1 :=
  ⟨(build R P).program, fun _ => (build R P).node P.source⟩

variable {R}

omit [CommRing R] in
/-- A constant gate is reached by no input. -/
private theorem wireSupport_const_last {g : ℕ} (p : Program (arithSignature R) N g) (c : R) :
    (p.gate ⟨ArithOp.const c, Fin.elim0⟩).wireSupport (Circuits.Wire.gate (Fin.last g)) = ∅ := by
  rw [Program.wireSupport_gate_last]
  simp [Line.inputSupport]

/-- The program of `P` has at most one gate for each node and five for each wire. -/
theorem size_build_le : ∀ {n : ℕ} (P : NBP (Fin N) Bool n), (build R P).size ≤ n + 5 * P.wireCount
  | _, target => le_rfl
  | _, node P wires => by
    have hP := size_build_le P
    have := size_appendTerms_le (R := R) ((wires.filter fun w => decide (P.Keeps w)).map
      fun w => (w.label, (build R P).node w.head)) ((build R P).program.gate ⟨ArithOp.const 0,
        Fin.elim0⟩) (Circuits.Wire.gate (Fin.last _)) Circuits.Wire.castSucc
    have hf := List.length_filter_le (fun w => decide (P.Keeps w)) wires
    simp only [build, wireCount, List.length_map] at this ⊢
    omega

/-- The value of a node is reached only by the coordinates tested below it. -/
theorem wireSupport_build_subset : ∀ {n : ℕ} (P : NBP (Fin N) Bool n) (v : Fin n),
    (build R P).program.wireSupport ((build R P).node v) ⊆ P.testVars v
  | _, target, _ => by
    change ((Program.empty : Program (arithSignature R) N 0).gate ⟨ArithOp.const 1,
      Fin.elim0⟩).wireSupport (Circuits.Wire.gate (Fin.last 0)) ⊆ _
    rw [wireSupport_const_last]
    exact Finset.empty_subset _
  | _, node P wires, v => by
    induction v using Fin.lastCases with
    | last =>
      simp only [build, Fin.lastCases_last]
      refine wireSupport_appendTerms_acc_subset _ _ _ _ _ ?_ fun t ht => ?_
      · rw [wireSupport_const_last]
        exact Finset.empty_subset _
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
      obtain ⟨hw, hk⟩ := List.mem_filter.mp hw
      obtain ⟨hne, -⟩ := of_decide_eq_true hk
      have hsub : P.testVars w.head ⊆ (P.node wires).testVars (Fin.last _) := by
        intro i hi
        simp only [testVars, List.mem_toFinset, List.mem_flatMap, tests_node_last,
          List.mem_map] at hi ⊢
        obtain ⟨l, hl, hil⟩ := hi
        refine ⟨w.label.toList ++ l, ⟨w, hw, l, hl, rfl⟩, ?_⟩
        obtain ⟨⟨j, b⟩, ha, rfl⟩ := hil
        cases b <;> simp [ha]
      refine ⟨fun i hi => ?_, ?_⟩
      · obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
        simp only [testVars, List.mem_toFinset, List.mem_flatMap, tests_node_last,
          List.mem_map]
        refine ⟨w.label.toList ++ l, ⟨w, hw, l, hl, rfl⟩, ?_⟩
        obtain ⟨_, _ | ⟨j, _⟩⟩ := w <;> simp_all [litVars]
      · simp only [Program.wireSupport_gate_castSucc]
        exact (wireSupport_build_subset P w.head).trans hsub
    | cast v =>
      simp only [build, Fin.lastCases_castSucc, wireSupport_appendTerms_embed,
        Program.wireSupport_gate_castSucc]
      simpa [testVars] using wireSupport_build_subset P v

/-- The program of `P` is syntactically multilinear. -/
theorem isDecomposableAt_build : ∀ {n : ℕ} (P : NBP (Fin N) Bool n),
    (build R P).program.IsDecomposableAt (· = .mul)
  | _, target => by simp [build]
  | _, node P wires => by
    refine isDecomposableAt_appendTerms _ _ _ _ (by simp [isDecomposableAt_build P])
      fun t ht i hi => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    have hk := (of_decide_eq_true (List.mem_filter.mp hw).2).2
    rw [Program.wireSupport_gate_castSucc]
    exact fun h => hk i hi (wireSupport_build_subset P w.head h)

/-- **Values at the Boolean points.** At a node from which no path tests a coordinate twice, the
program of `P` computes the number of paths that the point switches on. -/
theorem trace_build_bitPoint (A : Type*) [CommRing A] [Algebra R A] (x : Fin N → Bool) :
    ∀ {n : ℕ} (P : NBP (Fin N) Bool n) (v : Fin n), P.ReadOnceFrom v →
      (build R P).program.trace (arithInterpretationWith R (algebraMap R A)) (bitPoint x)
        ((build R P).node v) = (P.paths x v : A)
  | _, target, _, _ => by
    change algebraMap R A 1 = ((1 : ℕ) : A)
    simp
  | _, node P wires, v, hv => by
    induction v using Fin.lastCases with
    | last =>
      simp only [build, Fin.lastCases_last]
      rw [trace_appendTerms_acc, paths_node_last, List.sum_map_filter, Nat.cast_list_sum,
        List.map_map, List.map_map]
      have h0 : ((build R P).program.gate ⟨ArithOp.const 0, Fin.elim0⟩).trace
          (arithInterpretationWith R (algebraMap R A)) (bitPoint x)
          (Circuits.Wire.gate (Fin.last _)) = 0 := by
        change ((build R P).program.gate _).eval _ _ (Fin.last _) = 0
        rw [Program.eval_gate_last]
        exact map_zero _
      have hhead (w) (hw : w ∈ wires) : P.ReadOnceFrom w.head := fun l hl => by
        have := hv (w.label.toList ++ l) (by
          rw [tests_node_last]
          exact List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)
        rw [List.map_append] at this
        exact this.of_append_right
      rw [h0, zero_add, List.sum_map_filter]
      congr 1
      refine List.map_congr_left fun w hw => ?_
      simp only [Function.comp_apply, Program.trace_gate_castSucc, litValue_bitPoint]
      by_cases hk : P.Keeps w
      · simp only [hk, decide_true, ite_true, trace_build_bitPoint A x P w.head (hhead w hw)]
        cases w.on x <;> simp [bitVal]
      · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
        rcases not_and_or.mp hk with hne | hvar
        · have hnil : P.tests w.head = [] := not_not.mp hne
          simp [paths_eq_countP, hnil]
        · simp only [not_forall, not_not] at hvar
          obtain ⟨i, hi, hit⟩ := hvar
          exfalso
          simp only [testVars, List.mem_toFinset, List.mem_flatMap] at hit
          obtain ⟨l, hl, hil⟩ := hit
          have hnd := hv (w.label.toList ++ l) (by
            rw [tests_node_last]
            exact List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)
          obtain ⟨_, _ | ⟨j, _⟩⟩ := w <;> simp_all [litVars]
    | cast v =>
      simp only [build, Fin.lastCases_castSucc]
      rw [trace_appendTerms_embed, Program.trace_gate_castSucc, paths_node_castSucc]
      exact trace_build_bitPoint A x P v (by simpa [ReadOnceFrom] using hv)

/-- The arithmetic circuit has at most one gate for each node and five for each wire. -/
theorem size_toArith_le (P : NBP (Fin N) Bool n) : (P.toArith R).size ≤ n + 5 * P.wireCount :=
  size_build_le P

/-- **The arithmetic circuit of a branching program is syntactically multilinear.** -/
theorem isDecomposableAt_toArith (P : NBP (Fin N) Bool n) :
    (P.toArith R).program.IsDecomposableAt (· = .mul) :=
  isDecomposableAt_build P

/-- **The arithmetic circuit counts paths.** For a read-once program, the circuit at a Boolean
point computes, in every `R`-algebra, the number of paths from the source to the target that the
point switches on. -/
theorem eval_toArith_bitPoint (P : NBP (Fin N) Bool n) (hP : P.IsReadOnce) (A : Type*)
    [CommRing A] [Algebra R A] (x : Fin N → Bool) :
    (P.toArith R).eval (arithInterpretationWith R (algebraMap R A)) (bitPoint x) 0 =
      (P.pathCount x : A) := by
  rw [pathCount_eq_paths_source]
  exact trace_build_bitPoint A x P P.source ((isReadOnce_iff_readOnceFrom_source P).mp hP)

/-- **A read-once program computes the multilinear extension of its path count.** The polynomial
computed by the arithmetic circuit of a read-once program is the multilinear extension of the number
of switched-on paths. -/
theorem eval_toArith_X (P : NBP (Fin N) Bool n) (hP : P.IsReadOnce) :
    (P.toArith R).eval (arithInterpretationWith R C) X 0 =
      multilinearExtension fun x => (P.pathCount x : R) := by
  refine ((P.toArith R).program.trace_eq_multilinearExtension (isDecomposableAt_toArith P) id
    ((P.toArith R).outputs 0)).trans ?_
  congr 1
  funext x
  have := P.eval_toArith_bitPoint (R := R) hP R x
  rw [Algebra.algebraMap_self] at this
  exact this

/-- In characteristic two a natural number is its parity. -/
private theorem natCast_eq_bitVal_odd [CharP R 2] (k : ℕ) :
    (k : R) = bitVal R (decide (Odd k)) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [bitVal, ← two_mul, h2]
  · simp [bitVal, h2]

/-- In characteristic two the arithmetic circuit of a read-once parity program computes the
multilinear representative of the function it computes by parity. -/
theorem computesMultilinear_toArith [CharP R 2] (P : NBP (Fin N) Bool n) (hP : P.IsReadOnce) :
    (P.toArith R).ComputesMultilinear fun z => decide (P.AcceptsParity z) := by
  rw [Circuit.ComputesMultilinear, eval_toArith_X P hP]
  congr 1
  funext z
  rw [natCast_eq_bitVal_odd]
  rfl

/-- **Read-once parity programs simulate syntactically multilinear circuits.** In characteristic
two, the function computed by parity by a syntactic read-once parity branching program with `n`
nodes and `w` wires has a syntactically multilinear circuit with at most `n + 5 w` gates computing
its multilinear representative. -/
theorem exists_syntacticallyMultilinear [CharP R 2] (P : NBP (Fin N) Bool n)
    (hP : P.IsReadOnce) :
    ∃ A : Circuit (arithSignature R) N 1, A.IsSyntacticallyMultilinear ∧
      (A.ComputesMultilinear fun z => decide (P.AcceptsParity z)) ∧
      A.size ≤ n + 5 * P.wireCount :=
  ⟨P.toArith R, P.isDecomposableAt_toArith, P.computesMultilinear_toArith hP, P.size_toArith_le⟩

end NBP

end Cslib.BranchingPrograms
