/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Simulation

/-!
# Decomposable gates

The gates of a chosen kind in a straight-line program are *decomposable* when distinct arguments of
each of them are reached by disjoint sets of inputs (`Cslib.Circuits.Program.wireSupport`). This
is a syntactic condition on the program. For the AND gates of a Boolean circuit it is the
decomposability of d-DNNFs and of deterministic decomposable circuits
[Monet and Olteanu, Definition 3][MonetOlteanu2018], and for the multiplications of an arithmetic
circuit it is syntactic multilinearity.

The condition is stated gate by gate on the lines of the program (`Cslib.Circuits.Program.lines`),
so it is decidable, and it splits along the last gate
(`Cslib.Circuits.Program.isDecomposableAt_gate_iff`).

When a program `q` reads its inputs from wires with given supports `S`, as it does after being
appended to another program (`Cslib.Circuits.Program.append`), its decomposability is measured on
those supports (`Cslib.Circuits.Program.DecomposesOver`): the support of a wire of `q` is the
union of the supports `S i` of the inputs `i` reaching it
(`Cslib.Circuits.Program.wireSupport_append_appendedWire`). Replacing every gate by a circuit
(`Cslib.Circuits.Program.simulateProgram`) keeps the input supports of the original wires
(`Cslib.Circuits.Program.wireSupport_simulateRenaming`) and so keeps a program decomposable when
each replacement circuit decomposes over the supports of the arguments it is given
(`Cslib.Circuits.Program.isDecomposableAt_simulateProgram`).

## Main definitions

* `Cslib.Circuits.Program.IsDecomposableAt`: the gates of a given kind are decomposable.
* `Cslib.Circuits.Program.DecomposesOver`: the gates of a given kind are decomposable when the
  inputs have given supports.

## Main results

* `Cslib.Circuits.Program.isDecomposableAt_gate_iff`: decomposability of a program with one more
  gate.
* `Cslib.Circuits.Program.isDecomposableAt_append_iff`: decomposability of a continued program.
* `Cslib.Circuits.Program.isDecomposableAt_simulateProgram`: replacing gates by decomposable
  circuits keeps a program decomposable.

## References

* [M. Monet and D. Olteanu, *Towards Deterministic Decomposable Circuits for Safe
  Queries*][MonetOlteanu2018]
-/

public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- The gates of `p` whose operation satisfies `product` are *decomposable*: distinct arguments of
each of them are reached by disjoint sets of inputs (`Program.wireSupport`). For Boolean AND gates
this is the decomposability of d-DNNFs and d-Ds, and for multiplications of arithmetic circuits it
is syntactic multilinearity. -/
def Program.IsDecomposableAt (p : Program σ n g) (product : σ.Op → Prop) : Prop :=
  ∀ k, product (p.lines k).op →
    Pairwise fun a b => Disjoint (p.wireSupport ((p.lines k).wires a))
      (p.wireSupport ((p.lines k).wires b))

instance (p : Program σ n g) (product : σ.Op → Prop) [DecidablePred product] :
    Decidable (p.IsDecomposableAt product) :=
  inferInstanceAs (Decidable (∀ k, product (p.lines k).op → ∀ a b, a ≠ b →
    Disjoint (p.wireSupport ((p.lines k).wires a)) (p.wireSupport ((p.lines k).wires b))))

/-- The empty program is decomposable. -/
@[simp] theorem Program.isDecomposableAt_empty (product : σ.Op → Prop) :
    (Program.empty : Program σ n 0).IsDecomposableAt product :=
  fun k => k.elim0


/-! ### Programs reading inputs with given supports -/

section Over

variable {k m : ℕ}

/-- The gates of `q` whose operation satisfies `product` are decomposable when each input `i` of
`q` has the support `S i`: distinct arguments of each of them are reached by disjoint unions of
input supports. With singleton supports this is `Program.IsDecomposableAt`. -/
def Program.DecomposesOver (q : Program σ k g) (product : σ.Op → Prop)
    (S : Fin k → Finset (Fin n)) : Prop :=
  ∀ j, product (q.lines j).op →
    Pairwise fun a b => Disjoint ((q.wireSupport ((q.lines j).wires a)).biUnion S)
      ((q.wireSupport ((q.lines j).wires b)).biUnion S)

/-- The empty program decomposes over any supports. -/
@[simp] theorem Program.decomposesOver_empty (product : σ.Op → Prop)
    (S : Fin k → Finset (Fin n)) : (Program.empty : Program σ k 0).DecomposesOver product S :=
  fun j => j.elim0

/-- A program with one more gate decomposes over `S` when the earlier gates do and, if the new gate
is of the given kind, its distinct arguments are reached by disjoint unions of input supports. -/
@[simp] theorem Program.decomposesOver_gate_iff (q : Program σ k g) (line : Line σ k g)
    (product : σ.Op → Prop) (S : Fin k → Finset (Fin n)) :
    (q.gate line).DecomposesOver product S ↔ q.DecomposesOver product S ∧
      (product line.op → Pairwise fun a b =>
        Disjoint ((q.wireSupport (line.wires a)).biUnion S)
          ((q.wireSupport (line.wires b)).biUnion S)) := by
  unfold DecomposesOver
  rw [Fin.forall_fin_succ']
  refine and_congr (forall_congr' fun j => ?_) ?_
  · generalize hj : (q.gate line).lines j.castSucc = l
    rw [lines_gate_castSucc] at hj
    subst hj
    simp [Line.mapWires]
  · generalize hj : (q.gate line).lines (Fin.last g) = l
    rw [lines_gate_last] at hj
    subst hj
    simp [Line.mapWires]

/-- Decomposability is decomposability over the singleton supports `{i}` of the inputs. -/
theorem Program.isDecomposableAt_iff_decomposesOver (p : Program σ n g)
    (product : σ.Op → Prop) :
    p.IsDecomposableAt product ↔ p.DecomposesOver product fun i => {i} := by
  simp [IsDecomposableAt, DecomposesOver]

/-- A program with one more gate is decomposable when the earlier gates are and, if the new gate
is of the given kind, its distinct arguments are reached by disjoint sets of inputs. -/
@[simp] theorem Program.isDecomposableAt_gate_iff (p : Program σ n g) (line : Line σ n g)
    (product : σ.Op → Prop) :
    (p.gate line).IsDecomposableAt product ↔ p.IsDecomposableAt product ∧
      (product line.op → Pairwise fun a b =>
        Disjoint (p.wireSupport (line.wires a)) (p.wireSupport (line.wires b))) := by
  unfold IsDecomposableAt
  rw [Fin.forall_fin_succ']
  refine and_congr (forall_congr' fun k => ?_) ?_
  · rw [lines_gate_castSucc]
    simp [Line.mapWires]
  · rw [lines_gate_last]
    simp [Line.mapWires]

/-- The support interpretation of a program run on any input supports `S` unions the supports of
the inputs reaching each wire. -/
theorem Program.trace_supportInterpretation (q : Program σ k g) (S : Fin k → Finset (Fin n))
    (w : Wire k g) : q.trace (supportInterpretation σ n) S w = (q.wireSupport w).biUnion S := by
  let h : Homomorphism (supportInterpretation σ k) (supportInterpretation σ n) :=
    ⟨fun A => A.biUnion S, fun op args => by
      ext i
      simp only [supportInterpretation, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Function.comp_apply]
      exact ⟨fun ⟨a, ⟨b, hb⟩, hi⟩ => ⟨b, a, hb, hi⟩, fun ⟨b, a, hb, hi⟩ => ⟨a, ⟨b, hb⟩, hi⟩⟩⟩
  have := congrFun (q.map_trace h fun i => {i}) w
  simpa [h, Function.comp_def, Program.wireSupport] using this.symm

/-- The wires of `p` keep their supports after `p` is continued. -/
@[simp] theorem Program.wireSupport_append_castAdd (p : Program σ n g) (feed : Fin k → Wire n g)
    (q : Program σ k m) (w : Wire n g) :
    (p.append feed q).wireSupport (w.castAdd m) = p.wireSupport w :=
  trace_append_castAdd p feed _ _ q w

/-- A wire of `q`, continuing `p`, is reached by the inputs reaching the wires of `p` that feed the
inputs of `q` reaching it. -/
theorem Program.wireSupport_append_appendedWire (p : Program σ n g) (feed : Fin k → Wire n g)
    (q : Program σ k m) (w : Wire k m) :
    (p.append feed q).wireSupport (appendedWire feed w) =
      (q.wireSupport w).biUnion fun i => p.wireSupport (feed i) :=
  (trace_append_appendedWire p feed _ _ q w).trans (q.trace_supportInterpretation _ w)

/-- **Decomposability of a continued program.** Continuing `p` by `q` gives a decomposable program
exactly when `p` is decomposable and `q` decomposes over the supports of the wires feeding it. -/
theorem Program.isDecomposableAt_append_iff (p : Program σ n g) (feed : Fin k → Wire n g)
    (q : Program σ k m) (product : σ.Op → Prop) :
    (p.append feed q).IsDecomposableAt product ↔
      p.IsDecomposableAt product ∧ q.DecomposesOver product fun i => p.wireSupport (feed i) := by
  induction q with
  | empty => simp [append]
  | gate q line ih =>
    rw [append, isDecomposableAt_gate_iff, ih, decomposesOver_gate_iff, and_assoc]
    simp [Line.mapWires, wireSupport_append_appendedWire]

end Over

/-! ### Simulation -/

section Simulation

universe w

variable {τ : Signature.{w}}

/-- Replacing every gate by a circuit that, as a function of input supports, unions the supports of
all its arguments keeps the support of every original wire. -/
theorem Program.wireSupport_simulateRenaming (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (h : ∀ op, (impl op).Computes (supportInterpretation τ n)
      (single (supportInterpretation σ n op))) (w : Wire n g) :
    (p.simulateProgram impl).wireSupport (p.simulateRenaming impl w) = p.wireSupport w :=
  congrFun (p.trace_simulate impl h fun i => {i}) w

/-- **Simulation keeps programs decomposable.** Replace every gate of a program decomposable at
`product` by a circuit that unions the supports of all its arguments. If each replacement circuit
decomposes at `product'` over any supports of its arguments, pairwise disjoint when the replaced
gate is of kind `product`, then the simulated program is decomposable at `product'`. -/
theorem Program.isDecomposableAt_simulateProgram (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) {product : σ.Op → Prop}
    {product' : τ.Op → Prop}
    (hsupport : ∀ op, (impl op).Computes (supportInterpretation τ n)
      (single (supportInterpretation σ n op)))
    (himpl : ∀ op (S : Fin (σ.Arity op) → Finset (Fin n)),
      (product op → Pairwise fun a b => Disjoint (S a) (S b)) →
        (impl op).program.DecomposesOver product' S)
    (hp : p.IsDecomposableAt product) : (p.simulateProgram impl).IsDecomposableAt product' := by
  induction p with
  | empty => exact isDecomposableAt_empty product'
  | gate q line ih =>
    rw [isDecomposableAt_gate_iff] at hp
    change ((q.simulateProgram impl).append _ (impl line.op).program).IsDecomposableAt product'
    rw [isDecomposableAt_append_iff]
    refine ⟨ih hp.1, himpl line.op _ fun hop a b hab => ?_⟩
    simp only [Function.comp_apply, wireSupport_simulateRenaming q impl hsupport]
    exact hp.2 hop hab

end Simulation

end Cslib.Circuits
