/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.DecomposableGates
public import Mathlib.Data.Fintype.Pi

/-!
# Deterministic decomposable circuits

A *deterministic decomposable circuit* (d-D) is a Boolean circuit with constants, inputs, and
AND, OR and NOT gates in which every AND is *decomposable*, its arguments reading disjoint sets of
inputs, and every OR is *deterministic*, at most one of its arguments being true on any input
[Monet and Olteanu, Definition 3][MonetOlteanu2018]. NOT gates may occur anywhere, not only at the
inputs as in a d-DNNF. Both conditions are pairwise over the arguments of a gate. Decomposability is
a syntactic condition on the inputs that can reach each argument
(`Cslib.Circuits.Program.IsDecomposableAt`); determinism is a semantic condition on the values.

Here the circuits are those of the De Morgan basis (`Cslib.Circuits.Boolean.signature`), with binary
AND and OR and also Boolean constants, and size counts gates (`Cslib.Circuits.Circuit.size`). An
unbounded fan-in AND or OR with `k` arguments is a binary tree of `k - 1` gates of the same kind,
which is decomposable or deterministic when the original gate is, so a d-D with unbounded fan-in and
`s` wires gives a binary one with at most `s` AND and OR gates, besides its NOT gates and constants.

**Positions, not predecessors.** Definition 3 compares the distinct predecessor gates of an AND or
OR. Here the conditions compare argument positions, and two positions of a gate can read the same
earlier line. Such a gate can fail the conditions even with one distinct predecessor: `x ∨ x` is not
deterministic at `x = true`, and `x ∧ x` is not decomposable, both arguments reading `{x}`. So the
definitions agree with Definition 3 for circuits whose ANDs and ORs have distinct predecessors,
which removing repeated arguments achieves (`x ∧ x` and `x ∨ x` are `x`). The positional form is the
one the arithmetic simulation of #8623 uses, where an AND becomes a product of its arguments.

The conditions are stated gate by gate on the lines of the program (`Cslib.Circuits.Program.lines`),
so they are decidable, and they split along the last gate
(`Cslib.Circuits.Program.isDecomposableAt_gate_iff`,
`Cslib.Circuits.Program.isDeterministic_gate_iff`).

## Main definitions

* `Cslib.Circuits.Program.IsDeterministic`: every OR of a De Morgan program is deterministic.
* `Cslib.Circuits.Circuit.IsDeterministicDecomposable`: a d-D, a De Morgan circuit whose ANDs are
  decomposable (`Cslib.Circuits.Program.IsDecomposableAt`) and whose ORs are deterministic.

## Main results

* `Cslib.Circuits.Program.isDeterministic_gate_iff`: determinism of a program with one more gate.

## References

* [M. Monet and D. Olteanu, *Towards Deterministic Decomposable Circuits for Safe
  Queries*][MonetOlteanu2018]
-/

public section

namespace Cslib.Circuits

variable {n g m : ℕ}

/-- Every OR of a De Morgan program is *deterministic*: no input makes two distinct arguments of it
true [Monet and Olteanu, Definition 3][MonetOlteanu2018]. -/
def Program.IsDeterministic (p : Program Boolean.signature n g) : Prop :=
  ∀ k, (p.lines k).op = .or → ∀ x : Fin n → Bool, Pairwise fun a b =>
    ¬(p.trace Boolean.interpretation x ((p.lines k).wires a) = true ∧
      p.trace Boolean.interpretation x ((p.lines k).wires b) = true)

instance (p : Program Boolean.signature n g) : Decidable p.IsDeterministic :=
  inferInstanceAs (Decidable (∀ k, (p.lines k).op = .or → ∀ x : Fin n → Bool, ∀ a b, a ≠ b →
    ¬(p.trace Boolean.interpretation x ((p.lines k).wires a) = true ∧
      p.trace Boolean.interpretation x ((p.lines k).wires b) = true)))

/-- The empty program is deterministic. -/
@[simp] theorem Program.isDeterministic_empty :
    (Program.empty : Program Boolean.signature n 0).IsDeterministic :=
  fun k => k.elim0

/-- A program with one more gate is deterministic when the earlier gates are and, if the new gate
is an OR, no input makes two distinct arguments of it true. -/
@[simp] theorem Program.isDeterministic_gate_iff (p : Program Boolean.signature n g)
    (line : Line Boolean.signature n g) :
    (p.gate line).IsDeterministic ↔ p.IsDeterministic ∧
      (line.op = .or → ∀ x : Fin n → Bool, Pairwise fun a b =>
        ¬(p.trace Boolean.interpretation x (line.wires a) = true ∧
          p.trace Boolean.interpretation x (line.wires b) = true)) := by
  unfold IsDeterministic
  rw [Fin.forall_fin_succ']
  refine and_congr (forall_congr' fun k => ?_) ?_
  · generalize hk : (p.gate line).lines k.castSucc = l
    rw [lines_gate_castSucc] at hk
    subst hk
    simp [Line.mapWires]
  · generalize hk : (p.gate line).lines (Fin.last g) = l
    rw [lines_gate_last] at hk
    subst hk
    simp [Line.mapWires]

/-- A *deterministic decomposable circuit* (d-D): a De Morgan circuit whose ANDs are decomposable
and whose ORs are deterministic, with NOT gates anywhere
[Monet and Olteanu, Definition 3][MonetOlteanu2018]. -/
structure Circuit.IsDeterministicDecomposable (c : Circuit Boolean.signature n m) : Prop where
  /-- Every AND is decomposable: its arguments are reached by disjoint sets of inputs. -/
  decomposable : c.program.IsDecomposableAt (· = .and)
  /-- Every OR is deterministic. -/
  deterministic : c.program.IsDeterministic

instance (c : Circuit Boolean.signature n m) : Decidable c.IsDeterministicDecomposable :=
  decidable_of_iff (c.program.IsDecomposableAt (· = .and) ∧ c.program.IsDeterministic)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.decomposable, h.deterministic⟩⟩

end Cslib.Circuits
