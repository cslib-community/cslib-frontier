/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Program

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

## Main definitions

* `Cslib.Circuits.Program.IsDecomposableAt`: the gates of a given kind are decomposable.

## Main results

* `Cslib.Circuits.Program.isDecomposableAt_gate_iff`: decomposability of a program with one more
  gate.

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
  · generalize hk : (p.gate line).lines k.castSucc = l
    rw [lines_gate_castSucc] at hk
    subst hk
    simp [Line.mapWires]
  · generalize hk : (p.gate line).lines (Fin.last g) = l
    rw [lines_gate_last] at hk
    subst hk
    simp [Line.mapWires]
end Cslib.Circuits
