/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Bipartite
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
public import CslibFrontier.Computability.Complexity.Problems.UGraph
import CslibFrontier.Computability.Complexity.Problems.UGraph.USTCONWriter

/-!
# Bipartiteness is in logarithmic space

The copies of the double cover (`Cslib.Complexity.Bipartite.oddCycleInstance`) are written in
logarithmic space by the shared counter program `Cslib.Complexity.UGraphInstance.ustconWriter`.
An entry within a copy reads the one entry of the input matrix that it depends on; every other
entry is arithmetic in `n` and the two vertex numbers
(`Cslib.Complexity.Bipartite.computableInLogSpace_oddCycleInstance`). The registers hold `n` and
two vertex numbers, at most `2 n² + 2`.

This is a logarithmic-space many-one reduction from non-bipartiteness to undirected connectivity
(`Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON`). With Reingold's theorem
`Cslib.Complexity.USTCON_mem_L` and the closure of `L` under complement, bipartiteness is in `L`
(`Cslib.Complexity.Bipartite.mem_L`) [Goldreich, Exercise 5.16][Goldreich2008]. As for every
problem in `L`, the decider is only required to be correct on encodings of instances. The space
measure is that of `L`: the work-tape cells visited.

Conversely, undirected connectivity reduces to non-bipartiteness
(`Cslib.Complexity.Bipartite.USTCON_logSpaceReducible_compl`). Under logarithmic-space many-one
reductions this is immediate from `USTCON_mem_L`: the reduction decides its input and outputs a
triangle or the graph without vertices, as `Cslib.Complexity.USTCON_logSpaceHard_L` does. The
reduction of Goldreich's guideline, which adds edges to the double cover, is not formalized.
Together, bipartiteness and the complement of undirected connectivity reduce to each other
(`Cslib.Complexity.Bipartite.logSpaceReducible_compl_USTCON`,
`Cslib.Complexity.Bipartite.compl_USTCON_logSpaceReducible`).

## Main results

* `Cslib.Complexity.Bipartite.computableInLogSpace_oddCycleInstance`: the copies of the double
  cover are computed in logarithmic space.
* `Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON`,
  `Cslib.Complexity.Bipartite.USTCON_logSpaceReducible_compl`: non-bipartiteness and undirected
  connectivity reduce to each other.
* `Cslib.Complexity.Bipartite.logSpaceReducible_compl_USTCON`,
  `Cslib.Complexity.Bipartite.compl_USTCON_logSpaceReducible`: the same for bipartiteness and
  undirected non-connectivity.
* `Cslib.Complexity.Bipartite.mem_L`: bipartiteness is in `L`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]
-/

public section

namespace Cslib.Complexity

namespace Bipartite

/-! ### The entries as expressions -/

section Writer

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- The number of vertices, from `n` in register `0`. -/
private def numVerticesExpr : Expr := add (mul (const 2) (mul (reg 0) (reg 0))) (const 2)

/-- The copy of the vertex in a register. -/
private def copyExpr (i : ℕ) : Expr := div (sub (reg i) (const 2)) (mul (const 2) (reg 0))

/-- The vertex of the graph that the vertex in a register stands for. -/
private def vertExpr (i : ℕ) : Expr :=
  div (mod (sub (reg i) (const 2)) (mul (const 2) (reg 0))) (const 2)

/-- The side of the vertex in a register. -/
private def sideExpr (i : ℕ) : Expr := mod (sub (reg i) (const 2)) (const 2)

/-- The row `1` and the column `2` lie in one copy, on different sides. -/
private def withinExpr : Expr :=
  andB (ltB (const 1) (reg 1)) (andB (ltB (const 1) (reg 2))
    (andB (eqB (copyExpr 1) (copyExpr 2)) (notB (eqB (sideExpr 1) (sideExpr 2)))))

/-- The position of the input entry that an entry within a copy reads. -/
private def positionExpr : Expr :=
  add (add (reg 0) (const 1)) (add (mul (vertExpr 1) (reg 0)) (vertExpr 2))

/-- The entries at the source and the target. -/
private def endpointExpr : Expr :=
  orB (andB (ltB (reg 1) (const 2)) (andB (ltB (const 1) (reg 2))
      (andB (eqB (vertExpr 2) (copyExpr 2)) (eqB (sideExpr 2) (reg 1)))))
    (andB (ltB (const 1) (reg 1)) (andB (ltB (reg 2) (const 2))
      (andB (eqB (vertExpr 1) (copyExpr 1)) (eqB (sideExpr 1) (reg 2)))))

variable (G : UGraphInstance)

private theorem eval_numVerticesExpr (r c : ℕ) :
    numVerticesExpr.eval [G.n, r, c] = numVertices G.n := by
  simp [numVerticesExpr, numVertices, Nat.mul_assoc]

private theorem eval_copyExpr_one (r c : ℕ) : (copyExpr 1).eval [G.n, r, c] = copy G.n r := by
  simp [copyExpr, copy]

private theorem eval_copyExpr_two (r c : ℕ) : (copyExpr 2).eval [G.n, r, c] = copy G.n c := by
  simp [copyExpr, copy]

private theorem eval_vertExpr_one (r c : ℕ) : (vertExpr 1).eval [G.n, r, c] = vert G.n r := by
  simp [vertExpr, vert]

private theorem eval_vertExpr_two (r c : ℕ) : (vertExpr 2).eval [G.n, r, c] = vert G.n c := by
  simp [vertExpr, vert]

private theorem eval_sideExpr_one (r c : ℕ) : (sideExpr 1).eval [G.n, r, c] = side r := by
  simp [sideExpr, side]

private theorem eval_sideExpr_two (r c : ℕ) : (sideExpr 2).eval [G.n, r, c] = side c := by
  simp [sideExpr, side]

private theorem eval_withinExpr (r c : ℕ) :
    withinExpr.eval [G.n, r, c] =
      (decide (2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c ∧ side r ≠ side c)).toNat := by
  rw [withinExpr, eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB
    (eval_notB eval_eqB)))]
  simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ, eval_copyExpr_one,
    eval_copyExpr_two, eval_sideExpr_one, eval_sideExpr_two]
  congr 1

private theorem eval_endpointExpr (r c : ℕ) :
    endpointExpr.eval [G.n, r, c] =
      (decide (r < 2 ∧ 2 ≤ c ∧ vert G.n c = copy G.n c ∧ side c = r) ||
        decide (2 ≤ r ∧ c < 2 ∧ vert G.n r = copy G.n r ∧ side r = c)).toNat := by
  rw [endpointExpr, eval_orB (eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB
    eval_eqB))) (eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB eval_eqB)))]
  simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ, eval_copyExpr_one,
    eval_copyExpr_two, eval_vertExpr_one, eval_vertExpr_two, eval_sideExpr_one,
    eval_sideExpr_two]
  congr 1

/-- The entry `(r, c)` of the copies of the double cover, as computed from the expressions: the
input bit at `positionExpr` within a copy, `endpointExpr` otherwise. -/
private theorem entry_eq_exprs (G : UGraphInstance) (r c : Fin (oddCycleInstance G).n) :
    (oddCycleInstance G).adj r c =
      if 0 < withinExpr.eval [G.n, r, c] then G.encode[positionExpr.eval [G.n, r, c]]?.getD false
      else decide (0 < endpointExpr.eval [G.n, r, c]) := by
  rw [eval_withinExpr]
  by_cases hw : 2 ≤ (r : ℕ) ∧ 2 ≤ (c : ℕ) ∧ copy G.n r = copy G.n c ∧ side r ≠ side c
  · obtain ⟨-, hvr, -, -⟩ := eq_copyVertex hw.1 r.isLt
    obtain ⟨-, hvc, -, -⟩ := eq_copyVertex hw.2.1 c.isLt
    have hpos : positionExpr.eval [G.n, r, c] = G.n + 1 + (vert G.n r * G.n + vert G.n c) := by
      simp only [positionExpr, eval_add, eval_mul, eval_reg, eval_const, List.getD_cons_zero,
        eval_vertExpr_one, eval_vertExpr_two]
    simp only [hw, ne_eq, not_false_eq_true, and_self, decide_true, Bool.toNat_true,
      zero_lt_one, ↓reduceIte, hpos, G.getElem?_encode_matrix hvr hvc, Option.getD_some]
    change entry G r c = _
    rw [entry, ite_eq_left hw, UGraphInstance.adjN, dite_eq_left ⟨hvr, hvc⟩]
  · simp only [hw, decide_false, Bool.toNat_false, lt_irrefl, ↓reduceIte, eval_endpointExpr]
    change entry G r c = _
    rw [entry, ite_eq_right hw]
    cases (decide ((r : ℕ) < 2 ∧ 2 ≤ (c : ℕ) ∧ vert G.n c = copy G.n c ∧ side c = r) ||
      decide (2 ≤ (r : ℕ) ∧ (c : ℕ) < 2 ∧ vert G.n r = copy G.n r ∧ side r = c)) <;> simp

/-- **The copies of the double cover are computed in logarithmic space** from the encoded
graph, by `UGraphInstance.ustconWriter`. -/
theorem computableInLogSpace_oddCycleInstance :
    ComputableInLogSpace oddCycleInstance encUGraph encUSTCON :=
  UGraphInstance.computableInLogSpace_of_entryExprs 2 (fun G r c => eval_numVerticesExpr G r c)
    (fun G => by
      simp only [oddCycleInstance, numVertices, G.length_encode]
      nlinarith)
    (fun _ => rfl) (fun _ => rfl) entry_eq_exprs

end Writer

/-! ### Reductions -/

/-- **Non-bipartiteness reduces to undirected connectivity in logarithmic space**, by the copies
of the double cover. -/
theorem compl_logSpaceReducible_USTCON :
    LogSpaceReducible encUGraph encUSTCON Bipartiteᶜ USTCON :=
  ⟨oddCycleInstance, computableInLogSpace_oddCycleInstance,
    fun G => (oddCycleInstance_mem_iff G).symm⟩

/-- **Bipartiteness reduces to undirected non-connectivity in logarithmic space.** -/
theorem logSpaceReducible_compl_USTCON :
    LogSpaceReducible encUGraph encUSTCON Bipartite USTCONᶜ := by
  simpa only [compl_compl] using compl_logSpaceReducible_USTCON.compl

/-- **Bipartiteness is in `L`** [Goldreich, Exercise 5.16][Goldreich2008]: it reduces to the
complement of undirected connectivity, which is in `L` by Reingold's theorem. -/
theorem mem_L : Bipartite ∈ L encUGraph :=
  logSpaceReducible_compl_USTCON.mem_L (compl_mem_L USTCON_mem_L)

/-- The triangle, which is not bipartite. -/
@[expose] def triangle : UGraphInstance where
  n := 3
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp

/-- The graph without vertices, which is bipartite. -/
@[expose] def empty : UGraphInstance where
  n := 0
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl

theorem triangle_notMem : triangle ∉ Bipartite := by
  rw [mem_Bipartite, SimpleGraph.isBipartite_iff_forall_walk_even_length]
  intro h
  have hadj : ∀ a b : Fin 3, a ≠ b → triangle.graph.Adj a b := fun a b hab => by
    simpa [triangle] using hab
  have := h (show Fin triangle.n from (0 : Fin 3)) (.cons (hadj 0 1 (by decide))
    (.cons (hadj 1 2 (by decide)) (.cons (hadj 2 0 (by decide)) .nil)))
  exact Nat.not_even_iff_odd.2 ⟨1, rfl⟩ this

theorem empty_mem : empty ∈ Bipartite :=
  ⟨SimpleGraph.Coloring.mk (fun _ => 0) fun {a} => a.elim0⟩

/-- **Undirected connectivity reduces to non-bipartiteness in logarithmic space.** Under
logarithmic-space many-one reductions this is immediate from Reingold's theorem: the reduction
decides its input and outputs the triangle or the graph without vertices. -/
theorem USTCON_logSpaceReducible_compl :
    LogSpaceReducible encUSTCON encUGraph USTCON Bipartiteᶜ := by
  obtain ⟨f, hf, hA⟩ := USTCON_mem_L
  refine ⟨fun I => if f I then triangle else empty,
    (Turing.MultiTapeTM.ComputableInLogSpace.of_finite (encIn := Turing.MultiTapeTM.encBool)
      (fun b : Bool => if b then triangle else empty)).comp hf, fun I => ?_⟩
  rw [hA I]
  cases h : f I <;> simp [h, empty_mem, triangle_notMem]

/-- **Undirected non-connectivity reduces to bipartiteness in logarithmic space.** -/
theorem compl_USTCON_logSpaceReducible :
    LogSpaceReducible encUSTCON encUGraph USTCONᶜ Bipartite := by
  simpa only [compl_compl] using USTCON_logSpaceReducible_compl.compl

end Bipartite

end Cslib.Complexity
