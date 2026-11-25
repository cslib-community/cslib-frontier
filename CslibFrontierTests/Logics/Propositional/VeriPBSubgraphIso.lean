/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! Subgraph isomorphism under the ordinary imports of its API: the simple graph of a LAD graph,
the variables and constraints of the encoding, evaluated by the kernel (`decide`), the correctness
theorems on an assignment checked by the kernel, CakePB's variable names and their cover of the
encoding, and the end-to-end theorems in the shapes a client uses them. The LAD reader and the
checkers have no exposed bodies; `CslibFrontierTests.Logics.Propositional.VeriPBSubgraphIsoDecide`
evaluates them in the kernel, with proofs checked against LAD texts and Mathlib's graphs. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBSubgraphIso

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph

/-! ### LAD graphs -/

/-- The path `0 - 1 - 2` as neighbour lists, as `parseLAD "3\n1 1\n2 0 2\n1 1\n"` reads it. -/
abbrev p3 : LADGraph := ⟨3, [[1], [0, 2], [1]]⟩

example : p3.graph.Adj 0 1 ∧ p3.graph.Adj 2 1 ∧ ¬ p3.graph.Adj 0 2 := by decide

-- Lists that are not symmetric give the symmetric closure; the reader rejects them, and for a
-- graph it reads the adjacency is exactly the lists.
example : (⟨2, [[1]]⟩ : LADGraph).graph.Adj 1 0 := by decide
example {s : String} {g : LADGraph} (h : parseLAD s = some g) (u v : Fin g.n)
    (huv : g.graph.Adj u v) : v ∈ g.nbrs.getD u.val [] :=
  (adj_iff_of_parseLAD h u v).1 huv

-- `p3` has the same simple graph as Mathlib's path.
example : p3.graph = SimpleGraph.pathGraph 3 := by
  ext u v
  revert u v
  decide

/-! ### The encoding -/

-- The pattern vertex `a` mapped to the target vertex `u` among `3` is the variable `3a + u`.
example : isoVar 3 (1 : Fin 2) (2 : Fin 3) = 5 := rfl

-- `2 + 2` mapping constraints, `3` injectivity constraints and `3 · 2` edge constraints for the
-- two directions of the edge of `K₂` and the three target vertices.
example : (isoConstraints (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph 3)).length = 13 := by
  decide

/-- The assignment of the copy `0 ↦ 0`, `1 ↦ 1` of `K₂` in the path: `x₀₀` and `x₁₁`. -/
def copyAsg (i : ℕ) : Bool := i == isoVar 3 (0 : Fin 2) (0 : Fin 3) || i == isoVar 3 (1 : Fin 2) 1

theorem copyAsg_holds :
    ∀ c ∈ isoConstraints (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph 3), c.Holds copyAsg := by
  decide

/-- **A copy from a solution**: the assignment solves the encoding, so it is the graph of a copy
of `K₂` in the path, which sends `0` to `0`. -/
example : ∃ f : (⊤ : SimpleGraph (Fin 2)).Copy (SimpleGraph.pathGraph 3), f 0 = 0 := by
  obtain ⟨f, hf⟩ := (forall_holds_isoConstraints_iff _ _ copyAsg).1 copyAsg_holds
  exact ⟨f, by simpa [copyAsg, isoVar] using (hf 0 0).symm⟩

example : (⊤ : SimpleGraph (Fin 2)).IsContained (SimpleGraph.pathGraph 3) :=
  (exists_holds_isoConstraints_iff _ _).1 ⟨copyAsg, copyAsg_holds⟩

-- Conversely, no assignment solves the encoding of the triangle into `K₂`.
example : ¬ ∃ σ : ℕ → Bool,
    ∀ c ∈ isoConstraints (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 2)), c.Holds σ := by
  rw [exists_holds_isoConstraints_iff]
  rintro ⟨f⟩
  simpa using Fintype.card_le_of_injective f f.injective

/-! ### CakePB's names -/

-- The pattern vertex `1` mapped to the target vertex `2` is named `x1_2`, as by `cake_pb_iso`.
example : isoName 1 2 = "x1_2" := by decide

example : (isoNames 2 3).name (isoVar 3 (1 : Fin 2) (2 : Fin 3)) = "x1_2" := by
  rw [name_isoNames_isoVar]
  decide

open Text in
/-- **A copy from the solution of a `SAT` proof**: the names cover the encoding, so the solution
logged by an accepted proof solves it, and its literal `xa_u` tells whether the copy sends the
pattern vertex `a` to the target vertex `u`. -/
example {p t : ℕ} (P : SimpleGraph (Fin p)) [DecidableRel P.Adj] (T : SimpleGraph (Fin t))
    [DecidableRel T.Adj] {pbp : String} {ρ : List (Literal ℕ)}
    (h : (checkOPBOutput (printOPB ⟨isoConstraints P T, none, none⟩ (isoNames p t)) pbp).map
      (·.1) = some (Conclusion.sat (some ρ))) :
    ∃ f : P.Copy T, ∀ (a : Fin p) (u : Fin t), (ρ.map fun l =>
      ((proofNames (printOPB ⟨isoConstraints P T, none, none⟩ (isoNames p t)) pbp).name l.1,
        l.2)).contains (isoName a u, true) = decide (f a = u) := by
  obtain ⟨f, hf⟩ := (forall_holds_isoConstraints_iff P T _).1
    (holds_of_checkOPB_printOPB_sat (isoNames_covers P T) h)
  refine ⟨f, fun a u => ?_⟩
  have := hf a u
  simp only [name_isoNames_isoVar] at this
  exact this

/-! ### End to end -/

-- `UNSAT` for LAD texts: both parse, and the pattern read has no copy in the target read.
example {pattern target pbp : String} (h : checkSubgraphIso pattern target pbp = some false) :
    ∃ gp gt, parseLAD pattern = some gp ∧ parseLAD target = some gt ∧
      ¬ gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, hb⟩ := isContained_iff_of_checkSubgraphIso h
  exact ⟨gp, gt, hp, ht, fun hc => Bool.false_ne_true (hb.1 hc)⟩

-- `SAT` for graphs built in Lean.
example {pbp : String} (h : checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 2))
    (SimpleGraph.pathGraph 4) pbp = some true) :
    (⊤ : SimpleGraph (Fin 2)).IsContained (SimpleGraph.pathGraph 4) :=
  (isContained_iff_of_checkSubgraphIsoGraph h).2 rfl

-- No proof can certify `SAT` for the triangle in `K₂`.
example (pbp : String) :
    checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 2)) pbp ≠ some true :=
  fun h => by
    obtain ⟨f⟩ := (isContained_iff_of_checkSubgraphIsoGraph h).2 rfl
    simpa using Fintype.card_le_of_injective f f.injective

end CslibFrontierTests.Logics.Propositional.VeriPBSubgraphIso
