/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.PCP.Encoded.Witness
import CslibFrontier.Computability.Complexity.Problems.SAT.Relation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.FinEnum

/-!
# Tests for constructive PCP witness compilation

Executable checks on the constructive Dinur witness-compilation pipeline (`ofCompactCNFLabels`,
`powerPreprocessLabels`, and `proofOfLabelList`) together with non-vacuous instantiations of
`exists_pcpVerifier_of_npRelation` on a concrete binary `NPRelation` and on `SAT.npRelation`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.PCPWitness

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- Concrete two-clause SAT formula `([[ (0, true), (1, false) ], [ (1, true) ]])`. -/
def sampleCNF : CNF ℕ := [[(0, true), (1, false)], [(1, true)]]

example : sampleCNF.eval (fun _ => true) = true := by decide

-- Executable graph-labelling checks on `Graph.ofCompactCNF sampleCNF.to3CNF`: a satisfying raw
-- certificate yields a labelling that passes every edge check, while all-`false` fails an edge.
example : (ofCompactCNFLabels sampleCNF [true, true, true]).length =
    (Graph.ofCompactCNF sampleCNF.to3CNF).vertices := by
  decide

example :
    (Graph.ofCompactCNF sampleCNF.to3CNF).edges.all (fun edge =>
      edge.constraint
        ((ofCompactCNFLabels sampleCNF [true, true, true]).getD edge.src (fun _ => false))
        ((ofCompactCNFLabels sampleCNF [true, true, true]).getD edge.dst (fun _ => false))) =
      true := by
  decide

example :
    (Graph.ofCompactCNF sampleCNF.to3CNF).edges.all (fun edge =>
      edge.constraint
        ((ofCompactCNFLabels sampleCNF [false, false, false]).getD edge.src (fun _ => false))
        ((ofCompactCNFLabels sampleCNF [false, false, false]).getD edge.dst (fun _ => false))) =
      false := by
  decide

-- Mathematical satisfaction for `SAT.npRelation.IsWitness` via `SAT.isWitness_padCertificate`.
theorem sampleCNF_sat_witness :
    SAT.npRelation.IsWitness sampleCNF
      (SAT.padCertificate sampleCNF (sampleCNF.vars.map fun _ => true)) :=
  SAT.isWitness_padCertificate (by decide : sampleCNF.eval (fun _ => true) = true)

example (e : Fin (Graph.ofCompactCNF sampleCNF.to3CNF).edges.length) :
    ((Graph.ofCompactCNF sampleCNF.to3CNF).toGraph id).Satisfies
      (fun v =>
        (ofCompactCNFLabels sampleCNF
          (SAT.padCertificate sampleCNF (sampleCNF.vars.map fun _ => true))).getD v
            (fun _ => false))
      e :=
  satisfies_ofCompactCNFLabels sampleCNF_sat_witness e

-- Executable check of `powerPreprocessLabels` on a one-vertex equality self-loop graph using the
-- trivial `Fin 1` rotation map.
def trivFamily (n : ℕ) : RotationMap (Fin n) (Fin 1) where
  rot := id
  rot_involutive _ := rfl

def trivRotate (p : ℕ × ℕ × Fin 1) : ℕ × Fin 1 :=
  (p.2.1, p.2.2)

theorem trivRotate_eq (n : ℕ) (v : Fin n) (d : Fin 1) :
    trivRotate (n, v.val, d) =
      (((trivFamily n).rot (v, d)).1.val, ((trivFamily n).rot (v, d)).2) :=
  rfl

def boolEqGraph : Graph (Bool → Bool → Bool) where
  vertices := 1
  edges := [{ src := 0, dst := 0, constraint := (· == ·) }]

example :
    (Graph.powerPreprocessLabels (C := Bool → Bool → Bool) (α := Bool) (D := Fin 1)
      (· == ·) false trivRotate 1 boolEqGraph [true]).length = 2 := by
  decide

example (e : Fin (boolEqGraph.powerPreprocess id (· == ·) trivRotate 1 2
      (FinEnum.toList (Graph.PowerLabel (Fin 1) 1 2))).edges.length) :
    ((boolEqGraph.powerPreprocess id (· == ·) trivRotate 1 2
        (FinEnum.toList (Graph.PowerLabel (Fin 1) 1 2))).toGraph id).Satisfies
      (fun v =>
        (Graph.powerPreprocessLabels (· == ·) false trivRotate 1 boolEqGraph [true]).getD v
          (fun _ => false))
      e :=
  Graph.satisfies_powerPreprocessLabels boolEqGraph id (· == ·) trivFamily trivRotate
    trivRotate_eq 1 2 (FinEnum.toList (Graph.PowerLabel (Fin 1) 1 2))
    FinEnum.nodup_toList FinEnum.mem_toList false
    (fun e => by
      rcases e with ⟨i, hi⟩
      simp [boolEqGraph] at hi
      subst i
      simp [boolEqGraph, Graph.toGraph, ConstraintGraph.Satisfies])
    (fun _ => false) e

-- Exact equality check for `proofOfLabelList` on concrete `Fin 3 → Bool` labels.
def encFin3 (f : Fin 3 → Bool) (i : Fin 3) : Bool := f i

example :
    let labels : List (Fin 3 → Bool) := [fun _ => true, fun i => decide (i.val = 1)]
    Graph.proofOfLabelList encFin3 labels =
      Graph.proofOfLabels 3 labels.length encFin3 (fun v => labels.getD v (fun _ => false)) :=
  Graph.proofOfLabelList_eq_proofOfLabels encFin3 (fun _ => false)
    [fun _ => true, fun i => decide (i.val = 1)]

example :
    let labels : List (Fin 3 → Bool) := [fun _ => true, fun i => decide (i.val = 1)]
    Graph.proofOfLabelList encFin3 labels = [true, true, true, false, true, false] := by
  decide

-- Non-vacuous `NPRelation` client for `exists_pcpVerifier_of_npRelation`: strings starting with
-- `true`, with one-bit certificate equal to `[true]`.
noncomputable def headTrueRel : NPRelation encBits where
  certLength := 1
  verifier := fun (x, w) => x.headD false && w.headD false
  computableInPolyTime_verifier := by fun_prop

theorem headTrueRel_witness : headTrueRel.IsWitness [true] [true] := by
  simp [headTrueRel, NPRelation.IsWitness]

theorem headTrueRel_not_mem_false : [false] ∉ headTrueRel.language := by
  rintro ⟨w, _, hver⟩
  simp [headTrueRel] at hver

example :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool),
      V.PolyTime encBits ∧
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      V.tableVerifier ([true], compile ([true], [true])) = true ∧
      (∀ table, V.tableVerifier ([false], table) = false) := by
  obtain ⟨V, compile, _, _, hV, hpcp, hcompile, hacc⟩ :=
    exists_pcpVerifier_of_npRelation encBits headTrueRel
  refine ⟨V, compile, hV, hcompile, hacc [true] [true] headTrueRel_witness, fun table => ?_⟩
  by_contra htrue
  have hmem : [false] ∈ headTrueRel.language :=
    (hpcp.mem_iff_exists_tableVerifier [false]).mpr ⟨table, by simpa using htrue⟩
  exact headTrueRel_not_mem_false hmem

example :
    ∃ (V : PCPVerifier (CNF ℕ)) (compile : CNF ℕ × List Bool → List Bool),
      V.PolyTime encCNF ∧
      ComputableInPolyTime compile (encPair encCNF encBits) encBits ∧
      V.tableVerifier
        (sampleCNF,
          compile (sampleCNF, SAT.padCertificate sampleCNF (sampleCNF.vars.map fun _ => true))) =
        true := by
  obtain ⟨V, compile, _, _, hV, _, hcompile, hacc⟩ :=
    exists_pcpVerifier_of_npRelation encCNF SAT.npRelation
  exact ⟨V, compile, hV, hcompile, hacc sampleCNF _ sampleCNF_sat_witness⟩

end CslibFrontierTests.PCPWitness
