/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Data.BitString.BitVec
import CslibFrontier.Foundations.Data.BitString.ZModSpace
import CslibFrontier.Foundations.Data.BitString.LinearEquiv
import CslibFrontier.Foundations.Data.Code.ParityCheck
import CslibFrontier.Foundations.BooleanAnalysis.QuadraticForm
import CslibFrontier.Foundations.Combinatorics.Multigraph.CutSpace
import CslibFrontier.Foundations.Combinatorics.Multidigraph.Arborescence
import CslibFrontier.Foundations.Combinatorics.Multidigraph.Connectivity
import CslibFrontier.Foundations.Combinatorics.Digraph.Connectivity

/-!
# Tests for `BitString` representations, linear algebra, multigraph cut spaces, and multidigraphs

Exercises:
1. `Cslib.BitString.ZModSpace` (`toZModSpace`, `submoduleZModIso`, `finrank_submoduleZModIso`,
   `exists_isCompl_bool`, `orthogonal`, `finrank_orthogonal_add_finrank_bool`,
   `orthogonal_orthogonal_bool`), binary parity-check codes
   (`Code.submoduleZModIso_parityCheckCode`, `Code.orthogonal_parityCheckCode_bool`), and
   `BitString.quadForm_eq_bitEquiv`.
2. `Cslib.BitString.LinearEquiv` (`congrLinearEquiv`, `appendLinearEquiv`, `piBlocksLinearEquiv`).
3. `Cslib.Multigraph.CutSpace` (`incidenceMatrix_eq_endpointIncidence`,
   `cutSpace_eq_span_incidence`, `mem_cutSpace_iff_exists_edgeCut`, `finrank_cutSpace_add_one`,
   `orthogonal_cutSpace`, `finrank_ker_incidenceMatrix_add_card`) on a concrete connected
   multigraph with parallel edges and a self-loop.
4. `Cslib.Multidigraph` ↔ `Digraph` bridges (`toDigraph_arcSrc_arcTgt`, `arcMatrix_arcSrc_arcTgt`,
   `arborescenceEquivSubdigraph`, `isDipath_pmap_zip_tail`).
5. `Cslib.BitString.BitVec` (`equivBitVec`, `getLsbD_equivBitVec`, `getElem_equivBitVec`,
   `equivBitVec_symm_apply`, `equivBitVec_getLsbD`, `toNat_equivBitVec_eq_equivFin`,
   `equivBitVec_zero`, `equivBitVec_symm_zero`, `equivBitVec_compl`), bitwise `BooleanRing`
   correspondence, and separation between `BooleanRing` `+` (XOR) and modular `BitVec` `+` at
   `w = 2`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BitStringZModCutSpace

open Cslib Cslib.BitString Finset Matrix Module

/-! ### 1. `ZModSpace`: subspaces, complements, and dual orthogonal dimension over `Bool` -/

/-- A `2 × 4` Boolean parity-check matrix with independent rows `[1, 1, 0, 0]` and
`[0, 1, 1, 1]`. -/
private def checkMat4 : Matrix (Fin 2) (Fin 4) Bool :=
  !![true, true, false, false; false, true, true, true]

private abbrev code4 : Submodule Bool (BitString 4) :=
  Code.parityCheckCode checkMat4

private theorem submoduleZModIso_code4 :
    submoduleZModIso (Fin 4) code4 = Code.parityCheckCode (checkMat4.map bitEquiv.symm) ∧
      orthogonal code4 = LinearMap.range checkMat4.transpose.mulVecLin :=
  ⟨Code.submoduleZModIso_parityCheckCode checkMat4,
    Code.orthogonal_parityCheckCode_bool checkMat4⟩

/-- `code4` has exact `Bool`-dimension `2`, cardinality `4`, and `2`-dimensional orthogonal dual
`orthogonal code4`, with `orthogonal (orthogonal code4) = code4`. -/
private theorem finrank_and_dual_code4 :
    finrank Bool code4 = 2 ∧
      Nat.card code4 = 4 ∧
      finrank Bool (orthogonal code4) = 2 ∧
      orthogonal (orthogonal code4) = code4 := by
  have hcard : Nat.card code4 = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hpow := natCard_submodule_bool code4
  rw [hcard] at hpow
  have hdim : finrank Bool code4 = 2 := by
    have hle : finrank Bool code4 ≤ 4 := by
      rw [← finrank_submoduleZModIso]
      exact (Submodule.finrank_le _).trans (by simp)
    (interval_cases finrank Bool code4 <;> norm_num at hpow); rfl
  have hdual := finrank_orthogonal_add_finrank_bool code4
  rw [Fintype.card_fin, hdim] at hdual
  exact ⟨hdim, hcard, by omega, orthogonal_orthogonal_bool code4⟩

/-- Every `Bool`-submodule of `BitString 4` admits a direct-sum complement and 1-dimensional
subspaces when its dimension is at least `1`. -/
example :
    (∃ W : Submodule Bool (BitString 4), IsCompl code4 W) ∧
      ∃ U : Submodule Bool (BitString 4), U ≤ code4 ∧ finrank Bool U = 1 :=
  ⟨exists_isCompl_bool code4,
    exists_submodule_finrank_eq_bool code4 1 (by rw [finrank_and_dual_code4.1]; decide)⟩

example (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : BitString 3) :
    quadForm Q x = bitEquiv (toZModSpace (Fin 3) x ⬝ᵥ Q *ᵥ toZModSpace (Fin 3) x) :=
  quadForm_eq_bitEquiv Q x

/-! ### 2. `LinearEquiv`: concatenation and block decompositions over `Bool` -/

example :
    let u : BitString 2 := ![true, false]
    let v : BitString 3 := ![false, true, true]
    (appendLinearEquiv 2 3).symm (appendLinearEquiv 2 3 (u, v)) = (u, v) ∧
      appendLinearEquiv 2 3 ((u, v) + (u, 0)) =
        appendLinearEquiv 2 3 (u, v) + appendLinearEquiv 2 3 (u, 0) := by
  intro u v
  exact ⟨(appendLinearEquiv 2 3).symm_apply_apply (u, v), map_add (appendLinearEquiv 2 3) _ _⟩

example (x y : BitString 6) :
    piBlocksLinearEquiv ![2, 1, 3] (x + y) =
      piBlocksLinearEquiv ![2, 1, 3] x + piBlocksLinearEquiv ![2, 1, 3] y ∧
      congrLinearEquiv (by decide : 6 = 3 + 3) (x + y) =
        congrLinearEquiv (by decide : 6 = 3 + 3) x +
          congrLinearEquiv (by decide : 6 = 3 + 3) y :=
  ⟨map_add _ x y, map_add _ x y⟩

/-! ### 3. `Multigraph/CutSpace` ↔ `EndpointIncidence` with parallel edges and self-loops -/

/-- Concrete multigraph on `Fin 3` with `5` edges:
- edges `0` and `1`: parallel edges between `0` and `1`;
- edge `2`: between `1` and `2`;
- edge `3`: between `0` and `2`;
- edge `4`: self-loop at `2`. -/
private def uEnd : Fin 5 → Fin 3 := ![0, 0, 1, 0, 2]
private def vEnd : Fin 5 → Fin 3 := ![1, 1, 2, 2, 2]
private def loopParallelEnds : Fin 5 → Sym2 (Fin 3) := fun e => s(uEnd e, vEnd e)

private theorem connected_loopParallel :
    (Multigraph.toSimpleGraph loopParallelEnds).Connected :=
  (Multigraph.connected_toSimpleGraph_iff loopParallelEnds).2 ⟨⟨0⟩, by decide⟩

/-- `incidenceMatrix` matches `Matrix.endpointIncidence uEnd vEnd`: the self-loop column `4`
vanishes while the parallel edges `0` and `1` retain identical nonzero columns. -/
private theorem incidenceMatrix_loopParallel :
    Multigraph.incidenceMatrix loopParallelEnds = Matrix.endpointIncidence uEnd vEnd ∧
      (∀ v, Multigraph.incidenceMatrix loopParallelEnds v 4 = 0) ∧
      Multigraph.incidenceMatrix loopParallelEnds 0 0 = 1 ∧
      Multigraph.incidenceMatrix loopParallelEnds 0 1 = 1 :=
  ⟨Multigraph.incidenceMatrix_eq_endpointIncidence loopParallelEnds fun _ => rfl,
    by decide, by decide, by decide⟩

/-- On the connected 3-vertex, 5-edge multigraph `loopParallelEnds`, the `𝔽₂` cut space is spanned
by the vertex incidences, has dimension `3 - 1 = 2`, and its orthogonal cycle space has cyclomatic
dimension `5 - 3 + 1 = 3` (witnessed by the parallel-edge 2-cycle `{0, 1}`, the triangle
`{0, 2, 3}`, and the self-loop 1-cycle `{4}`). -/
private theorem cutSpace_and_cycleSpace_loopParallel :
    Multigraph.cutSpace loopParallelEnds = Submodule.span (ZMod 2)
      (Set.range fun v : Fin 3 => fun e : Fin 5 =>
        if e ∈ Multigraph.incidence loopParallelEnds v then (1 : ZMod 2) else 0) ∧
    finrank (ZMod 2) (Multigraph.cutSpace loopParallelEnds) = 2 ∧
    finrank (ZMod 2) (LinearMap.ker (Multigraph.incidenceMatrix loopParallelEnds).mulVecLin) = 3 ∧
    ![1, 1, 0, 0, 0] ∈ BitString.orthogonal (Multigraph.cutSpace loopParallelEnds) ∧
    ![1, 0, 1, 1, 0] ∈ BitString.orthogonal (Multigraph.cutSpace loopParallelEnds) ∧
    ![0, 0, 0, 0, 1] ∈ BitString.orthogonal (Multigraph.cutSpace loopParallelEnds) := by
  have hcut := Multigraph.finrank_cutSpace_add_one connected_loopParallel
  have hcyc := Multigraph.finrank_ker_incidenceMatrix_add_card connected_loopParallel
  simp only [Fintype.card_fin] at hcut hcyc
  refine ⟨Multigraph.cutSpace_eq_span_incidence loopParallelEnds,
    by omega, by omega, ?_, ?_, ?_⟩ <;>
    · rw [Multigraph.orthogonal_cutSpace, LinearMap.mem_ker]
      decide

/-! ### 4. `Multidigraph` ↔ `Digraph` bridges -/

/-- Simple digraph on `Fin 3` with arcs `0 → 1`, `1 → 2`, `0 → 2`, and self-loop `1 → 1`. -/
private def sampleDigraph : Digraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 1)

private instance : DecidableRel sampleDigraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

example :
    Multidigraph.toDigraph (Multidigraph.arcSrc sampleDigraph)
      (Multidigraph.arcTgt sampleDigraph) = sampleDigraph ∧
    Multidigraph.arcMatrix (Multidigraph.arcSrc sampleDigraph)
      (Multidigraph.arcTgt sampleDigraph) ℤ = sampleDigraph.adjMatrix ℤ :=
  ⟨Multidigraph.toDigraph_arcSrc_arcTgt sampleDigraph,
    Multidigraph.arcMatrix_arcSrc_arcTgt ℤ sampleDigraph⟩

example :
    Nat.card {f : {v : Fin 3 // v ≠ 2} → Multidigraph.Arc sampleDigraph //
      Multidigraph.IsInArborescence (Multidigraph.arcSrc sampleDigraph)
        (Multidigraph.arcTgt sampleDigraph) 2 f} =
    Nat.card {T : Digraph (Fin 3) // T ≤ sampleDigraph ∧ T.IsInArborescence 2} :=
  Nat.card_congr (Multidigraph.arborescenceEquivSubdigraph sampleDigraph 2)

example :
    let p : List (Fin 3) := [0, 1, 2]
    let hS : ∀ e ∈ p.zip p.tail, sampleDigraph.Adj e.1 e.2 := by decide
    let q := (p.zip p.tail).pmap (fun e he => (⟨e, he⟩ : Multidigraph.Arc sampleDigraph)) hS
    Multidigraph.IsDipath (Multidigraph.arcSrc sampleDigraph)
      (Multidigraph.arcTgt sampleDigraph) 0 2 q ∧
      0 :: q.map (Multidigraph.arcTgt sampleDigraph) = [0, 1, 2] :=
  let h := Multidigraph.isDipath_pmap_zip_tail
    (Multidigraph.arcSrc sampleDigraph) (Multidigraph.arcTgt sampleDigraph)
    (fun e he => (⟨e, he⟩ : Multidigraph.Arc sampleDigraph)) (fun _ _ => ⟨rfl, rfl⟩)
    (p := [0, 1, 2]) (by decide) rfl rfl (by decide)
  ⟨h.1, h.2.1⟩

/-! ### 5. `BitString.BitVec`: little-endian `BitVec` equivalence and bitwise vs. modular `+` -/

-- Little-endian layout (`1 + 0 + 4 = 5`), zero, and bitwise complement on 3-bit strings.
example :
    equivBitVec ![true, false, true] = 5#3 ∧
    equivBitVec.symm 5#3 = ![true, false, true] ∧
    (equivBitVec ![true, false, true]).toNat = (equivFin 3 ![true, false, true] : ℕ) ∧
    equivBitVec (0 : BitString 3) = 0#3 ∧
    equivBitVec (![true, false, true]ᶜ : BitString 3) = 2#3 := by
  decide

-- Coordinate access, unsigned value agreement, and `BooleanRing` bitwise operations (`0`, `ᶜ`,
-- XOR `+`, and AND `*`).
example {w : ℕ} (x y : BitString w) (v : BitVec w) (i : Fin w) :
    (equivBitVec x).getLsbD i.val = x i ∧
    (equivBitVec x)[i.val] = x i ∧
    equivBitVec.symm v i = v[i.val] ∧
    equivBitVec (fun j : Fin w => v.getLsbD j.val) = v ∧
    (equivBitVec x).toNat = (equivFin w x : ℕ) ∧
    equivBitVec (0 : BitString w) = 0#w ∧
    equivBitVec.symm 0#w = (0 : BitString w) ∧
    equivBitVec xᶜ = ~~~equivBitVec x ∧
    equivBitVec (x + y) = (equivBitVec x ^^^ equivBitVec y) ∧
    equivBitVec (x * y) = (equivBitVec x &&& equivBitVec y) := by
  refine ⟨getLsbD_equivBitVec x i, getElem_equivBitVec x i.val i.isLt,
    equivBitVec_symm_apply v i, equivBitVec_getLsbD v, toNat_equivBitVec_eq_equivFin x,
    equivBitVec_zero, equivBitVec_symm_zero, equivBitVec_compl x, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getElem_eq
    intro j hj
    simp only [getElem_equivBitVec, BitVec.getElem_xor, BitVec.getElem_and,
      Pi.add_apply, Pi.mul_apply]
    cases x ⟨j, hj⟩ <;> cases y ⟨j, hj⟩ <;> rfl

-- At `w = 2`, `BooleanRing` `+` on `BitString 2` is coordinatewise XOR (`1 ⊕ 3 = 2`), whereas
-- `BitVec` `+` is modular addition mod `4` (`1 + 3 ≡ 0 (mod 4)`), so `equivBitVec` does not
-- intertwine `BooleanRing` `+` with `BitVec` `+`.
example :
    let u : BitString 2 := ![true, false]
    let v : BitString 2 := ![true, true]
    equivBitVec u = 1#2 ∧
    equivBitVec v = 3#2 ∧
    equivBitVec (u + v) = 2#2 ∧
    equivBitVec u + equivBitVec v = 0#2 ∧
    equivBitVec (u + v) ≠ equivBitVec u + equivBitVec v := by
  decide

end CslibFrontierTests.BitStringZModCutSpace
