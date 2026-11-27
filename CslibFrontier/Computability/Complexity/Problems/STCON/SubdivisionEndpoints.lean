/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.FlatQuery

/-!
# Fixed subdivision endpoints for layered STCON

The source is the initial column in layer zero. The target is the sink column in the
final layer. Both are represented by offset-zero roots so that the scan can use the
same flat IDs for its endpoints and its adjacency queries.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.QueryMachine.Subdivision
open Cslib.LayeredDigraph.Subdivision

/-- Number the slots of a subdivided layered instance by flattening the layer and column,
then flattening the original label and chain offset. -/
abbrev subdivisionIndex (I : STCONInstance) (bound : ℕ) :
    Vertex (Fin ((I.n - 1) + 1) × Fin I.n) bound ≃
      Fin ((((I.n - 1) + 1) * I.n) * (bound + 1)) :=
  ((equivProd _ bound).trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))).trans
    ((equivProd _ bound).symm.trans (flatIndex _ bound))

/-- The numbering agrees with the flat adjacency interface after flattening the original
vertex. -/
theorem subdivisionIndex_apply (I : STCONInstance) (bound : ℕ)
    (v : Vertex (Fin ((I.n - 1) + 1) × Fin I.n) bound) :
    subdivisionIndex I bound v =
      flatIndex (((I.n - 1) + 1) * I.n) bound ⟨finProdFinEquiv v.vertex, v.offset⟩ := by
  simp only [subdivisionIndex, Equiv.trans_apply, equivProd_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  congr 1
  simpa only [equivProd_apply] using
    (equivProd (Fin (((I.n - 1) + 1) * I.n)) bound).apply_symm_apply
      (finProdFinEquiv v.vertex, v.offset)

/-- The root of an original vertex is numbered by the scalar root ID of its row-major label. -/
theorem subdivisionIndex_root_val (I : STCONInstance) (bound : ℕ)
    (v : Fin ((I.n - 1) + 1) × Fin I.n) :
    (subdivisionIndex I bound (root bound v)).val = rootID (finProdFinEquiv v).val bound := by
  rw [subdivisionIndex_apply]
  exact (rootID_eq_flatIndex _ bound).symm

/-- The source and target IDs for the scan, computed from the graph parameters and chain
bound. The final layer and the sink column are both the predecessor of the width. -/
def subdivisionEndpointIDs (p : LayeredParameters × ℕ) : ℕ × ℕ :=
  let last := p.1.width - 1
  (rootID p.1.source p.2, rootID (last + p.1.width * last) p.2)

/-- The scalar endpoint computation agrees with the indexed roots of the actual layered
configuration graph. Both IDs belong to the same rectangular carrier as adjacency. -/
theorem subdivisionEndpointIDs_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (bound : ℕ) :
    let I := configurationInstance ntm c w
    let index := subdivisionIndex I bound
    subdivisionEndpointIDs (layeredParameters ntm c w.length, bound) =
      ((index (root bound (layeredCoordinates I (layeredStart I)))).val,
        (index (root bound (layeredCoordinates I (layeredTarget I)))).val) := by
  let I := configurationInstance ntm c w
  dsimp only
  rw [subdivisionIndex_root_val, subdivisionIndex_root_val]
  change (rootID _ _, rootID _ _) = (rootID (I.s.val + I.n * 0) _,
    rootID (I.t.val + I.n * (I.n - 1)) _)
  simp [layeredParameters, I, configurationInstance]

/-- Preparing both IDs takes native workspace linear in the encoded graph parameters
and chain bound. -/
theorem subdivisionEndpointIDs_inSpace :
    ComputableInSpace subdivisionEndpointIDs (encPair encLayeredParameters encNat)
      (encPair encNat encNat) (fun p => (encPair encLayeredParameters encNat p).length) := by
  have hp := fst encLayeredParameters encNat
  have hb := snd encLayeredParameters encNat
  have hw := encLayeredParameters_width_budget hp
  have hl := budget_natPred hw
  have hs := budget_comp_linear rootID_inSpace
    (budget_prod (encLayeredParameters_source_budget hp) hb)
  have ht := budget_comp_linear rootID_inSpace
    (budget_prod (budget_natAdd hl (budget_natMul hw hl)) hb)
  exact budget_prod hs ht

end Cslib.Complexity.STCON
