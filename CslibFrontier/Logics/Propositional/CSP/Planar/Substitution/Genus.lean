/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Rotation
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArityOccurrence
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.ProbeParity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceDartColors
import CslibFrontier.Foundations.Data.BitString.CyclicSeam
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Darts
import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryColors
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VariableCycleColors
import Mathlib.Data.List.GetD

/-!
# Numerical genus and full certificate acceptance for actual substitution

The original source constraint cycle and the actual reversed gadget probe carry the same
internally determined marker bits. Their clockwise corner colors therefore differ by one
uniform shift on each complete gadget copy, including every disconnected body component.
At arity zero the shift is false and no marker is selected.

The exact free and auxiliary word paths descend to the emitted replacement rotation.
The existing componentwise cycle-space converse proves its numerical genus zero, including
closed and nullary components. Its canonical table is the actual computed certificate, so
the full original ordered numerical checker accepts that table on every accepted,
well-formed source. No finite relation alphabet or target invariant provider is required.

## Main results

* `numericalGenusZero_replacementRotation`: genus of the actual positional rotation.
* `verifyRotationCertificate_replacementCertificate`: full original target checker acceptance.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

section PrivateHelpers

variable (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
  (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)

private theorem colorAtIndex_incidenceDart {α V : Type} [DecidableEq V] {G : CSP α V}
    (P : Dart (incidenceGraph G) → Bool) (o : G.Occurrence) :
    (Dart.colorAtIndex P (2 * incidenceEdgeIndex o),
      Dart.colorAtIndex P (2 * incidenceEdgeIndex o + 1)) =
      (P (incidenceDart o false), P (incidenceDart o true)) :=
  Prod.mk.injEq _ _ _ _ ▸ ⟨Dart.colorAtIndex_index P (incidenceDart o false),
    Dart.colorAtIndex_index P (incidenceDart o true)⟩

private theorem exists_copy_colorShifts (hF : WellFormed srcArity F)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (r : RotationSystem (incidenceGraph F)) (hr : RespectsArgumentOrder r)
    (Ps : Dart (incidenceGraph F) → Bool) (hs : ∀ d, Ps (r.rotate d) = Ps d.reverse)
    (hxs : ∀ d, (Ps d ^^ Ps d.reverse) = sourceEdgeLabels gadgets witnesses B F x d.1)
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (hg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      Pg i ((witnesses F[i.val].rel).probeRotation.rotate d) = Pg i d.reverse)
    (hxg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      (Pg i d ^^ Pg i d.reverse) = copiedProbeLabels gadgets witnesses B F i x d.1) :
    ∀ i : Fin F.length, ∃ K : Bool, (srcArity F[i.val].rel = 0 → K = false) ∧
      (∀ a, (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false) ^^ K) =
        Ps (incidenceDart (arityOccurrence F hF i a) true)) ∧
      ∀ a, (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) true) ^^ K) =
        Ps (incidenceDart (arityOccurrence F hF i a) false) := by
  intro i
  apply Cslib.BitString.exists_uniform_colorSeam
    (fun a => Ps (incidenceDart (arityOccurrence F hF i a) true))
    (fun a => Ps (incidenceDart (arityOccurrence F hF i a) false))
    (fun a => Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false))
    (fun a => Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) true))
  · intro a
    rw [← argumentSuccessor_arityOccurrence F hF i a, ← hr (arityOccurrence F hF i a)]
    exact hs (incidenceDart (arityOccurrence F hF i a) true)
  · intro a
    have h := hg i (incidenceDart
      (gadgetProbeOccurrence (gadgets F[i.val].rel) (finRotate (srcArity F[i.val].rel) a)) true)
    rw [(witnesses F[i.val].rel).respectsArgumentOrder_probeRotation,
      argumentSuccessor_gadgetProbeOccurrence_reverse] at h
    exact h.symm
  · intro a
    have hleft := hxs (incidenceDart (arityOccurrence F hF i a) true)
    have hright := hxg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false)
    rw [sourceEdgeLabels_incidenceDart gadgets witnesses B F x (arityOccurrence F hF i a) true
      a rfl] at hleft
    rw [copiedProbeLabels_marker] at hright
    exact hleft.trans hright.symm

private noncomputable def copyColors
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool)
    (q : Σ i : Fin F.length, (gadgets F[i.val].rel).body.Occurrence) (side : Bool) : Bool :=
  Pg q.1 (incidenceDart
    (bodyOccurrence (gadgets F[q.1.val].rel).body (List.ofFn Sum.inl) q.2) side) ^^ K q.1

private noncomputable def replacementColors
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool) :
    Dart (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)) → Bool :=
  fun d =>
    let p := (incidenceDartEquiv _).symm d
    let q := (replacementOccurrenceEquiv gadgets B F).symm p.1
    copyColors gadgets F Pg K q p.2

private theorem replacementColors_incidenceDart
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) (side : Bool) :
    replacementColors gadgets B F Pg K
        (incidenceDart (replacementOccurrence gadgets B F i o) side) =
      (Pg i (incidenceDart
        (bodyOccurrence (gadgets F[i.val].rel).body (List.ofFn Sum.inl) o) side) ^^ K i) := by
  dsimp only [replacementColors]
  have ho := (replacementOccurrenceEquiv gadgets B F).symm_apply_apply ⟨i, o⟩
  rw [replacementOccurrenceEquiv_apply] at ho
  rw [← incidenceDartEquiv_apply (replacementOccurrence gadgets B F i o, side),
    Equiv.symm_apply_apply, ho]
  rfl

private theorem replacementColors_xor_reverse
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool)
    (hxg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      (Pg i d ^^ Pg i d.reverse) = copiedProbeLabels gadgets witnesses B F i x d.1) :
    ∀ d, (replacementColors gadgets B F Pg K d ^^
      replacementColors gadgets B F Pg K d.reverse) = x d.1 := by
  intro d
  obtain ⟨o, ho⟩ := exists_incidenceDart d
  obtain ⟨i, p, rfl⟩ := exists_replacementOccurrence gadgets B F o
  rw [← ho]
  change (replacementColors gadgets B F Pg K (incidenceDart _ d.2) ^^
    replacementColors gadgets B F Pg K (incidenceDart _ (!d.2))) = _
  rw [replacementColors_incidenceDart, replacementColors_incidenceDart,
    Bool.xor_assoc, Bool.xor_left_comm (K i), Bool.xor_self, Bool.xor_false,
    ← copiedProbeLabels_bodyOccurrence gadgets witnesses B F i x p d.2]
  exact hxg i (incidenceDart
    (bodyOccurrence (gadgets F[i.val].rel).body (List.ofFn Sum.inl) p) d.2)

private theorem replacementColors_rotate_constraint
    (hB : ∀ r, (gadgets r).numAux ≤ B) (hF : WellFormed srcArity F)
    (c : RotationCertificate) (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool)
    (hg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      Pg i ((witnesses F[i.val].rel).probeRotation.rotate d) = Pg i d.reverse)
    (i : Fin F.length) (o : (gadgets F[i.val].rel).body.Occurrence) :
    replacementColors gadgets B F Pg K
      ((replacementRotation gadgets witnesses B hB F hF c hc).rotate
        (incidenceDart (replacementOccurrence gadgets B F i o) true)) =
      replacementColors gadgets B F Pg K
        (incidenceDart (replacementOccurrence gadgets B F i o) false) := by
  rw [respectsArgumentOrder_replacementRotation, argumentSuccessor_replacementOccurrence,
    replacementColors_incidenceDart, replacementColors_incidenceDart]
  have h := hg i (incidenceDart
    (bodyOccurrence (gadgets F[i.val].rel).body (List.ofFn Sum.inl) o) true)
  rw [(witnesses F[i.val].rel).respectsArgumentOrder_probeRotation,
    argumentSuccessor_bodyOccurrence] at h
  exact congrArg (fun b => b ^^ K i) h

private theorem map_shiftBlock_replacementColors
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool) (i : Fin F.length) (word : List ℕ)
    (hw : ∀ j ∈ word, ∃ o : (gadgets F[i.val].rel).body.Occurrence,
      incidenceEdgeIndex o = j) :
    ((shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i.val) word).map
      fun j => (Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j),
        Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j + 1))) =
      word.map (fun j => (Dart.colorAtIndex (Pg i) (2 * j) ^^ K i,
        Dart.colorAtIndex (Pg i) (2 * j + 1) ^^ K i)) := by
  simp only [shiftBlock, List.map_map, Function.comp_def]
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨o, rfl⟩ := hw j hj
  have hb := Prod.mk.inj (colorAtIndex_incidenceDart (Pg i)
    (bodyOccurrence (gadgets F[i.val].rel).body (List.ofFn Sum.inl) o))
  rw [incidenceEdgeIndex_bodyOccurrence] at hb
  rw [← incidenceEdgeIndex_replacementOccurrence gadgets B F i o, colorAtIndex_incidenceDart,
    replacementColors_incidenceDart, replacementColors_incidenceDart, hb.1, hb.2]

private theorem isChain_shifted_boundaryColors
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool) (i : Fin F.length)
    (v : Fin (srcArity F[i.val].rel) ⊕ Fin (gadgets F[i.val].rel).numAux) (entry exit : Bool)
    (hc : List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((entry, entry) :: (boundaryBlock (gadgets F[i.val].rel) (witnesses F[i.val].rel) v).map
        (fun j => (Dart.colorAtIndex (Pg i) (2 * j), Dart.colorAtIndex (Pg i) (2 * j + 1))) ++
        [(exit, exit)])) :
    List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((entry ^^ K i, entry ^^ K i) ::
        ((shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i.val)
          (boundaryBlock (gadgets F[i.val].rel) (witnesses F[i.val].rel) v)).map
          fun j => (Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j),
            Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j + 1))) ++
        [(exit ^^ K i, exit ^^ K i)]) := by
  rw [map_shiftBlock_replacementColors gadgets B F Pg K i _ fun j hj =>
    ((mem_boundaryBlock_iff _ _ v j).mp hj).imp fun _ h => h.1]
  have h := List.isChain_map_of_isChain (S := fun p q : Bool × Bool => p.2 = q.1)
    (fun p : Bool × Bool => (p.1 ^^ K i, p.2 ^^ K i)) (fun _ _ => congrArg (· ^^ K i)) hc
  simpa only [List.map_cons, List.map_append, List.map_map, List.map_nil, Function.comp_def] using h

private theorem isChain_incidenceBlock_colors
    (hF : WellFormed srcArity F) (Ps : Dart (incidenceGraph F) → Bool)
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool)
    (hg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      Pg i ((witnesses F[i.val].rel).probeRotation.rotate d) = Pg i d.reverse)
    (hKvar : ∀ (i : Fin F.length) a,
      (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) true) ^^ K i) =
        Ps (incidenceDart (arityOccurrence F hF i a) false))
    (hKcenter : ∀ (i : Fin F.length) a,
      (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false) ^^ K i) =
        Ps (incidenceDart (arityOccurrence F hF i a) true)) (o : F.Occurrence) :
    List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((Ps (incidenceDart o false), Ps (incidenceDart o false)) ::
        ((incidenceBlock (fun r => (gadgets r).template)
          (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F
          (incidenceDart o false).index).map
          fun j => (Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j),
            Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j + 1))) ++
        [(Ps (incidenceDart o true), Ps (incidenceDart o true))]) := by
  let a : Fin (srcArity F[o.1.val].rel) :=
    Fin.cast (hF F[o.1.val] (List.getElem_mem o.1.isLt)) o.2
  have ho : arityOccurrence F hF o.1 a = o := CSP.Occurrence.eq_of_positions rfl rfl
  have h := isChain_shifted_boundaryColors gadgets witnesses B F Pg K o.1 (Sum.inl a) _ _
    (isChain_freeBoundaryBlock_colors (gadgets F[o.1.val].rel) (witnesses F[o.1.val].rel) a
      (Pg o.1) (hg o.1))
  have hrev : (incidenceDart (gadgetProbeOccurrence (gadgets F[o.1.val].rel) a) false).reverse =
      incidenceDart (gadgetProbeOccurrence (gadgets F[o.1.val].rel) a) true := rfl
  rw [hrev, hKvar, hKcenter, ho] at h
  change List.IsChain _ (_ :: ((incidenceBlock _ _ F
    (2 * incidenceEdgeIndex o)).map _) ++ _)
  rw [incidenceBlock_occurrence]
  exact h

private theorem isChain_variableBlock_colors
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (Ps : Dart (incidenceGraph F) → Bool)
    (hs : ∀ d, Ps ((RotationCertificate.decode _ c hc).rotate d) = Ps d.reverse)
    (Pg : ∀ i : Fin F.length,
      Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))) → Bool)
    (K : Fin F.length → Bool)
    (hg : ∀ (i : Fin F.length)
      (d : Dart (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl)))),
      Pg i ((witnesses F[i.val].rel).probeRotation.rotate d) = Pg i d.reverse)
    (hKvar : ∀ (i : Fin F.length) a,
      (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) true) ^^ K i) =
        Ps (incidenceDart (arityOccurrence F hF i a) false))
    (hKcenter : ∀ (i : Fin F.length) a,
      (Pg i (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false) ^^ K i) =
        Ps (incidenceDart (arityOccurrence F hF i a) true)) (v : ℕ) (hv : v ∈ F.vars) :
    ∃ color : Bool, List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((color, color) :: ((variableBlock (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F c v).map
          fun j => (Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j),
            Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * j + 1))) ++
        [(color, color)]) := by
  obtain ⟨q, hq, _⟩ := exists_occurrence_at_first_index v hv
  have hstart : (incidenceDart q false).index = 2 * F.vars.idxOf v := congrArg (2 * ·) hq
  refine ⟨Ps (incidenceDart q false), ?_⟩
  unfold variableBlock
  rw [CSP.map_occurrences, ← hstart, List.map_flatMap]
  apply List.isChain_colorPairs_flatMap
    (RotationCertificate.cycleWord c (incidenceDart q false).index)
    (fun j => (incidenceBlock (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F j).map
        fun k => (Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * k),
          Dart.colorAtIndex (replacementColors gadgets B F Pg K) (2 * k + 1)))
    (Dart.colorAtIndex Ps) (Dart.colorAtIndex fun d => Ps d.reverse)
    (RotationCertificate.isChain_colors_cycleWord hc (incidenceDart q false) Ps hs)
  intro j hj
  obtain ⟨p, hp, _⟩ := (mem_variable_cycleWord_iff hc q j).mp hj
  rw [hp]
  change List.IsChain _
    ((Dart.colorAtIndex Ps (incidenceDart p false).index,
      Dart.colorAtIndex Ps (incidenceDart p false).index) :: _ ++
      [(Dart.colorAtIndex (fun d => Ps d.reverse) (incidenceDart p false).index,
        Dart.colorAtIndex (fun d => Ps d.reverse) (incidenceDart p false).index)])
  rw [Dart.colorAtIndex_index, Dart.colorAtIndex_index]
  exact isChain_incidenceBlock_colors gadgets witnesses B F hF Ps Pg K hg hKvar hKcenter p

end PrivateHelpers

/-- The exact replacement rotation has componentwise numerical genus zero. Every edge
labeling and every face color used in the proof is derived internally from the accepted source
table and actual checked gadget witnesses. Repeated names and empty blocks are allowed. -/
theorem numericalGenusZero_replacementRotation
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : verifyRotationCertificate F c = true) :
    (replacementRotation gadgets witnesses B hB F hF c
      ((verifyRotationCertificate_eq_true_iff _ _).mp hc).1).NumericalGenusZero := by
  classical
  obtain ⟨hraw, hrgenus, hrorder⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hc
  let r := RotationCertificate.decode (incidenceGraph F) c hraw
  apply RotationSystem.numericalGenusZero_of_vertexEven_dartColors
    _ (incidenceVertices_declared _)
  intro x hx
  obtain ⟨Ps, hs, hxs⟩ := (r.exists_faceColors_iff_exists_dartColors
    (sourceEdgeLabels gadgets witnesses B F x)).mp
      ((r.vertexEven_iff_exists_faceColors (incidenceVertices_declared F) hrgenus _).mp
        (vertexEven_sourceEdgeLabels gadgets witnesses B hB F hF c hraw x hx))
  have hlocal (i : Fin F.length) :=
    ((witnesses F[i.val].rel).probeRotation.exists_faceColors_iff_exists_dartColors _).mp
      (((witnesses F[i.val].rel).probeRotation.vertexEven_iff_exists_faceColors
        (incidenceVertices_declared _)
        (witnesses F[i.val].rel).numericalGenusZero_probeRotation _).mp
        (vertexEven_copiedProbeLabels gadgets witnesses B hB F i x hx))
  choose Pg hg hxg using hlocal
  choose K hKzero hKcenter hKvar using
    exists_copy_colorShifts gadgets witnesses B F hF x r hrorder Ps hs hxs Pg hg hxg
  refine ⟨replacementColors gadgets B F Pg K, ?_,
    replacementColors_xor_reverse gadgets witnesses B F x Pg K hxg⟩
  unfold replacementRotation
  apply colors_rotate_rotationOfVariableCycles _ _ _
    (nodup_flatten_replacementCycles gadgets witnesses F hF c hraw)
    (replacementColors gadgets B F Pg K)
  · intro o
    obtain ⟨i, p, rfl⟩ := exists_replacementOccurrence gadgets B F o
    have h := replacementColors_rotate_constraint gadgets witnesses B F hB hF c hraw Pg K hg i p
    rwa [respectsArgumentOrder_replacementRotation] at h
  · intro word hw
    rw [mem_replacementCycles_iff] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨i, block, hb, rfl⟩
    · exact isChain_variableBlock_colors gadgets witnesses B F hF c hraw Ps hs Pg K hg
        hKvar hKcenter v (CSP.mem_distinctVars.mp hv)
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
      let a : Fin (gadgets F[i.val].rel).numAux := ⟨j, length_auxiliaryBoundaryBlocks _ _ ▸ hj⟩
      obtain ⟨color, hc⟩ := isChain_auxiliaryBoundaryBlock_colors
        (gadgets F[i.val].rel) (witnesses F[i.val].rel) a (Pg i) (hg i)
      refine ⟨color ^^ K i, ?_⟩
      simpa only [a, boundaryBlock, Sum.elim_inr, List.getD_eq_getElem _ _ hj] using
        isChain_shifted_boundaryColors gadgets witnesses B F Pg K i (Sum.inr a) color color hc

/-- The full existing ordered numerical checker accepts the literal computed replacement
certificate on every well-formed source with an actually accepted source certificate. The
target body and table are exactly the original replacement and deterministic block splice. -/
theorem verifyRotationCertificate_replacementCertificate
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : verifyRotationCertificate F c = true) :
    verifyRotationCertificate (replaceGadgets B (fun r => (gadgets r).template) F)
      (replacementCertificate B (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
        (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c) = true := by
  let hraw := ((verifyRotationCertificate_eq_true_iff _ _).mp hc).1
  rw [← ofRotation_replacementRotation gadgets witnesses B hB F hF c hraw]
  exact verifyRotationCertificate_ofRotation _
    (numericalGenusZero_replacementRotation gadgets witnesses B hB F hF c hc)
    (respectsArgumentOrder_replacementRotation gadgets witnesses B hB F hF c hraw)

end Cslib.Complexity.CSP.GadgetRotation
