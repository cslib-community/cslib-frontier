/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.PathData
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Geometry.Orthogonal.Subdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


/-!
# Native computation of canonical path data

Input natural labels and coordinates use binary encodings; syntactic positions and the
subdivision budget use unary counters. These certificates compute only the shared paths,
crossing cells, and occurrence lookup, with no geometric validity assumption.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_budget`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_paths`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_crossingSites`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_occurrencePath`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal
open Turing.MultiTapeTM

private theorem computable_finVal :
    ComputableInPolyTime (fun s : Fin 3 => s.val) (encFinEnum (Fin 3)) encUnary :=
  ComputableInPolyTime.of_finite _

attribute [local fun_prop] computable_finVal

private theorem computable_incidencePort :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.incidencePort p.2)
      (encPair encGraph encUnary) (encFinEnum (Fin 3)) := by
  let unary3 : Fin 3 ↪ List Bool :=
    ⟨fun index => encUnary index.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩
  have hmod : ComputableInPolyTime (fun index : ℕ =>
      (⟨index % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3)) encUnary (encFinEnum (Fin 3)) :=
    (ComputableInPolyTime.of_finite (encIn := unary3) (encOut := encFinEnum (Fin 3)) id).comp
      ((ComputableInPolyTime.unary_mod.comp
        (ComputableInPolyTime.id'.prod (.const 3))).of_enc_eq fun _ => rfl)
  have hiv : ComputableInPolyTime Graph.incidenceVertices encGraph (encList encNat) := by
    unfold Graph.incidenceVertices; fun_prop
  have htake : ComputableInPolyTime (fun q : List ℕ × ℕ => q.1.take q.2)
      (encPair (encList encNat) encUnary) (encList encNat) := by fun_prop
  exact hmod.comp (show ComputableInPolyTime (fun p : Graph × ℕ =>
    (p.1.incidenceVertices.take p.2).count (p.1.incidenceVertices.getD p.2 0))
    (encPair encGraph encUnary) encUnary by fun_prop)

attribute [local fun_prop] computable_incidencePort

private theorem computable_canonicalPorts :
    ComputableInPolyTime Graph.canonicalPorts encGraph
      (encList (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3)))) := by
  unfold Graph.canonicalPorts
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp
      (show ComputableInPolyTime (fun G : Graph => G.edges.length) encGraph encUnary by fun_prop))
    (by fun_prop)

attribute [local fun_prop] computable_canonicalPorts

/-- `Layout.center` is computable in polynomial time from a unary index. -/
theorem computable_layoutCenter :
    ComputableInPolyTime Layout.center encUnary encPoint := by
  unfold Layout.center encPoint; fun_prop

private theorem computable_layoutColumn :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.column p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encIntBin := by
  unfold Layout.column; fun_prop

private theorem computable_layoutTrack :
    ComputableInPolyTime (fun p : ℕ × ℕ => Layout.track p.1 p.2)
      (encPair encUnary encUnary) encIntBin := by
  unfold Layout.track; fun_prop

attribute [local fun_prop] computable_layoutCenter computable_layoutColumn computable_layoutTrack

private theorem computable_layoutElbow :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.elbow p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encPoint := by
  unfold Layout.elbow encPoint; fun_prop

attribute [local fun_prop] computable_layoutElbow

private theorem computable_layoutRoute :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ × Fin 3 × Fin 3 =>
      Layout.route p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3))))))) encRoute := by
  unfold Layout.route encRoute; fun_prop

attribute [local fun_prop] computable_layoutRoute

private theorem computable_orthogonalRoutes :
    ComputableInPolyTime (fun G : Graph => G.orthogonalRoutes G.canonicalPorts)
      encGraph (encList encRoute) := by
  fun_prop [Graph.orthogonalRoutes]

attribute [local fun_prop] computable_orthogonalRoutes

/-- The budget is a linear expression in syntactic list lengths, computed as a unary counter. -/
@[fun_prop]
theorem computableInPolyTime_budget : ComputableInPolyTime budget encCNF encUnary := by
  fun_prop [budget]

/-- Canonical incidence routes have a native polynomial-time bounded unit expansion.
The input labels and output coordinates are binary; only the step budget is unary. -/
@[fun_prop]
theorem computableInPolyTime_paths :
    ComputableInPolyTime paths encCNF (encList encRoute) := by
  change ComputableInPolyTime (fun φ =>
    ((SAT.incidenceGraph φ).orthogonalRoutes (SAT.incidenceGraph φ).canonicalPorts).map
      (subdivideWithin (budget φ))) encCNF (encList encRoute)
  simpa only [Function.comp_def, encCNF] using ComputableInPolyTime.mapWithInput
    (computable_orthogonalRoutes.comp (SAT.computableInPolyTime_incidenceGraph encNat))
    (computableInPolyTime_subdivideWithin.comp
      (show ComputableInPolyTime (fun p : CNF ℕ × Route => (budget p.1, p.2))
        (encPair encCNF encRoute) (encPair encUnary encRoute) by fun_prop))

private def endpointColumns (p : Graph × ℕ) : Point :=
  (Layout.column (p.1.vertices.idxOf (p.1.edgeEndpoint p.2 false))
      (Graph.portAt p.1.canonicalPorts p.2 false),
    Layout.column (p.1.vertices.idxOf (p.1.edgeEndpoint p.2 true))
      (Graph.portAt p.1.canonicalPorts p.2 true))

private theorem computable_endpointColumns :
    ComputableInPolyTime endpointColumns (encPair encGraph encUnary) encPoint := by
  fun_prop [endpointColumns, Graph.edgeEndpoint, Graph.portAt]

attribute [local fun_prop] computable_endpointColumns

private def candidatePair (p : Graph × (ℕ × ℕ)) : List Point :=
  [((endpointColumns (p.1, p.2.2)).1, Layout.track p.1.vertices.length p.2.1),
    ((endpointColumns (p.1, p.2.2)).2, Layout.track p.1.vertices.length p.2.1)]

private theorem computable_candidatePair :
    ComputableInPolyTime candidatePair (encPair encGraph (encPair encUnary encUnary))
      (encList encPoint) := by
  fun_prop [candidatePair]

private def candidateRow (p : Graph × ℕ) : List Point :=
  (List.range p.1.edges.length).flatMap fun j => candidatePair (p.1, p.2, j)

private theorem computable_edgeRange :
    ComputableInPolyTime (fun G : Graph => List.range G.edges.length) encGraph
      (encList encUnary) :=
  ComputableInPolyTime.range.comp
    ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp (by fun_prop))

private theorem computable_candidateRow :
    ComputableInPolyTime candidateRow (encPair encGraph encUnary) (encList encPoint) := by
  change ComputableInPolyTime (fun p : Graph × ℕ =>
    (List.range p.1.edges.length).flatMap fun j => candidatePair (p.1, p.2, j)) _ _
  simpa only [Function.comp_def] using ComputableInPolyTime.flatMapWithInput
    (computable_edgeRange.comp (ComputableInPolyTime.fst encGraph encUnary))
    (computable_candidatePair.comp
      (show ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
        (encPair (encPair encGraph encUnary) encUnary)
        (encPair encGraph (encPair encUnary encUnary)) by fun_prop))

private theorem computable_crossingCandidates :
    ComputableInPolyTime (fun G : Graph => G.crossingCandidates G.canonicalPorts)
      encGraph (encList encPoint) := by
  simpa only [candidateRow, candidatePair, endpointColumns, Graph.crossingCandidates] using
    ComputableInPolyTime.flatMapWithInput
      (f := fun G i => candidateRow (G, i)) (encB := encPoint)
      computable_edgeRange computable_candidateRow

attribute [local fun_prop] computable_crossingCandidates

private theorem computable_orthogonalPositions :
    ComputableInPolyTime Graph.orthogonalPositions encGraph encRoute := by
  unfold Graph.orthogonalPositions encRoute
  exact (ComputableInPolyTime.map computable_layoutCenter).comp
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list encNat).comp (by fun_prop)))

attribute [local fun_prop] computable_orthogonalPositions

/-- Deduplicating a route via `selectDistinct` with an all-`true` mask is polynomial-time
computable. -/
theorem computable_distinctPoints :
    ComputableInPolyTime (fun l : Route => selectDistinct l (List.replicate l.length true))
      encRoute encRoute := by
  have hrep : ComputableInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hlen : ComputableInPolyTime (fun l : Route => l.length) encRoute encUnary := by fun_prop
  unfold encRoute at *; fun_prop

private theorem computable_crossingPredicate :
    ComputableInPolyTime (fun p : CNF ℕ × Point =>
      !((SAT.incidenceGraph p.1).orthogonalPositions.contains p.2) &&
        decide (2 ≤ ((paths p.1).filter fun r => r.contains p.2).length))
      (encPair encCNF encPoint) encBool := by
  fun_prop

/-- Occupied nonvertex crossing sites can be selected in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_crossingSites :
    ComputableInPolyTime crossingSites encCNF encRoute := by
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun φ p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
      decide (2 ≤ ((paths φ).filter fun r => r.contains p).length))
    (computable_crossingCandidates.comp (SAT.computableInPolyTime_incidenceGraph encNat))
    computable_crossingPredicate
  change ComputableInPolyTime (fun φ =>
    selectDistinct
      (((SAT.incidenceGraph φ).crossingCandidates (SAT.incidenceGraph φ).canonicalPorts).filter
        fun p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
          decide (2 ≤ ((paths φ).filter fun r => r.contains p).length))
      (List.replicate
        ((((SAT.incidenceGraph φ).crossingCandidates (SAT.incidenceGraph φ).canonicalPorts).filter
          fun p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
            decide (2 ≤ ((paths φ).filter fun r => r.contains p).length)).length) true)) _ _
  simpa only [Function.comp_def, encCNF] using computable_distinctPoints.comp hf

/-- Looking up the path for a syntactic literal occurrence is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_occurrencePath :
    ComputableInPolyTime (fun p : CNF ℕ × Occurrence ℕ => occurrencePath p.1 p.2)
      (encPair encCNF (Cslib.Logic.PL.encOccurrence encNat)) encRoute :=
  ComputableInPolyTime.listGetDWithInput
    (computableInPolyTime_paths.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.idxOfWithInput
      ((Cslib.Logic.PL.computableInPolyTime_occurrences encNat).comp
        (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)) []

end Cslib.Complexity.SAT.PlanarCompile
