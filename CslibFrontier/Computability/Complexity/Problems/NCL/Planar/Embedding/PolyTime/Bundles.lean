/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Serialization
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Routing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Bundle
import Mathlib.Data.List.Zip
import Mathlib.Tactic.FinCases

/-!
# Exact source and cap instruction streams

Cubic source bundles create three stubs in port order. Cap bundles consume endpoint pairs
without creating further boundary wires, so every cap starts at the same offset.

## Main results

* `expand_sourceProgram`, `configurationBits_sourceProgram`: exact source emission.
* `expand_capProgram`, `configurationBits_capProgram`: exact cap emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram

/-- Read the three signals of one source cell from its incidence list. -/
@[expose] def sourceOpcode (ws : List Wire) : Opcode :=
  let a := ws.getD 0 default
  let b := ws.getD 1 default
  let c := ws.getD 2 default
  .source a.color b.color c.color a.bit b.bit c.bit

/-- Emit one three-output source per vertex, in vertex and port order. -/
@[expose] def sourceProgram (wss : List (List Wire)) (k : ℕ) : Program :=
  wss.zipIdx.map fun p => (k + 3 * p.2, sourceOpcode p.1)

private theorem sourceProgram_cons (ws : List Wire) (wss : List (List Wire)) (k : ℕ) :
    sourceProgram (ws :: wss) k = (k, sourceOpcode ws) :: sourceProgram wss (k + 3) := by
  simp only [sourceProgram, List.zipIdx_cons', List.map_cons, List.map_map,
    Nat.mul_zero, Nat.add_zero, List.cons.injEq, true_and]
  exact List.map_congr_left fun ⟨_, i⟩ _ => Prod.ext (by dsimp; omega) rfl

private theorem source_bits {Label : Type} (wire : Label → Wire) (p q r : Label) :
    labelledBits (Sources.one (fun a => (wire a).color) [p, q, r] 2).labeling
      (fun a => (wire a).bit) =
      (sourceOpcode [wire p, wire q, wire r]).configuration := by
  refine (congrArg (extendedBits (gen (.source [(wire p).color, (wire q).color,
      (wire r).color] 2))) (funext ?_)).trans
    (extendedBits_source _ _ _ ![(wire p).bit, (wire q).bit, (wire r).bit])
  rintro (i | i)
  · exact i.elim0
  · fin_cases i <;> rfl

/-- Source instructions are exactly the actual source bundle's primitive word. -/
theorem expand_sourceProgram {E : Type} (wire : Port E → Wire) (vs : List (Vertex E))
    (hs : ∀ v ∈ vs, v.ports.length = 3 ∧ v.minInflow = 2) (k : ℕ) :
    expand (sourceProgram (vs.map fun v => v.ports.map fun p => wire p.port) k) =
      (planarizeAlong Cell.expand
        (Sources.vertices (fun p => (wire p).color) vs).diagram).toWord Prim.interp k := by
  induction vs generalizing k with
  | nil => rfl
  | cons v vs ih =>
    rcases v with ⟨ps, need⟩
    obtain ⟨hl, rfl⟩ := hs _ (List.mem_cons_self ..)
    obtain ⟨p, q, r, rfl⟩ := List.length_eq_three.mp hl
    rw [List.map_cons, sourceProgram_cons, expand_cons,
      ih (fun w hw => hs w (List.mem_cons_of_mem _ hw))]
    rfl

/-- Source instructions serialize the exact canonical extension of the labeled source bundle. -/
theorem configurationBits_sourceProgram {E : Type} (wire : Port E → Wire)
    (vs : List (Vertex E)) (hs : ∀ v ∈ vs, v.ports.length = 3 ∧ v.minInflow = 2) (k : ℕ) :
    configurationBits (sourceProgram (vs.map fun v => v.ports.map fun p => wire p.port) k) =
      labelledBits (Sources.vertices (fun p => (wire p).color) vs).labeling
        (fun p => (wire p).bit) := by
  induction vs generalizing k with
  | nil => rfl
  | cons v vs ih =>
    rcases v with ⟨ps, need⟩
    obtain ⟨hl, rfl⟩ := hs _ (List.mem_cons_self ..)
    obtain ⟨p, q, r, rfl⟩ := List.length_eq_three.mp hl
    rw [List.map_cons, sourceProgram_cons, configurationBits_cons,
      ih (fun w hw => hs w (List.mem_cons_of_mem _ hw))]
    exact ((labelledBits_tensor _ _ _).trans
      (congrArg (· ++ _) (source_bits wire ..))).symm

/-- Emit one cap per listed edge, always at the same remaining-wire offset. -/
@[expose] def capProgram {E : Type} (color : E → Color) (u : Port E → Bool)
    (es : List E) (k : ℕ) : Program :=
  es.map fun e => (k, Opcode.cap (color e) (u ⟨e, false⟩) (u ⟨e, true⟩))

/-- Cap instructions are exactly the actual sink bundle's primitive word. -/
theorem expand_capProgram {E : Type} (color : E → Color) (u : Port E → Bool)
    (es : List E) (k : ℕ) :
    expand (capProgram color u es k) =
      (planarizeAlong Cell.expand (Sinks.caps color es).diagram).toWord Prim.interp k := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [capProgram, List.map_cons, expand_cons, ← capProgram, ih]
    rfl

private theorem cap_bits {Label : Type} (c : Color) (p q : Label) (u : Label → Bool) :
    labelledBits (Sinks.cap c p q).labeling u = (Opcode.cap c (u p) (u q)).configuration := by
  refine (congrArg (extendedBits (gen (.cap c))) (funext ?_)).trans
    (extendedBits_cap c ![u p, u q])
  rintro (i | i)
  · fin_cases i <;> rfl
  · exact i.elim0

/-- Cap instructions serialize the actual canonical cap extensions in edge order. -/
theorem configurationBits_capProgram {E : Type} (color : E → Color) (u : Port E → Bool)
    (es : List E) (k : ℕ) :
    configurationBits (capProgram color u es k) =
      labelledBits (Sinks.caps color es).labeling u := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [capProgram, List.map_cons, configurationBits_cons, ← capProgram, ih]
    exact ((labelledBits_tensor _ _ _).trans (congrArg (· ++ _) (cap_bits ..))).symm

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
