/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Routing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Crossover
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Generator

/-!
# Planarizing a supplied diagram

First route each swap through its two wire relations, then replace each crossing by the
certified planar AND/OR crossover for its colors. Source generators are replaced by a supplied
open implementation. The resulting simulation preserves all reachability questions.

## Main definitions

* `Cslib.Complexity.NCL.Planar.planarizeAlong`: the diagram transformation.
* `Cslib.Complexity.NCL.Planar.planarizeAlongSimulation`: its simulation for forward generators.

## Main results

* `Cslib.Complexity.NCL.Planar.planarizeAlong_planar`: planar source cells give a planar result.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Routed

open Diagram
variable {Γ : List Color → List Color → Type} {I : Interp Γ}

/-- Implement source generators by `H` and crossing relations by certified crossovers. -/
@[expose] def expand (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) :
    {a b : List Color} → Routed Γ a b → Diagram Prim a b
  | _, _, .base g => H g
  | _, _, .cross c d => Crossover.diagram c d

/-- Every routed generator has an open implementation over primitive diagrams. -/
@[expose] def expandOpenSim {H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), OpenSim I Prim.interp (gen g) (H g))
    {a b : List Color} (g : Routed Γ a b) :
    OpenSim (interp I) Prim.interp (gen g) (expand H g) := by
  cases g with
  | base g =>
    exact (OpenSim.genOfVerts (I := interp I) (I' := I) (Routed.base g) g rfl).trans (hH g)
  | cross c d => exact (OpenSim.genOfVerts (I := interp I) (I' := Prim.interp) (Routed.cross c d)
      (Prim.cross c d) rfl).trans (Crossover.openSim c d)

end Cslib.Complexity.NCL.Planar.Routed

namespace Cslib.Complexity.NCL.Planar

open Diagram
variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color}

/-- Route all swaps, then substitute the supplied planar source cells and the crossover family. -/
@[expose] def planarizeAlong (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b)
    (D : Diagram Γ a b) : Diagram Prim a b :=
  (Route.diagram D).subst (Routed.expand H)

/-- Planar source cells and the crossover family give a planar whole drawing. -/
theorem planarizeAlong_planar {H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), (H g).Planar) (D : Diagram Γ a b) :
    (planarizeAlong H D).Planar :=
  Planar.subst (H := Routed.expand H) (fun | .base g => hH g | .cross c d => Crossover.planar c d)
    (Route.planar D)

/-- Routing and open substitution compose into a whole-diagram reachability simulation. -/
@[expose] def planarizeAlongSimulation (hI : I.Forward)
    {H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), OpenSim I Prim.interp (gen g) (H g))
    (D : Diagram Γ a b) :
    ConstraintGraph.Simulation (D.graph I) ((planarizeAlong H D).graph Prim.interp) :=
  (Route.simulation hI D).trans (substSimulation (Routed.expandOpenSim hH) (Route.diagram D))

/-- Track an original edge through routing and open substitution. -/
@[expose] def planarizeAlongEdge
    {H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), OpenSim I Prim.interp (gen g) (H g))
    (D : Diagram Γ a b) (e : D.Edge) : (planarizeAlong H D).Edge :=
  (openSimSubst (Routed.expandOpenSim hH) (Route.diagram D)).ι (Route.original D e)

/-- Abstraction reads exactly the tracked edge. -/
theorem planarizeAlongSimulation_abs (hI : I.Forward)
    {H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), OpenSim I Prim.interp (gen g) (H g))
    (D : Diagram Γ a b) (t : (planarizeAlong H D).Edge → Bool) (e : D.Edge) :
    (planarizeAlongSimulation hI hH D).abs t e = t (planarizeAlongEdge hH D e) := rfl

private theorem planarizeAlong_gen
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) (g : Γ a b) :
    planarizeAlong H (gen g) = H g := rfl

private theorem planarizeAlong_id (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b)
    (a : List Color) : planarizeAlong H (Diagram.id a) = Diagram.id a := rfl

private theorem planarizeAlong_swap (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b)
    (c d : Color) : planarizeAlong H (swap c d) = Crossover.diagram c d := rfl

private theorem planarizeAlong_comp (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b)
    (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) :
    planarizeAlong H (D₁.comp D₂) = (planarizeAlong H D₁).comp (planarizeAlong H D₂) := rfl

private theorem planarizeAlong_tensor (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b)
    (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d) :
    planarizeAlong H (D₁.tensor D₂) = (planarizeAlong H D₁).tensor (planarizeAlong H D₂) := rfl

/-- Local checks of source cells suffice after each crossover passes the same check. -/
theorem checkGens_planarizeAlong (test : ∀ {a b : List Color}, Prim a b → Bool)
    (hc : ∀ c d, (Crossover.diagram c d).checkGens test = true)
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) (D : Diagram Γ a b) :
    (planarizeAlong H D).checkGens test = D.checkGens (fun g => (H g).checkGens test) := by
  induction D with
  | gen _ => exact congrArg (checkGens test) (planarizeAlong_gen H _)
  | id a => exact congrArg (checkGens test) (planarizeAlong_id H a)
  | swap c d => exact (congrArg (checkGens test) (planarizeAlong_swap H c d)).trans (hc c d)
  | comp D₁ D₂ ih₁ ih₂ => simp only [planarizeAlong_comp, checkGens, ih₁, ih₂]
  | tensor D₁ D₂ ih₁ ih₂ => simp only [planarizeAlong_tensor, checkGens, ih₁, ih₂]

private theorem measure_planarizeAlong_le
    (μ : {a b : List Color} → Diagram Prim a b → ℕ) (k : ℕ)
    (hcomp : ∀ {a b c} (D₁ : Diagram Prim a b) (D₂ : Diagram Prim b c),
      μ (D₁.comp D₂) = μ D₁ + μ D₂)
    (htensor : ∀ {a b c d} (D₁ : Diagram Prim a b) (D₂ : Diagram Prim c d),
      μ (D₁.tensor D₂) = μ D₁ + μ D₂)
    (hc : ∀ c d, μ (Crossover.diagram c d) ≤ k)
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) (D : Diagram Γ a b) :
    μ (planarizeAlong H D) ≤ μ (D.subst H) + k * Diagram.swapCount D := by
  induction D with
  | gen _ | id _ => simp [planarizeAlong_gen, planarizeAlong_id, subst, Diagram.swapCount]
  | swap c d =>
    have := hc c d
    simp only [planarizeAlong_swap, subst, Diagram.swapCount, Nat.mul_one]; omega
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [planarizeAlong_comp, planarizeAlong_tensor, subst, hcomp, htensor,
      Diagram.swapCount, Nat.mul_add] at ih₁ ih₂ ⊢
    omega

/-- Planarization adds at most 286 vertices per syntactic crossing. -/
theorem length_vertexList_planarizeAlong_le
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) (D : Diagram Γ a b) :
    (vertexList Prim.interp (planarizeAlong H D)).length ≤
      (vertexList Prim.interp (D.subst H)).length + 286 * Diagram.swapCount D :=
  measure_planarizeAlong_le (fun D => (vertexList Prim.interp D).length) 286
    (length_vertexList_comp Prim.interp) (length_vertexList_tensor Prim.interp)
    Crossover.length_vertexList_le H D

/-- Planarization creates at most 429 additional wires per syntactic crossing. -/
theorem innerCount_planarizeAlong_le
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) (D : Diagram Γ a b) :
    (planarizeAlong H D).innerCount ≤ (D.subst H).innerCount + 429 * Diagram.swapCount D :=
  measure_planarizeAlong_le innerCount 429 (fun _ _ => rfl) (fun _ _ => rfl)
    Crossover.innerCount_le H D

end Cslib.Complexity.NCL.Planar
