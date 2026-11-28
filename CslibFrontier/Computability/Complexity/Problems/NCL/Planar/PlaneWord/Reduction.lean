/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Planarized.Instances

/-!
# Public plane-word reductions and image invariants

Each plane-word problem exposes its canonical source reduction, polynomial-time bound and
correctness. The output specifications package the plane-word checks, graph validity, legal
configuration lengths and fixed decision-edge positions. A downstream reduction needs
correctness only on any invariant containing this source image.

## Main definitions

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.reduce` and its edge variants: public source maps.

## Main results

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.reduce_spec` and its edge variants: output invariants.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.pspaceHard_of_inv` and its edge variants:
  hardness transfer with an image invariant.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

open Diagram QBF _root_.Turing.MultiTapeTM

private theorem plane_properties (x : PrenexCNF) : (Planarized.word x).ValidPlane :=
  ⟨Planarized.checkPlane_word x, Planarized.wellTyped_word x,
    Planarized.graphData_valid x, Planarized.graphData_loopFree x⟩

private theorem canonical_properties (x : PrenexCNF)
    (R : Realization Prim.interp (Planarized.diagram x) [] []) :
    ((Planarized.diagram x).bits R.orient).length = (Planarized.graphData x).edgeCount ∧
      (Planarized.graphData x).graph.Legal
        ((Planarized.graphData x).config ((Planarized.diagram x).bits R.orient)) :=
  Diagram.compile_bits_legal Prim.interp (Planarized.diagram x)
    (Planarized.graphData_valid x) R.legal

/-- Transfer source hardness through a polynomial-time map correct on an image invariant. -/
theorem pspaceHard_of_source_inv {A B : Type} {encA : A ↪ List Bool}
    {encB : B ↪ List Bool} {L : Set A} {K : Set B}
    (f : PrenexCNF → A) (hf : ComputableInPolyTime f encPrenexCNF encA)
    (hL : ∀ x, f x ∈ L ↔ x ∈ TQBFCNF) (Inv : A → Prop) (hInv : ∀ x, Inv (f x))
    (g : A → B) (hg : ComputableInPolyTime g encA encB)
    (hcorrect : ∀ x, Inv x → (x ∈ L ↔ g x ∈ K)) : PSPACEHard encB K :=
  TQBFCNF_pspaceHard.trans ⟨g ∘ f, hg.comp hf,
    fun x => (hL x).symm.trans (hcorrect (f x) (hInv x))⟩

namespace PlaneWordAndOrNCL

/-- The reduced instance is a valid closed plane word with canonical legal configurations
and the designated edge positions required by this problem. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).word.ValidPlane ∧
      (reduce x).initial.length = (Word.compile (reduce x).word).edgeCount ∧
      (reduce x).target.length = (Word.compile (reduce x).word).edgeCount ∧
      (Word.compile (reduce x).word).graph.Legal
        ((Word.compile (reduce x).word).config (reduce x).initial) ∧
      (Word.compile (reduce x).word).graph.Legal
        ((Word.compile (reduce x).word).config (reduce x).target) := by
  have hi := canonical_properties x (Planarized.initial x)
  have ht := canonical_properties x (Planarized.target x)
  exact ⟨plane_properties x, hi.1, ht.1, hi.2, ht.2⟩

/-- Transfer PSPACE hardness using correctness on any invariant satisfied by the source image. -/
theorem pspaceHard_of_inv {B : Type} {encB : B ↪ List Bool} {K : Set B}
    (Inv : Instance → Prop) (hInv : ∀ x, Inv (reduce x))
    (g : Instance → B)
    (hg : ComputableInPolyTime g encPlaneWordAndOrNCL encB)
    (hcorrect : ∀ x, Inv x → (x ∈ PlaneWordAndOrNCL ↔ g x ∈ K)) : PSPACEHard encB K :=
  pspaceHard_of_source_inv reduce computableInPolyTime_reduce reduce_mem_iff Inv hInv g hg hcorrect

end PlaneWordAndOrNCL

namespace PlaneWordAndOrNCLEdge

/-- The reduced instance is a valid closed plane word with canonical legal configurations
and the designated edge positions required by this problem. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).word.ValidPlane ∧
      (reduce x).initial.length = (Word.compile (reduce x).word).edgeCount ∧
      (Word.compile (reduce x).word).graph.Legal
        ((Word.compile (reduce x).word).config (reduce x).initial) ∧
      (reduce x).edge = 4 ∧ (reduce x).edge < (Word.compile (reduce x).word).edgeCount := by
  have hi := canonical_properties x (Planarized.initial x)
  refine ⟨plane_properties x, hi.1, hi.2, Planarized.num_output x, ?_⟩
  exact Diagram.num_lt_compile Prim.interp _ (Planarized.output x)

/-- Transfer PSPACE hardness using correctness on any invariant satisfied by the source image. -/
theorem pspaceHard_of_inv {B : Type} {encB : B ↪ List Bool} {K : Set B}
    (Inv : Instance → Prop) (hInv : ∀ x, Inv (reduce x))
    (g : Instance → B)
    (hg : ComputableInPolyTime g encPlaneWordAndOrNCLEdge encB)
    (hcorrect : ∀ x, Inv x → (x ∈ PlaneWordAndOrNCLEdge ↔ g x ∈ K)) : PSPACEHard encB K :=
  pspaceHard_of_source_inv reduce computableInPolyTime_reduce reduce_mem_iff Inv hInv g hg hcorrect

end PlaneWordAndOrNCLEdge

namespace PlaneWordAndOrNCLEdgeToEdge

/-- The reduced instance is a valid closed plane word with canonical legal configurations
and the designated edge positions required by this problem. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).word.ValidPlane ∧ (reduce x).first = ⟨6, false⟩ ∧
      (reduce x).second = ⟨0, false⟩ ∧
      (reduce x).first.edge < (Word.compile (reduce x).word).edgeCount ∧
      (reduce x).second.edge < (Word.compile (reduce x).word).edgeCount := by
  refine ⟨plane_properties x, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun e => (⟨e, false⟩ : Port ℕ)) (Planarized.num_tryIn x)
  · exact congrArg (fun e => (⟨e, false⟩ : Port ℕ)) (Planarized.num_satOut x)
  · exact Diagram.num_lt_compile Prim.interp _ (Planarized.tryIn x)
  · exact Diagram.num_lt_compile Prim.interp _ (Planarized.satOut x)

/-- Transfer PSPACE hardness using correctness on any invariant satisfied by the source image. -/
theorem pspaceHard_of_inv {B : Type} {encB : B ↪ List Bool} {K : Set B}
    (Inv : Instance → Prop) (hInv : ∀ x, Inv (reduce x))
    (g : Instance → B)
    (hg : ComputableInPolyTime g encPlaneWordAndOrNCLEdgeToEdge encB)
    (hcorrect : ∀ x, Inv x → (x ∈ PlaneWordAndOrNCLEdgeToEdge ↔ g x ∈ K)) : PSPACEHard encB K :=
  pspaceHard_of_source_inv reduce computableInPolyTime_reduce reduce_mem_iff Inv hInv g hg hcorrect

end PlaneWordAndOrNCLEdgeToEdge

end Cslib.Complexity.NCL
