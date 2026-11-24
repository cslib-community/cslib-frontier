/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.BoundedReduction
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Incidence
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Bandwidth

/-! Parallel edges, stable sorting with tied rows, and an actual accepted reduction image. -/

open Cslib.Complexity.NCL

private def parallelGraph : AndOrGraph :=
  ⟨[.or ⟨0, false⟩ ⟨1, false⟩ ⟨2, false⟩,
    .or ⟨0, true⟩ ⟨1, true⟩ ⟨2, true⟩], 3⟩

example : parallelGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

example : parallelGraph.checkBandwidth 1 [0, 1] = true := by decide +kernel

example : parallelGraph.checkBandwidth 0 [0, 1] = false := by decide +kernel

example : parallelGraph.checkBandwidth 1 [0, 0] = false := by decide +kernel

-- Undeclared ports are absent from the interpreted finite graph.
example : ({ parallelGraph with edgeCount := 0 } : AndOrGraph).checkBandwidth 0 [0, 1] = true := by
  decide +kernel

private def loopGraph : AndOrGraph :=
  ⟨[.or ⟨0, false⟩ ⟨0, true⟩ ⟨1, false⟩,
    .or ⟨1, true⟩ ⟨2, false⟩ ⟨2, true⟩], 3⟩

example : loopGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

example : loopGraph.checkBandwidth 1 [0, 1] = true := by decide +kernel

example : parallelGraph.graph.HasBandwidth 1 := by
  refine ⟨{ size := 2, order := Equiv.refl _, span := ?_ }⟩
  intro u v _ _ _ _ _
  have hu := u.isLt
  have hv := v.isLt
  simp only [Nat.dist]
  change u.val < 2 at hu
  change v.val < 2 at hv
  omega

example : ¬parallelGraph.graph.HasBandwidth 0 := by
  let G : ConstraintGraph (Fin 2) (Fin 3) := parallelGraph.graph
  change ¬G.HasBandwidth 0
  rintro ⟨C⟩
  have h := C.span 0 1 ⟨⟨0, false⟩, 2⟩ (by decide +kernel)
    ⟨⟨0, true⟩, 2⟩ (by decide +kernel) rfl
  have he : (C.order 0).val = (C.order 1).val := by
    simp only [Nat.dist] at h
    omega
  have hn : (0 : Fin 2) ≠ 1 := by decide +kernel
  exact hn (C.order.injective (Fin.ext he))

example : ConstraintGraph.RowOrder.indices [2, 0, 2, 1] = [1, 3, 0, 2] := by decide +kernel

private def compatibility : Digraph (Fin 2) := ⟨fun _ _ => True⟩

private instance : DecidableRel compatibility.Adj := fun _ _ => isTrue trivial

private def wordInput : HWord.Instance 2 := ⟨[0], [1]⟩

example : HWord.Planarized.reduceGraph compatibility (by decide +kernel) wordInput ∈
    BandwidthPlanarAndOrNCL (HWord.Planarized.layoutBound 2) := by
  apply (HWord.Planarized.reduceGraph_mem_iff compatibility (by decide +kernel) wordInput).mpr
  refine ⟨fun _ => 1, rfl, ?_, ?_⟩
  · intro _ _ _
    trivial
  · exact HWord.reachable_of_eq_off (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      ⟨0, by decide +kernel⟩
      (fun j hj => False.elim (hj (Fin.eq_zero j)))

-- Two-letter inputs exercise an actual forbidden-pair clause in the compiler.
private def restrictedCompatibility : Digraph (Fin 2) := ⟨fun a b => a = 0 ∨ b = 0⟩

private instance : DecidableRel restrictedCompatibility.Adj :=
  fun a b => inferInstanceAs (Decidable (a = 0 ∨ b = 0))

private def pairInput : HWord.Instance 2 := ⟨[0, 0], [1, 0]⟩

private def forbiddenPairInput : HWord.Instance 2 := ⟨[0, 0], [1, 1]⟩

example : HWord.Planarized.reduceGraph restrictedCompatibility (by decide +kernel) pairInput ∈
    BandwidthPlanarAndOrNCL (HWord.Planarized.layoutBound 2) := by
  rw [HWord.Planarized.reduceGraph_mem_iff]
  change HWord.Instance.mk (List.ofFn (fun _ : Fin 2 => (0 : Fin 2)))
    (List.ofFn (fun i : Fin 2 => if i = 0 then (1 : Fin 2) else 0)) ∈ _
  rw [HWord.language_ofFn]
  exact ⟨by decide +kernel, .single (by unfold HWord.Step; decide +kernel)⟩

example : HWord.Planarized.reduceGraph restrictedCompatibility (by decide +kernel)
    forbiddenPairInput ∉ BandwidthPlanarAndOrNCL (HWord.Planarized.layoutBound 2) := by
  rw [HWord.Planarized.reduceGraph_mem_iff]
  change HWord.Instance.mk (List.ofFn (fun _ : Fin 2 => (0 : Fin 2)))
    (List.ofFn (fun _ : Fin 2 => (1 : Fin 2))) ∉ _
  rw [HWord.language_ofFn]
  rintro ⟨hs, hr⟩
  exact (by decide +kernel : ¬HWord.Legal restrictedCompatibility (fun _ : Fin 2 => 1))
    (hr.legal hs)
