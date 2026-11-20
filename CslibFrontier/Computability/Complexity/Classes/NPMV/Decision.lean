/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NPMV.Machine
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Nondeterministic machines with decisive and inconclusive branches

A branch decides yes or no when it produces the corresponding one-bit payload. A branch
that produces no payload is inconclusive. On every input at least one branch is decisive,
and all decisive branches agree. This characterizes `NP ∩ coNP`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeNTM Turing.MultiTapeTM

/-- A language in `NP ∩ coNP` is exactly a language that one polynomial-time
nondeterministic machine decides with yes, no, and inconclusive branches. Each input
has the correct decisive payload, and no other payload. -/
theorem mem_NPInterCoNP_iff_computesDecisionRelation {α : Type} {enc : α ↪ List Bool}
    {A : Set α} :
    A ∈ NPInterCoNP enc ↔ ComputesRelationInPolyTime
      (fun a w => (a ∈ A ∧ w = [true]) ∨ (a ∉ A ∧ w = [false])) enc := by
  rw [← mem_NPMV_iff_computesRelationInPolyTime]
  let R := fun (a : α) (w : List Bool) =>
    (a ∈ A ∧ w = [true]) ∨ (a ∉ A ∧ w = [false])
  change A ∈ NPInterCoNP enc ↔ R ∈ NPMV enc
  constructor
  · rintro ⟨hYes, hNo⟩
    let input := encPair enc encBits
    let graphFor (b : Bool) (B : Set α) : Set (α × List Bool) :=
      {x | x.1 ∈ B ∧ x.2 = [b]}
    have hGraph (b : Bool) (B : Set α) (hB : B ∈ NP enc) : graphFor b B ∈ NP input := by
      have hproj : PolyTimeReducible input enc {x : α × List Bool | x.1 ∈ B} B :=
        ⟨Prod.fst, ComputableInPolyTime.fst enc encBits, fun _ => Iff.rfl⟩
      have htest := (ComputableInPolyTime.snd enc encBits).decide_eq'
        (ComputableInPolyTime.const [b])
      exact mem_NP_of_guard htest (hproj.mem_NP hB) fun x => by simp [graphFor, and_comm]
    refine ⟨⟨1, fun a w hw => ?_⟩, ?_⟩
    · rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    · exact union_mem_NP (hGraph true A hYes) (hGraph false Aᶜ (mem_coNP.mp hNo))
  · intro h
    have hGraph : {x : α × List Bool | R x.1 x.2} ∈ NP (encPair enc encBits) := h.2
    have hYes : PolyTimeReducible enc (encPair enc encBits) A {x | R x.1 x.2} :=
      ⟨fun a => (a, [true]), ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [true]),
        fun a => by simp [R]⟩
    have hNo : PolyTimeReducible enc (encPair enc encBits) Aᶜ {x | R x.1 x.2} :=
      ⟨fun a => (a, [false]), ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [false]),
        fun a => by simp [R]⟩
    exact ⟨hYes.mem_NP hGraph, mem_coNP.mpr (hNo.mem_NP hGraph)⟩

end Cslib.Complexity
