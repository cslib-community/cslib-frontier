/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.WeightDimensions
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import Mathlib.Tactic.NormNum

/-! Checked native parameters for the generator and a nontrivial capacity threshold. -/

set_option linter.privateModule false

namespace CslibFrontierTests.JustesenParameters

open Cslib Cslib.Code.JustesenFamily Cslib.Reachability.Hoza Turing.MultiTapeTM

/-- A caller can compute both binary parameters needed by the degree and seed indices. -/
example :
    ComputableInSpace
      (fun p : ℕ × ℕ => (fieldDegree p.1 p.2, codeLength p.1 p.2))
      (encPair encNat encNat) (encPair encNat encNat)
      (fun p => (encPair encNat encNat p).length) :=
  ComputableInSpace.budget_prod fieldDegree_inSpace codeLength_inSpace

/-- The certified length is the seed index bound in the graph-wide isolation theorem. -/
example {w n : ℕ} (G : LayeredDigraph (Fin (n + 1) × Fin w))
    (hlayer : ∀ v, G.layer v = v.1.val) :
    ComputableInSpace (fun p : ℕ × ℕ => codeLength p.1 p.2) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) ∧
    ∃ seed : Fin (codeLength w n) → Bool, G.IsMinIsolating (generatedWeight seed) :=
  ⟨codeLength_inSpace, exists_generatedWeight_isMinIsolating G hlayer⟩

/-- The Horner caller can retain the selected modulus and coefficient count together. -/
example :
    ComputableInSpace
      (fun p : ℕ × ℕ => ((fieldContext p.1 p.2).modulus, (fieldContext p.1 p.2).count))
      (encPair encNat encNat) (encPair encBits encNat)
      (fun p => (encPair encNat encNat p).length) :=
  let hctx := fieldContext_inSpace
  ComputableInSpace.budget_prod (encFieldContext_modulus_budget hctx)
    (encFieldContext_count_budget hctx)

/-- At this input width the initial degree is too small, so the selected degree advances. -/
example : fieldDegree (2 ^ 1024) 0 = 32 ∧ coefficientCount (2 ^ 1024) 0 = 2 ^ 31 := by
  obtain ⟨s, -, hd, hpass, hsmall⟩ := fieldDegree_spec (2 ^ 1024) 0
  simp only [Nat.zero_add, mul_one, Nat.log2_two_pow] at hpass hsmall
  have hnonzero : 0 < s := by
    by_contra! h
    have hs : s = 0 := by omega
    subst s
    norm_num [dimension, scaleDegree] at hpass
  have hle : s ≤ 1 := by
    by_contra! h
    have hfirst := hsmall 1 h
    norm_num [dimension, scaleDegree] at hfirst
  have hd32 : fieldDegree (2 ^ 1024) 0 = 32 := by
    rw [hd, show s = 1 by omega]
    rfl
  exact ⟨hd32, by rw [coefficientCount_eq, hd32]⟩

open Turing QueryMachine SeedWeight.Dimensions in
/-- The native initializer supplies the original-input offset to the weight pass at layer one. -/
example (seed : Fin (codeLength 1 1) → Bool) :
    let x : Input := ⟨⟨1, 1, 1, 0⟩, List.ofFn seed⟩
    let start := load x
    let M := SeedWeight.machine start.inner
    ComputableInSpace load encInput (encLocated SeedWeight.Context SeedWeight.encContext)
      (fun r => (encHeader r.header).length) ∧
      (∀ t, M.withOffset.runFrom (encInput x) ⟨start.offset, M.init⟩ t =
        ⟨start.offset, M.run x.seed t⟩) ∧
      M.output x.seed (x.seed.length + 1) = encNat (generatedWeight seed (1, 0)) := by
  intro x start M
  refine ⟨load_inSpace, fun t => ?_, ?_⟩
  · rw [withOffset_runFrom, drop_seed]
    rfl
  · exact (SeedWeight.generatedWeight_output seed (1, 0)).2.2

open Turing SeedWeight.Dimensions in
/-- One native machine computes the weight from the raw input at layer one for every seed. -/
example :
    ∃ (time : Input → ℕ) (C k : ℕ) (State : Type) (_ : Finite State)
        (tm : MultiTapeTM k Bool State),
      ∀ seed : Fin (codeLength 1 1) → Bool,
        let x := canonicalInput seed (1, 0)
        let budget := C * ((encPair encNat encNat (1, 1)).length + 1)
        tm.ComputesInTimeAndSpace (encInput x) (encNat (generatedWeight seed (1, 0)))
          (time x) budget ∧
          (encNat (generatedWeight seed (1, 0))).length ≤ budget := by
  obtain ⟨time, C, k, State, hfinite, tm, h⟩ := generatedWeight_computesInTimeAndSpace
  exact ⟨time, C, k, State, hfinite, tm, fun seed => h (w := 1) (n := 1) seed (1, 0)⟩

end CslibFrontierTests.JustesenParameters
