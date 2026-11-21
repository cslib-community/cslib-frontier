/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
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
example (hmodulus : ComputableInSpace BinaryField.modulusBitsScan encNat encBits (fun d => d + 1)) :
    ComputableInSpace
      (fun p : ℕ × ℕ => ((fieldContext p.1 p.2).modulus, (fieldContext p.1 p.2).count))
      (encPair encNat encNat) (encPair encBits encNat)
      (fun p => (encPair encNat encNat p).length) :=
  let hctx := fieldContext_inSpace_of_modulus hmodulus
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

end CslibFrontierTests.JustesenParameters
