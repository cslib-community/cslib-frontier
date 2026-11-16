/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (source-correspondence tests)

import CslibFrontier.Computability.Complexity.Problems.Halting
import CslibFrontier.Computability.Complexity.Problems.Permanent.SharpSAT
import CslibFrontier.Computability.Complexity.Problems.SharpCycle
import CslibFrontier.Computability.Complexity.Classes.PH.Complete
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Short exercise bridges

AB locators use the 2007-01-08 web draft. Goldreich Exercise 2.33 uses `r1.pdf`, December
2006, printed p. 113 / PDF p. 138. Its existential witnesses below are SAT, represented by CNFs.
Class equalities quantify over explicit instance encodings as required by the completeness API.
-/

-- This module intentionally contains only checked clients.
set_option linter.privateModule false

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

-- AB 7 §10, printed p. 134 / PDF p. 150: symmetry turns row stochasticity into
-- column stochasticity. Mathlib's existing norm bound even drops symmetry once both are given.
open scoped Matrix.Norms.L2Operator in
example {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hs : M.IsSymm) (hM : M ∈ Matrix.rowStochastic ℝ n) : ‖M‖ ≤ 1 := by
  apply Matrix.l2_opNorm_le_one_of_mem_doublyStochastic
  refine mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic.mpr ⟨hM, ?_⟩
  rw [← hs]
  exact Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic.mpr hM

-- AB 2 §3: hardness does not imply completeness.
example : ¬ NPComplete (encPair encBits encBits) haltingProblem :=
  fun h => haltingProblem_notMem_NP h.1

-- Goldreich 2.33(1): SAT is the promised witness in NP \ P, and it reduces to its complement.
example (h : ∀ {α : Type} (enc : α ↪ List Bool), NP enc = coNP enc)
    (hne : ¬ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc) :
    ∃ S : Set (CNF ℕ), S ∈ NP encCNF ∧ S ∉ P encCNF ∧
      PolyTimeReducible encCNF encCNF S Sᶜ := by
  refine ⟨SAT, CookLevin.SAT_npComplete.1, ?_, ?_⟩
  · exact fun hp => hne (CookLevin.SAT_npComplete.mem_P_iff.mp hp)
  · exact ((CookLevin.SAT_npComplete.NP_eq_coNP_iff_reducible
      CookLevin.SAT_npComplete.compl).mp h).1

-- Goldreich 2.33(2): failure of NP = coNP prevents both SAT ∈ P and SAT ≤p coSAT.
example (hne : ¬ ∀ {α : Type} (enc : α ↪ List Bool), NP enc = coNP enc) :
    ∃ S : Set (CNF ℕ), S ∈ NP encCNF ∧ S ∉ P encCNF ∧
      ¬ PolyTimeReducible encCNF encCNF S Sᶜ := by
  refine ⟨SAT, CookLevin.SAT_npComplete.1, ?_, ?_⟩
  · intro hp
    have h : ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
      CookLevin.SAT_npComplete.mem_P_iff.mp hp
    apply hne
    intro α enc
    apply Set.Subset.antisymm
    · intro A hA
      exact P_subset_coNP ((h enc).symm ▸ hA)
    · intro A hA
      have hc : Aᶜ ∈ P enc := (h enc).symm ▸ hA
      simpa only [compl_compl] using P_subset_NP (compl_mem_P hc)
  · exact fun hr => hne (fun enc =>
      CookLevin.SAT_npComplete.NP_eq_coNP_of_reducible_compl hr (enc := enc))

-- The approximation endpoint also rules out a factor-two counter when P differs from NP.
example {α : Type} (enc : α ↪ List Bool) (hne : P enc ≠ NP enc) :
    ¬ ∃ A : Graph → ℕ, ComputableInPolyTime A encGraph encNat ∧
      (∀ G, SharpCycle G ≤ 2 * A G) ∧ (∀ G, A G ≤ 2 * SharpCycle G) := by
  rintro ⟨A, hA, hlo, hhi⟩
  exact hne (P_eq_NP_of_polyTime_approx_SharpCycle hA hlo hhi enc)

-- Compose the signed permanent endpoint with a caller-side polynomial-time preprocessing map.
example {α : Type} (enc : α ↪ List Bool) (f : α → List (List ℤ))
    (hf : ComputableInPolyTime f enc encIntTable) :
    ComputableInPolyTimeWithOracle (bitGraph encCNF SharpSAT) (IntPermanent ∘ f)
      enc encIntBin := by
  exact intPermanent_computableInPolyTimeWithOracle_SharpSAT.preprocess hf
