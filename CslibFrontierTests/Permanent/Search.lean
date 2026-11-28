/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.Permanent.Search

/-! Checked clients of the matching search relation and Goldreich Exercise 6.22. -/

set_option linter.privateModule false

namespace Cslib.Complexity

open Turing.MultiTapeTM BipartitePerfectMatching

-- The empty graph has an empty certificate; padding is not a second solution.
example : searchRel [] [] := by
  unfold searchRel
  decide
example : ¬ searchRel [] [false] := by
  unfold searchRel
  decide

-- Missing entries are false. Two explicit certificates for the complete 2-by-2 table
-- represent its two matchings, while an isolated vertex has no accepted certificate.
example : searchRel [[true], [false, true]] [true, false, false, true] := by
  unfold searchRel
  decide
example : searchRel [[true, true], [true, true]] [false, true, true, false] := by
  unfold searchRel
  decide
example : ¬ searchRel [[false]] [true] := by
  unfold searchRel
  decide

example : searchCount searchRel [[true, true], [true, true]] = 2 := by
  rw [searchCount_searchRel, bipartitePerfectMatchingCount_eq_zeroOnePermanent,
    zeroOnePermanent_eq_card]
  decide

-- A caller obtains a certified searcher without reconstructing the edge-list/matrix bridge.
example : ∃ f : List (List Bool) → Option (List Bool),
    ComputableInPolyTime f encBoolTable (encOption encBits) ∧
      (∃ w, f [[true], [false, true]] = some w ∧
        searchRel [[true], [false, true]] w) ∧ f [[false]] = none := by
  obtain ⟨_, f, hf, hsolve⟩ := searchRel_mem_FPSearch
  refine ⟨f, hf, ?_, ?_⟩
  · have hex : [[true], [false, true]] ∈ searchDomain searchRel :=
      ⟨[true, false, false, true], by unfold searchRel; decide⟩
    cases h : f [[true], [false, true]] with
    | none => exact (hsolve.notMem h hex).elim
    | some w => exact ⟨w, rfl, hsolve.rel h⟩
  · cases h : f [[false]] with
    | none => rfl
    | some w =>
      have hw := hsolve.rel h
      have hpos : 0 < acceptCount ZeroOnePermanent.verifier [[false]] (1 * 1) :=
        acceptCount_pos_iff.mpr ⟨w, hw⟩
      change 0 < acceptCount ZeroOnePermanent.verifier [[false]]
        (([[false]] : List (List Bool)).length * ([[false]] : List (List Bool)).length) at hpos
      rw [ZeroOnePermanent.acceptCount_verifier, zeroOnePermanent_eq_card] at hpos
      norm_num at hpos

-- The faithful 6.36(b) endpoint includes all three certificates for the same relation.
example : searchRel ∈ FNP encBoolTable ∧
    SharpPMetricComplete encBoolTable (searchCount searchRel) :=
  ⟨exercise_6_36b.1.1, exercise_6_36b.2.1⟩

-- Exercise 6.22(a): total domain is explicit, and completeness is metric.
example : ∃ R : List (List Bool) → List Bool → Prop, R ∈ FNP encBoolTable ∧
    searchDomain R = Set.univ ∧ SharpPMetricComplete encBoolTable (searchCount R) := by
  obtain ⟨R, hR, htotal, hcomplete⟩ := exists_mem_FPSearch_sharpPMetricComplete
  exact ⟨R, hR.1, isTotalSearch_iff_searchDomain_eq_univ.mp htotal, hcomplete⟩

-- Exercise 6.22(b) applies to arbitrary PC relations, not only complete counts.
example {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop} (hR : R ∈ FNP enc) :
    ∃ S : α → List Bool → Prop, S ∈ FPSearch enc ∧ IsTotalSearch S ∧
      ∀ a, searchCount S a = searchCount R a + 1 :=
  exists_mem_FPSearch_searchCount_add_one hR

end Cslib.Complexity
