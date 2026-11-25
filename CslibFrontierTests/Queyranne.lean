/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Query.Submodular.Queyranne
import Mathlib.Basic.Real.Basic

/-!
# Tests for Queyranne's Symmetric Submodular Minimization Algorithm

Kernel-checked (`by decide`) finite witnesses covering:
1. Positive and negative instances of `IsSymmetric` and `IsSubmodular` (`symConcave` non-graph set
   function vs directed cut and supermodular `|S|²`).
2. Direct `queyranne` optimization on a symmetric submodular function that is not a pairwise graph
   cut, plus `IsQOrdering` and `pendentPair_le`.
3. Signed integer (`ℤ`, negative values) symmetric submodular minimization, plus polymorphic
   instantiation of `queyranne_cutWeight_spec` over `ℚ` and `ℝ`.
4. Agreement with `Cslib.WeightedCut.minCut` (`queyranne_minCut_eq`) on a 4-vertex multigraph and on
   a weighted 4-vertex hypergraph (`queyranne_hyperCutWeight_spec`) whose unique global minimum cut
   has size 2 rather than 1.
5. `FreeM (ValueQuery V β)` oracle agreement (`eval_queyranneQuery_oracleOf`) and exact query counts
   (`countQueries`) with duplicate vertices and degenerate inputs (`n = 0, 1`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Queyranne

open Cslib.Query Cslib.Algorithms.Lean.Submodular Cslib.WeightedCut

/-! ## Non-graph symmetric submodular function -/

/-- A symmetric submodular function on `Fin 4` taking value `5` on singletons and complements of
singletons, `6` on size-2 cuts, and `0` on `∅` and `Finset.univ`. No undirected 4-vertex graph cut
has all singleton cuts equal to `5` and all pair cuts equal to `6` (their sums would have to match).
-/
private def symConcave (S : Finset (Fin 4)) : ℕ :=
  if S.card = 0 ∨ S.card = 4 then 0
  else if S.card = 2 then 6
  else 5

private theorem symConcave_isSymmetric : IsSymmetric symConcave := by
  unfold IsSymmetric
  decide

private theorem symConcave_isSubmodular : IsSubmodular symConcave := by
  unfold IsSubmodular
  decide

example : (queyranne symConcave [0, 1, 2, 3]).val = 5 := by decide

example : IsNonTrivialCut (queyranne symConcave [0, 1, 2, 3]).cut := by
  unfold IsNonTrivialCut
  decide

/-- Exhaustive check: every non-trivial subset achieves `symConcave ≥ 5`. -/
example : ∀ C : Finset (Fin 4), IsNonTrivialCut C → 5 ≤ symConcave C := by
  intro C ⟨hCne, hCuniv⟩
  revert C hCne hCuniv
  decide

/-- Positive `IsQOrdering` witness `[0, 1, 2, 3]` and checked `pendentPair_le` separating `2` and
`3` on `{0, 2}`. -/
private theorem isQOrdering_symConcave : IsQOrdering symConcave [0, 1, 2, 3] := by
  refine ⟨by decide, by decide, ?_⟩
  refine ⟨by decide, ⟨by decide, ⟨by decide, ⟨by decide, trivial⟩⟩⟩⟩

example : IsQOrdering symConcave [0, 1, 2, 3] := isQOrdering_symConcave

example : symConcave {3} ≤ symConcave {0, 2} :=
  pendentPair_le symConcave_isSubmodular symConcave_isSymmetric
    (p := [0, 1]) (s := 2) (t := 3) isQOrdering_symConcave (by decide)

/-! ## Boundary checks: dropping symmetry or submodularity -/

/-- A directed cut weight is not symmetric on `Fin 2`. -/
private def dirCut (S : Finset (Fin 2)) : ℕ :=
  if 0 ∈ S ∧ 1 ∉ S then 1 else 0

example : ¬ IsSymmetric dirCut := by
  intro h
  have h0 := h {0}
  revert h0
  decide

/-- Quadratic cardinality `S.card ^ 2` fails submodularity on `Fin 2`. -/
example : ¬ IsSubmodular (fun S : Finset (Fin 2) => S.card * S.card) := by
  intro h
  have h01 := h {0} {1}
  revert h01
  decide

/-! ## Natural-number multigraph, signed `ℤ` values, and `ℚ`/`ℝ` Stoer–Wagner -/

private def symMat {n : ℕ} {β : Type} [Zero β] (f : Fin n → Fin n → β) : Fin n → Fin n → β :=
  fun i j => if i < j then f i j else if j < i then f j i else 0

private def G4N : Fin 4 → Fin 4 → ℕ := symMat fun i j =>
  match i.val, j.val with
  | 0, 1 => 3
  | 1, 2 => 1
  | 2, 3 => 4
  | 0, 3 => 2
  | _, _ => 0

private theorem G4N_multigraph : IsMultigraph G4N := by
  unfold IsMultigraph
  decide

example : (queyranne (cutWeight G4N) [0, 1, 2, 3]).val = 3 := by decide

example : minCut G4N = 3 :=
  (queyranne_minCut_eq G4N_multigraph (vs := [0, 1, 2, 3]) (by decide)
    (by decide)).symm.trans (by decide)

/-- A signed integer symmetric submodular function `f S = (symConcave S : ℤ) - 6` taking negative
values (`f ∅ = -6`, `f {0, 1} = 0`, global minimum over non-trivial cuts `= -1`). -/
private def signedSubmod (S : Finset (Fin 4)) : ℤ :=
  (symConcave S : ℤ) - 6

example : (queyranne signedSubmod [0, 1, 2, 3]).val = -1 := by decide

example :
    let res := queyranne signedSubmod [0, 1, 2, 3]
    IsNonTrivialCut res.cut ∧ res.val = signedSubmod res.cut ∧
      ∀ C : Finset (Fin 4), IsNonTrivialCut C → signedSubmod res.cut ≤ signedSubmod C :=
  queyranne_spec (by unfold IsSubmodular; decide) (by unfold IsSymmetric; decide)
    (by decide) (by decide)

/-- Polymorphic instantiation of `queyranne_cutWeight_spec` over `ℚ` and `ℝ`. -/
example (W : Fin 4 → Fin 4 → ℚ) (hWsym : ∀ u v, W u v = W v u) (hWnonneg : ∀ u v, 0 ≤ W u v) :
    let res := queyranne (cutWeight W) [0, 1, 2, 3]
    IsNonTrivialCut res.cut ∧ res.val = cutWeight W res.cut ∧
      ∀ C : Finset (Fin 4), IsNonTrivialCut C → cutWeight W res.cut ≤ cutWeight W C :=
  queyranne_cutWeight_spec hWsym hWnonneg (by decide) (by decide)

noncomputable example (W : Fin 4 → Fin 4 → ℝ) (hWsym : ∀ u v, W u v = W v u)
    (hWnonneg : ∀ u v, 0 ≤ W u v) :
    let res := queyranne (cutWeight W) [0, 1, 2, 3]
    IsNonTrivialCut res.cut ∧ res.val = cutWeight W res.cut ∧
      ∀ C : Finset (Fin 4), IsNonTrivialCut C → cutWeight W res.cut ≤ cutWeight W C :=
  queyranne_cutWeight_spec hWsym hWnonneg (by decide) (by decide)

/-! ## Weighted hypergraph global minimum cut -/

/-- 4-vertex hypergraph with hyperedges `{0, 1}` (weight `10`), `{2, 3}` (weight `10`), and a
3-vertex hyperedge `{0, 1, 2}` (weight `2`). Every singleton cut weighs at least `10`, while
`{0, 1}` cuts only `{0, 1, 2}` for global minimum hypercut `2`. -/
private def H4 : Finset (Finset (Fin 4)) := {{0, 1}, {2, 3}, {0, 1, 2}}

private def wH4 (e : Finset (Fin 4)) : ℕ :=
  if e = {0, 1, 2} then 2 else 10

example : (queyranne (hyperCutWeight H4 wH4) [0, 1, 2, 3]).val = 2 := by decide

example : ∀ C : Finset (Fin 4), IsNonTrivialCut C → 2 ≤ hyperCutWeight H4 wH4 C := by
  intro C ⟨hCne, hCuniv⟩
  revert C hCne hCuniv
  decide

example :
    let res := queyranne (hyperCutWeight H4 wH4) [0, 1, 2, 3]
    IsNonTrivialCut res.cut ∧ res.val = hyperCutWeight H4 wH4 res.cut ∧
      ∀ C : Finset (Fin 4), IsNonTrivialCut C → hyperCutWeight H4 wH4 res.cut ≤
        hyperCutWeight H4 wH4 C :=
  queyranne_hyperCutWeight_spec H4 (fun _ _ => Nat.zero_le _) (by decide) (by decide)

/-! ## Value-oracle `FreeM (ValueQuery V β)` evaluation and exact query counts -/

private def oracle4 : {ι : Type} → ValueQuery (Fin 4) ℕ ι → ι :=
  ValueQuery.oracleOf (hyperCutWeight H4 wH4)

/-- With `|vs.eraseDups| = 4` (even with duplicates), `queyranneQuery` matches `queyranne` and
performs `(4 * 5 * 6 + 6 - 48) / 6 = 13` value queries (`3 * 13 = 39 ≤ 64 = 4³`). -/
example : (queyranneQuery [0, 1, 0, 2, 3, 2]).eval oracle4 =
    queyranne (hyperCutWeight H4 wH4) [0, 1, 2, 3] := by decide

example : (queyranneQuery [0, 1, 0, 2, 3, 2]).countQueries oracle4 = 13 := by decide

example : (queyranneQuery ([] : List (Fin 4))).countQueries oracle4 = 1 := by decide

example : (queyranneQuery ([0] : List (Fin 4))).countQueries oracle4 = 1 := by decide

example : 3 * (queyranneQuery [0, 1, 0, 2, 3, 2]).countQueries oracle4 ≤
    ([0, 1, 0, 2, 3, 2] : List (Fin 4)).toFinset.card ^ 3 :=
  three_mul_countQueries_queyranneQuery_le oracle4 (by decide)

end CslibFrontierTests.Queyranne
