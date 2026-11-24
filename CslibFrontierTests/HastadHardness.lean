/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.Hastad.Hardness
import Mathlib.Tactic.NormNum

/-!
# Checked tests for Håstad's MAX-E3LIN-2 and MAX-E3SAT NP-hardness

Exercises the subtle model boundaries and non-vacuity of the folded Long Code reduction and the
resulting gap problems:

* a computable `Tables Bool Bool 3` witness verifying `Tables.Valid`, degenerate-equation dropping
  (`108` emitted distinct-variable equations out of `4 * 9 * 4 = 144` raw triples), and folding
  oddness (`isOdd_decodeRight`);
* the edgeless-graph boundary (`reduce T ⟨0, []⟩ = [trivialEq]`) and the empty-system boundary
  between `GapExactThreeLin` and `GapLin` (`[] ∉ (GapLin ...).yes` while
  `toGapLin [] ∈ (GapLin ...).yes`);
* explicit yes- and no-instances for `GapExactThreeLin (9 / 10) (3 / 5)` and
  `GapMaxExactThreeSAT (31 / 32) (29 / 32)` (meeting the exact `1 / 2` and `7 / 8` boundaries);
* concrete instantiations of `GapExactThreeLin_npHard`, `GapLin_npHard_of_lt`,
  `GapMaxExactThreeSAT_npHard`, `P_eq_NP_of_maxExactThreeLin_approx`, and
  `P_eq_NP_of_maxExactThreeSAT_approx`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.HastadHardness

open Cslib.BitString Cslib.Complexity Cslib.Logic.PL Cslib.PCP.Encoded Cslib.PCP.Hastad.Reduction
  Turing.MultiTapeTM

/-! ### Concrete computable `Tables Bool Bool 3` and boundary checks -/

private def boolFunIdx (f : Bool → Bool) : ℕ :=
  (f false).toNat + 2 * (f true).toNat

private theorem boolFunIdx_injective : Function.Injective boolFunIdx := by
  intro f g h
  funext b
  cases hf0 : f false <;> cases hf1 : f true <;> cases hg0 : g false <;> cases hg1 : g true <;>
    simp [boolFunIdx, hf0, hf1, hg0, hg1] at h ⊢ <;> cases b <;> simp [hf0, hf1, hg0, hg1]

private def allBoolFuns : List (Bool → Bool) :=
  [fun _ => false, fun b => b, fun b => !b, fun _ => true]

private def allFin3Funs : List (Bool → Fin 3) :=
  let digits : List (Fin 3) := [0, 1, 2]
  digits.flatMap fun a => digits.map fun b => fun x => if x then b else a

private def boolTables : Tables Bool Bool 3 where
  pivot := false
  rightIdx := boolFunIdx
  leftIdx := boolFunIdx
  rightQueries := allBoolFuns
  leftQueries := allBoolFuns
  noiseDigits := allFin3Funs

private theorem mem_allBoolFuns (f : Bool → Bool) : f ∈ allBoolFuns := by
  cases hf0 : f false <;> cases hf1 : f true
  · have h : f = fun _ => false := by funext b; cases b <;> simp [hf0, hf1]
    subst h; simp [allBoolFuns]
  · have h : f = fun b => b := by funext b; cases b <;> simp [hf0, hf1]
    subst h; simp [allBoolFuns]
  · have h : f = fun b => !b := by funext b; cases b <;> simp [hf0, hf1]
    subst h; simp [allBoolFuns]
  · have h : f = fun _ => true := by funext b; cases b <;> simp [hf0, hf1]
    subst h; simp [allBoolFuns]

private theorem nodup_allBoolFuns : allBoolFuns.Nodup := by
  simp only [allBoolFuns, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h
  · exact Bool.false_ne_true (congrFun h true)
  · exact Bool.false_ne_true (congrFun h false)
  · exact Bool.false_ne_true (congrFun h false)
  · exact Bool.false_ne_true (congrFun h false)
  · exact Bool.false_ne_true (congrFun h false)
  · exact Bool.false_ne_true (congrFun h true)

private theorem mem_allFin3Funs (r : Bool → Fin 3) : r ∈ allFin3Funs := by
  have hfin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  simp only [allFin3Funs, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false]
  refine ⟨r false, hfin3 _, r true, hfin3 _, ?_⟩
  funext b; cases b <;> rfl

private theorem nodup_allFin3Funs : allFin3Funs.Nodup := by
  have hinj :
      ∀ a : Fin 3, Function.Injective (fun b : Fin 3 => fun x : Bool => if x then b else a) :=
    fun a b₁ b₂ h => by simpa using congrFun h true
  refine List.nodup_flatMap.2
    ⟨fun a _ => (by decide : ([0, 1, 2] : List (Fin 3)).Nodup).map (hinj a), ?_⟩
  refine List.Pairwise.imp (fun {a₁ a₂} hne => ?_) (by decide : ([0, 1, 2] : List (Fin 3)).Nodup)
  intro f hf₁ hf₂
  obtain ⟨b₁, _, rfl⟩ := List.mem_map.1 hf₁
  obtain ⟨b₂, _, heq⟩ := List.mem_map.1 hf₂
  exact hne (by simpa using (congrFun heq false).symm)

private theorem valid_boolTables : boolTables.Valid where
  rightIdx_injective := boolFunIdx_injective
  leftIdx_injective := boolFunIdx_injective
  rightQueries_nodup := nodup_allBoolFuns
  mem_rightQueries := mem_allBoolFuns
  leftQueries_nodup := nodup_allBoolFuns
  mem_leftQueries := mem_allBoolFuns
  noiseDigits_nodup := nodup_allFin3Funs
  mem_noiseDigits := mem_allFin3Funs

/-- Edgeless Label Cover graphs map to `[trivialEq]` (nonempty, distinct three-variable scope). -/
example : reduce boolTables ⟨0, []⟩ = [trivialEq] :=
  reduce_of_edges_nil boolTables rfl

/-- On a 1-edge identity graph over `Bool → Bool` with `m = 3`, `9` of the `4 * 9 = 36` pairs
`(f, r)` satisfy `f ∘ id = noiseMask r`, dropping `36` of the `144` raw triples and leaving
exactly `108` distinct-variable parity equations. -/
example : (reduce boolTables ⟨1, [⟨0, 0, id⟩]⟩).length = 108 := by decide

/-- Every equation emitted on the 1-edge graph has three distinct variables. -/
example : ∀ c ∈ reduce boolTables ⟨1, [⟨0, 0, id⟩]⟩, c.scope.length = 3 ∧ c.scope.Nodup :=
  scopes_reduce valid_boolTables ⟨1, [⟨0, 0, id⟩]⟩

/-- Decoded right tables are odd for every assignment. -/
example (σ : ℕ → Bool) (w : ℕ) : IsOdd (decodeRight boolTables σ w) :=
  isOdd_decodeRight boolTables σ w

/-! ### Non-vacuity and empty-system boundary witnesses -/

/-- A single satisfiable parity equation on three distinct variables. -/
private def oneSatEq : CSP Bool ℕ := [⟨false, [0, 1, 2]⟩]

/-- Two opposite parity equations on the same three distinct variables: every assignment satisfies
exactly one of the two, achieving value `1 / 2` (and `7 / 8` after the four-clause gadget). -/
private def inconsistentPair : CSP Bool ℕ := [⟨false, [0, 1, 2]⟩, ⟨true, [0, 1, 2]⟩]

private theorem unsatVal_inconsistentPair :
    inconsistentPair.unsatVal CSP.paritySem = 1 / 2 := by
  have hcount (σ : ℕ → Bool) :
      inconsistentPair.countP (fun c => !Constraint.eval CSP.paritySem σ c) = 1 := by
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
      simp [inconsistentPair, Constraint.eval, CSP.paritySem, h0, h1, h2]
  have hlen : inconsistentPair.length = 2 := rfl
  refine le_antisymm ?_ ((CSP.le_unsatVal_iff CSP.paritySem inconsistentPair).2 fun σ => ?_)
  · simpa [hcount, hlen] using CSP.unsatVal_le CSP.paritySem inconsistentPair (fun _ => false)
  · simp [hcount, hlen]

/-- Concrete yes-instance of `GapExactThreeLin (9 / 10) (3 / 5)`. -/
example : oneSatEq ∈ (GapExactThreeLin (9 / 10) (3 / 5)).yes := by
  rw [mem_yes_GapExactThreeLin]
  refine ⟨by decide, ?_⟩
  have hsat : CSP.Satisfiable CSP.paritySem oneSatEq := ⟨fun _ => false, by decide⟩
  rw [(CSP.unsatVal_eq_zero_iff CSP.paritySem oneSatEq).2 hsat]
  norm_num

/-- Concrete no-instance of `GapExactThreeLin (9 / 10) (3 / 5)`. -/
example : inconsistentPair ∈ (GapExactThreeLin (9 / 10) (3 / 5)).no := by
  rw [mem_no_GapExactThreeLin (by norm_num)]
  refine ⟨by decide, ?_⟩
  rw [unsatVal_inconsistentPair]
  norm_num

/-- Empty-system boundary between `GapExactThreeLin` and `GapLin`: the empty `XORSAT.System` has
satisfied proportion `0 / 0 = 0`, so it is not a yes-instance of `GapLin (9 / 10) (3 / 5)`,
whereas `toGapLin []` maps the empty `CSP Bool ℕ` yes-instance to a nonempty yes-instance. -/
example : ([] : XORSAT.System) ∉ (GapLin (9 / 10) (3 / 5)).yes := by
  rw [mem_yes_GapLin]
  rintro ⟨_, h⟩
  norm_num at h

example : toGapLin [] ∈ (GapLin (9 / 10) (3 / 5)).yes := by
  rw [mem_yes_GapLin]
  refine ⟨fun _ => false, ?_⟩
  have hsat : AffineSystem.countSat (toGapLin []) (fun _ => false) = 1 := rfl
  have hlen : (toGapLin []).length = 1 := rfl
  rw [hsat, hlen]
  norm_num

/-- Quarter-factor value transfer on `inconsistentPair`: `unsatVal` goes from `1 / 2` to `1 / 8`. -/
example : (inconsistentPair.toCNFBounded 3 CSP.paritySem).unsatVal = 1 / 8 := by
  rw [CSP.unsatVal_toCNFBounded_parity (by decide), unsatVal_inconsistentPair]
  norm_num

/-- Concrete yes-instance of `GapMaxExactThreeSAT (31 / 32) (29 / 32)`. -/
example :
    oneSatEq.toCNFBounded 3 CSP.paritySem ∈ (GapMaxExactThreeSAT (31 / 32) (29 / 32)).yes := by
  rw [mem_yes_GapMaxExactThreeSAT]
  refine ⟨CSP.isExactThreeDistinct_toCNFBounded_parity (by decide), ?_⟩
  rw [CSP.unsatVal_toCNFBounded_parity (by decide)]
  have hsat : CSP.Satisfiable CSP.paritySem oneSatEq := ⟨fun _ => false, by decide⟩
  rw [(CSP.unsatVal_eq_zero_iff CSP.paritySem oneSatEq).2 hsat]
  norm_num

/-- Concrete no-instance of `GapMaxExactThreeSAT (31 / 32) (29 / 32)`, achieving value `7 / 8`. -/
example :
    inconsistentPair.toCNFBounded 3 CSP.paritySem ∈
      (GapMaxExactThreeSAT (31 / 32) (29 / 32)).no := by
  rw [mem_no_GapMaxExactThreeSAT (by norm_num)]
  refine ⟨CSP.isExactThreeDistinct_toCNFBounded_parity (by decide), ?_⟩
  rw [CSP.unsatVal_toCNFBounded_parity (by decide), unsatVal_inconsistentPair]
  norm_num

/-! ### Concrete instantiations of the headline hardness theorems -/

/-- Håstad Theorem 5.4 (gap form) at `δ = ε = 1 / 10`. -/
example : PromiseProblem.NPHard (encCSP encBool encNat) (GapExactThreeLin (9 / 10) (3 / 5)) := by
  simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num,
    show (1 : ℝ) / 2 + 1 / 10 = 3 / 5 by norm_num] using
    GapExactThreeLin_npHard (δ := 1 / 10) (ε := 1 / 10) (by norm_num) (by norm_num) (by norm_num)

/-- Goldreich Theorem 10.9 (`GapLin`) at `δ = ε = 1 / 10`. -/
example : PromiseProblem.NPHard XORSAT.encoding (GapLin (9 / 10) (3 / 5)) := by
  simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num,
    show (1 : ℝ) / 2 + 1 / 10 = 3 / 5 by norm_num] using
    GapLin_npHard_of_lt (δ := 1 / 10) (ε := 1 / 10) (by norm_num) (by norm_num) (by norm_num)

/-- Håstad Theorem 6.1 (imperfect completeness, distinct variables) at `δ = ε = 1 / 32`. -/
example : PromiseProblem.NPHard encCNF (GapMaxExactThreeSAT (31 / 32) (29 / 32)) := by
  simpa only [show (1 : ℝ) - 1 / 32 = 31 / 32 by norm_num,
    show (7 : ℝ) / 8 + 1 / 32 = 29 / 32 by norm_num] using
    GapMaxExactThreeSAT_npHard (δ := 1 / 32) (ε := 1 / 32)
      (by norm_num) (by norm_num) (by norm_num)

/-- Håstad Theorem 5.4 (approximation-ratio form): a `3 / 5`-approximation for MAX-E3LIN-2 gives
`P = NP`. -/
example {A : CSP Bool ℕ → List ℕ}
    (hA : ComputableInPolyTime A (encCSP encBool encNat) (encList encNat))
    (happrox : ∀ F : CSP Bool ℕ, (∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup) →
      (3 / 5 : ℝ) * (1 - F.unsatVal CSP.paritySem) * F.length ≤
        F.length - F.countP (fun e => !Constraint.eval CSP.paritySem
          (fun v => decide (v ∈ A F)) e)) :
    P encCNF = NP encCNF :=
  P_eq_NP_of_maxExactThreeLin_approx (ρ := 3 / 5) (by norm_num) hA happrox encCNF

/-- Håstad Theorem 6.1 (approximation-ratio form): a `15 / 16`-approximation for distinct-variable
MAX-E3SAT gives `P = NP`. -/
example {A : CNF ℕ → List ℕ}
    (hA : ComputableInPolyTime A encCNF (encList encNat))
    (happrox : ∀ φ : CNF ℕ, φ.IsExactThreeDistinct →
      (15 / 16 : ℝ) * (1 - φ.unsatVal) * φ.length ≤
        φ.length - φ.countUnsat (fun v => decide (v ∈ A φ))) :
    P encCNF = NP encCNF :=
  P_eq_NP_of_maxExactThreeSAT_approx (ρ := 15 / 16) (by norm_num) hA happrox encCNF

end CslibFrontierTests.HastadHardness
