/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.IndependentSet
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Checked client: FGLSS every-constant Independent Set and Clique hardness

Ordinary-import `module` client for the FGLSS reduction and every-constant inapproximability
theorems in `CslibFrontier.Computability.PCP.Approximation.IndependentSet` and `FGLSSRuntime`:

* Concrete 1-coin, 1-query verifier `oneCoinConflict` on `Bool` whose `false` instance produces two
  conflicting accepting views (independence number `1` vs target `2`), amplified by `repeatAll` to
  arbitrary constant soundness;
* Every-constant `NP`-hardness and `PromiseP` non-membership of `GapIndependentSet s` and
  `GapClique s` for `0 < s < 1`, including the former fixed constant `1 - 1 / (3 * 2 ^ 77)` and
  arbitrarily small constants, together with nonemptiness of both sides of the promise;
* Sharpness of both hypotheses `0 < s` and `s < 1`: for `s = 0` and for `1 ≤ s`,
  `GapIndependentSet s` lies unconditionally in `PromiseP`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FGLSSHardness

open Cslib.Complexity Turing.MultiTapeTM

/-- One coin, one query to position `0`: on `true`, accept when the answer bit is `true`
(both coins agree on `π = [true]`); on `false`, require the answer at position `0` to match the
coin bit, creating two accepting views that conflict at position `0`. -/
def oneCoinConflict : PCPVerifier Bool where
  coins _ := 1
  queries _ := [0]
  verdict p := if p.1.1 then p.2.getD 0 false else p.1.2.getD 0 false == p.2.getD 0 false

theorem polyTime_oneCoinConflict : oneCoinConflict.PolyTime encBool where
  coins := .const 1
  queries := .const [0]
  verdict := by
    have hb := (ComputableInPolyTime.fst (encPair encBool encBits) encBits).fst'
    have hρ := (ComputableInPolyTime.fst (encPair encBool encBits) encBits).snd'
    have hans := ComputableInPolyTime.snd (encPair encBool encBits) encBits
    have hρ0 := (ComputableInPolyTime.bitsGetD false).comp (hρ.prod (.const 0))
    have hans0 := (ComputableInPolyTime.bitsGetD false).comp (hans.prod (.const 0))
    have hfin : ComputableInPolyTime
        (fun t : Bool × Bool × Bool => if t.1 then t.2.2 else t.2.1 == t.2.2)
        (encPair encBool (encPair encBool encBool)) encBool := .of_finite _
    exact hfin.comp (hb.prod (hρ0.prod hans0))

theorem isPCPVerifier_oneCoinConflict :
    IsPCPVerifier encBool (fun _ => 1) (fun _ => 1) oneCoinConflict {b | b = true} where
  coins_le _ := le_rfl
  length_queries_le _ _ _ := le_rfl
  complete b hb := ⟨[true], fun ρ _ => by subst hb; rfl⟩
  sound b hb π := by
    have hb' : b = false := Bool.eq_false_iff.mpr hb
    subst hb'
    rw [acceptCount_congr (W := fun x => x.2.getD 0 false == π.getD 0 false) (fun _ => rfl)]
    have hcoins : oneCoinConflict.coins false = 1 := rfl
    rw [hcoins]
    cases π.getD 0 false <;> decide

/-- On `true`, `oneCoinConflict.fglssToIndependentSet true` has independence number `2 = 2 ^ 1`;
on `false`, the two accepting views conflict at position `0`, leaving independence number at most
`1`. -/
example :
    oneCoinConflict.fglssToIndependentSet true ∈ (GapIndependentSet (1 / 2)).yes ∧
    oneCoinConflict.fglssToIndependentSet false ∈ (GapIndependentSet (1 / 2)).no := by
  have hpcp : IsPCPVerifierWith encBool 1 (1 / 2) (fun _ => 1) (fun _ => 1)
      oneCoinConflict {b | b = true} :=
    isPCPVerifierWith_one_half_iff.mpr isPCPVerifier_oneCoinConflict
  have hmem : ({b : Bool | b = true} : Set Bool) ∈
      PCPWith 1 (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => 1) encBool :=
    ⟨oneCoinConflict, 1, 1, polyTime_oneCoinConflict,
      hpcp.mono_randomness fun n => by dsimp only; omega⟩
  have _ := polyTimeReducible_GapIndependentSet_of_mem_PCPWith
    (by norm_num : (1 / 2 : ℝ) < 1) hmem
  have htrue := isPCPVerifier_oneCoinConflict.indepNum_fglssGraph_eq_of_mem (a := true) rfl
  have hfalse := isPCPVerifier_oneCoinConflict.two_mul_indepNum_fglssGraph_le_of_not_mem
    (a := false) Bool.false_ne_true
  refine ⟨?_, ?_⟩
  · simp only [GapIndependentSet, PromiseProblem.mem_yes_gapMax,
      PCPVerifier.fglssToIndependentSet, PCPVerifier.indepNum_fglssEdgeList, htrue]
    norm_num [oneCoinConflict]
  · refine (PromiseProblem.mem_no_gapMax_of_lt (by norm_num [PCPVerifier.fglssToIndependentSet,
        oneCoinConflict])).2 ?_
    change ((oneCoinConflict.fglssEdgeList false).indepNum : ℝ) ≤
      1 / 2 * ((oneCoinConflict.fglssToIndependentSet false).m : ℝ)
    rw [PCPVerifier.indepNum_fglssEdgeList]
    have hfalse' : (2 : ℝ) * (oneCoinConflict.fglssGraph false).indepNum ≤ 2 := by
      simpa [oneCoinConflict] using (Nat.cast_le (α := ℝ)).mpr hfalse
    have hm : ((oneCoinConflict.fglssToIndependentSet false).m : ℝ) = 2 := by
      norm_num [PCPVerifier.fglssToIndependentSet, oneCoinConflict]
    linarith

/-- Fourfold independent repetition amplifies `oneCoinConflict` to soundness `1 / 16` with native
polynomial-time FGLSS reduction. -/
example :
    ComputableInPolyTime (oneCoinConflict.repeatAll 4).fglssToIndependentSet
      encBool encIndependentSetInstance ∧
    ((oneCoinConflict.repeatAll 4).fglssEdgeList false).indepNum ≤ 1 := by
  have hpoly := oneCoinConflict.polyTime_repeatAll polyTime_oneCoinConflict 4
  refine ⟨(oneCoinConflict.repeatAll 4).computableInPolyTime_fglssToIndependentSet hpoly
    (c := 4) (d := 4)
    (fun _ => by simp [oneCoinConflict])
    (fun a ρ hρ => oneCoinConflict.length_queries_repeatAll_le 4 hρ
      (B := 1) fun _ _ => le_rfl), ?_⟩
  rw [PCPVerifier.indepNum_fglssEdgeList]
  obtain ⟨π, hπ⟩ := (oneCoinConflict.repeatAll 4).exists_acceptCount_eq_indepNum_fglssGraph false
  have hpcp := (isPCPVerifierWith_one_half_iff.mpr isPCPVerifier_oneCoinConflict).repeatAll
    zero_le_one 4
  have hs := hpcp.sound false Bool.false_ne_true π
  have hcoins : (oneCoinConflict.repeatAll 4).coins false = 4 := rfl
  rw [PCPVerifier.acceptProb, PCPVerifier.acceptCount, hπ, hcoins,
    div_le_iff₀ (by positivity)] at hs
  have hs' : (((oneCoinConflict.repeatAll 4).fglssGraph false).indepNum : ℝ) ≤ 1 := by linarith
  exact_mod_cast hs'

/-- Every constant `0 < s < 1` gives NP-hard `GapIndependentSet s` and `GapClique s` with both
yes- and no-instances, recovering the former `1 - 1 / (3 * 2 ^ 77)` constant and arbitrarily small
constants alike. -/
example {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    PromiseProblem.NPHard encIndependentSetInstance (GapIndependentSet s) ∧
    PromiseProblem.NPHard encCliqueInstance (GapClique s) ∧
    (∃ x, x ∈ (GapIndependentSet s).yes) ∧ (∃ x, x ∈ (GapIndependentSet s).no) ∧
    (∃ x, x ∈ (GapClique s).yes) ∧ (∃ x, x ∈ (GapClique s).no) := by
  have hIS := GapIndependentSet_npHard hs0 hs1
  have hCl := GapClique_npHard hs0 hs1
  have hNP : ({b : Bool | b = true} : Set Bool) ∈ NP encBool :=
    P_subset_NP (mem_P.mpr ⟨id, .id', fun b => by simp⟩)
  obtain ⟨f, _, hyesIS, hnoIS⟩ := hIS encBool {b : Bool | b = true} hNP
  obtain ⟨g, _, hyesCl, hnoCl⟩ := hCl encBool {b : Bool | b = true} hNP
  exact ⟨hIS, hCl,
    ⟨f true, hyesIS rfl⟩, ⟨f false, hnoIS Bool.false_ne_true⟩,
    ⟨g true, hyesCl rfl⟩, ⟨g false, hnoCl Bool.false_ne_true⟩⟩

example :
    PromiseProblem.NPHard encIndependentSetInstance (GapIndependentSet (1 / 100)) ∧
    PromiseProblem.NPHard encCliqueInstance (GapClique (1 / 100)) ∧
    PromiseProblem.NPHard encIndependentSetInstance (GapIndependentSet (1 - 1 / (3 * 2 ^ 77))) ∧
    PromiseProblem.NPHard encCliqueInstance (GapClique (1 - 1 / (3 * 2 ^ 77))) :=
  ⟨GapIndependentSet_npHard (by norm_num) (by norm_num),
    GapClique_npHard (by norm_num) (by norm_num),
    GapIndependentSet_npHard (by norm_num) (by norm_num),
    GapClique_npHard (by norm_num) (by norm_num)⟩

example {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapIndependentSet (1 / 100) ∉ PromiseP encIndependentSetInstance ∧
    GapClique (1 / 100) ∉ PromiseP encCliqueInstance :=
  ⟨GapIndependentSet_notMem_PromiseP (by norm_num) (by norm_num) h,
    GapClique_notMem_PromiseP (by norm_num) (by norm_num) h⟩

/-- Boundary sharpness at `s ≥ 1`: no-instances are empty, so `GapIndependentSet s ∈ PromiseP`. -/
example {s : ℝ} (hs1 : 1 ≤ s) :
    (GapIndependentSet s).no = ∅ ∧ GapIndependentSet s ∈ PromiseP encIndependentSetInstance := by
  have hno : (GapIndependentSet s).no = ∅ := by
    ext x
    simp only [GapIndependentSet, PromiseProblem.mem_no_gapMax, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro _
    have hm : (0 : ℝ) ≤ x.m := Nat.cast_nonneg x.m
    nlinarith
  refine ⟨hno, mem_PromiseP_iff.mpr ⟨fun _ => true, .const true, fun _ _ => rfl, ?_⟩⟩
  rw [hno]
  intro _ h
  exact False.elim h

/-- Boundary sharpness at `s = 0`: an instance is a no-instance only when its graph has no declared
vertices and its target is positive, so `GapIndependentSet 0 ∈ PromiseP`. -/
example : GapIndependentSet 0 ∈ PromiseP encIndependentSetInstance := by
  refine mem_PromiseP_iff.mpr
    ⟨fun x => decide (x.m = 0) || !x.graph.vertices.isEmpty, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hm : ComputableInPolyTime (fun x : IndependentSetInstance => decide (x.m = 0))
        encIndependentSetInstance encBool := by fun_prop
    have hv : ComputableInPolyTime
        (fun x : IndependentSetInstance => !x.graph.vertices.isEmpty)
        encIndependentSetInstance encBool := by fun_prop
    exact hm.bool_or' hv
  · rw [yes_GapIndependentSet] at hx
    rcases Nat.eq_zero_or_pos x.m with hm0 | hmpos
    · simp [hm0]
    · have hcard := Graph.le_card_of_mem_IndependentSet hx
      have hne : x.graph.vertices ≠ [] := by
        intro hemp
        rw [hemp] at hcard
        simp at hcard
        omega
      simp [List.isEmpty_eq_false_iff.mpr hne]
  · simp only [GapIndependentSet, PromiseProblem.mem_no_gapMax, zero_mul, Nat.cast_nonpos,
      Nat.cast_pos] at hx
    obtain ⟨hind0, hmpos⟩ := hx
    have hemp : x.graph.vertices = [] := by
      by_contra hne
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
      have h1 : 1 ≤ x.graph.indepNum :=
        Graph.le_indepNum_iff.mpr (mem_IndependentSet_iff.mpr
          ⟨{v}, by simp [hv], ⟨by simp [SimpleGraph.IsIndepSet, Set.Pairwise], by simp⟩⟩)
      omega
    simp [Nat.ne_of_gt hmpos, hemp]

/-- Model-boundary witness: a 0-coin verifier querying position `0` twice and accepting only when
the two answers differ has no self-consistent accepting views (`fglssEdgeList` has `[]` vertices and
`indepNum = 0`), while `2 ^ 0 = 1` sets a positive target `m = 1`, placing the image in
`(GapIndependentSet s).no` for every `0 ≤ s < 1`. -/
def zeroCoinSelfConflict : PCPVerifier Unit where
  coins _ := 0
  queries _ := [0, 0]
  verdict p := p.2.getD 0 false != p.2.getD 1 false

example {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (zeroCoinSelfConflict.fglssEdgeList ()).vertices = [] ∧
    (zeroCoinSelfConflict.fglssToIndependentSet ()).m = 1 ∧
    zeroCoinSelfConflict.fglssToIndependentSet () ∈ (GapIndependentSet s).no := by
  have hno_vert : IsEmpty
      {v : zeroCoinSelfConflict.View () // zeroCoinSelfConflict.IsFGLSSVertex () v} :=
    ⟨fun ⟨v, hv⟩ => by
      have h := hv.consistent.eq (i := ⟨0, by simp [zeroCoinSelfConflict]⟩)
        (j := ⟨1, by simp [zeroCoinSelfConflict]⟩) rfl
      exact absurd h (by simpa [zeroCoinSelfConflict, List.ofFn_succ] using hv.accepts)⟩
  have hemp : (zeroCoinSelfConflict.fglssEdgeList ()).vertices = [] := by
    by_contra h
    obtain ⟨n, hn⟩ := List.exists_mem_of_ne_nil _ h
    exact isEmptyElim ((zeroCoinSelfConflict.fglssGraphIso ()).symm ⟨n, hn⟩)
  have hm : (zeroCoinSelfConflict.fglssToIndependentSet ()).m = 1 := rfl
  refine ⟨hemp, hm, ?_⟩
  refine (PromiseProblem.mem_no_gapMax_of_lt (by rw [hm]; push_cast; linarith)).2 ?_
  have hle := Graph.indepNum_le_card (zeroCoinSelfConflict.fglssEdgeList ())
  rw [hemp] at hle
  have h0 : (zeroCoinSelfConflict.fglssEdgeList ()).indepNum = 0 := by simpa using hle
  change ((zeroCoinSelfConflict.fglssEdgeList ()).indepNum : ℝ) ≤ s * (1 : ℕ)
  rw [h0]
  push_cast
  linarith

end CslibFrontierTests.FGLSSHardness
