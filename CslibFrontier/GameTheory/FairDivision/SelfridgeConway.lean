/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Selfridge–Conway Discrete Three-Player Envy-Free Cake Cutting

Formalizes the discrete three-player envy-free cake-cutting protocol discovered independently by
John Selfridge and John Horton Conway c. 1960 and published in [BramsTaylor1995] and
[RobertsonWebb1998], over arbitrary nonatomic finite additive valuations (`CakeValuation`) on
`[0, 1]` in the Robertson–Webb query model (`FreeM (RWQuery (Fin 3))`).

## Protocol overview

1. **Initial division (`2` cuts):** Player `0` cuts `[0, 1]` at `0 ≤ c₁ ≤ c₂ ≤ 1` into three
   intervals `X 0 = [0, c₁]`, `X 1 = [c₁, c₂]`, `X 2 = [c₂, 1]` of equal `v₀`-value `1 / 3`.
2. **Player `1` inspection:** Player `1` evaluates `X 0, X 1, X 2` and sorts them in nonincreasing
   order `v₁(X p₀) ≥ v₁(X p₁) ≥ v₁(X p₂)`.
   * **Untrimmed branch (`v₁(X p₀) ≤ v₁(X p₁)`):** Player `1`'s top two pieces are tied. No
     further cuts are made (`2` cuts total): Player `2` takes a favorite piece `X q₂`, Player `1`
     takes an available piece `X q₁` from `{p₀, p₁}` (`v₁(X q₁) = v₁(X p₀)`), and Player `0`
     receives the remaining piece `X q₀` (`v₀(X q₀) = 1 / 3`).
   * **Trimmed branch (`v₁(X p₁) < v₁(X p₀)`):**
     - **Phase 1 (`1` trim cut):** Player `1` trims `X p₀ = [ℓ, r]` at `t ∈ [ℓ, r]` so that
       `Y p₀ = [ℓ, t]` satisfies `v₁(Y p₀) = v₁(X p₁)`, setting aside the trimming `T = [t, r]`
       while leaving `Y k = X k` for `k ≠ p₀`. Player `2` chooses a favorite `Y q₂`; Player `1`
       takes `Y p₀` if `q₂ ≠ p₀` and `Y p₁` if `q₂ = p₀`; Player `0` receives the remaining
       untrimmed piece `Y q₀` (`q₀ ≠ p₀`, so `v₀(Y q₀) = 1 / 3`).
     - **Phase 2 (`2` trimming cuts):** Let `pa ∈ {1, 2}` be whichever of Players `1, 2` received
       the trimmed piece `Y p₀`, and `pd ∈ {1, 2} \ {pa}` the other. Player `pd` cuts `T = [t, r]`
       at `t ≤ u₁ ≤ u₂ ≤ r` into three pieces `T₀, T₁, T₂` of equal `v_{pd}`-value `v_{pd}(T) / 3`.
       Player `pa` chooses a favorite `T_{s_{pa}}` first, Player `0` chooses a preferred remaining
       piece `T_{s₀}` second, and `pd` receives the last piece `T_{s_{pd}}`.

In Phase 2, Player `0` holds an irrevocable advantage over `pa`: because `Y p₀` and `T₀, T₁, T₂`
partition `X p₀`, `v₀(Y p₀) + v₀(T_{s_{pa}}) ≤ v₀(X p₀) = 1 / 3 ≤ v₀(Y q₀) + v₀(T_{s₀})`. Thus
every player weakly prefers their combined bundle to every other player's bundle using at most `5`
physical cuts.

## Main definitions

* `Cslib.GameTheory.FairDivision.selfridgeConwayQ`: three-player Selfridge–Conway protocol in
  `FreeM (RWQuery (Fin 3)) (DividedCake 3)`.
* `Cslib.GameTheory.FairDivision.selfridgeConway`: canonical pure evaluation against
  `RWQuery.oracleOf v`.

## Main results

* `Cslib.GameTheory.FairDivision.isValidPartition_selfridgeConwayQ`: `selfridgeConwayQ` produces a
  valid interval partition of `[0, 1]` against every oracle.
* `Cslib.GameTheory.FairDivision.numCuts_selfridgeConwayQ_le`,
  `Cslib.GameTheory.FairDivision.numCuts_selfridgeConwayQ_eq_two_or_five`: `selfridgeConwayQ` makes
  at most `5` physical cuts (`2` untrimmed or `5` trimmed).
* `Cslib.GameTheory.FairDivision.countQueries_selfridgeConwayQ_le`: `selfridgeConwayQ` makes at
  most `18` Robertson–Webb queries.
* `Cslib.GameTheory.FairDivision.isEnvyFree_selfridgeConwayQ`,
  `Cslib.GameTheory.FairDivision.isProportional_selfridgeConwayQ`: complete case analysis proving
  all three players are envy-free (and hence receive `≥ 1 / 3`) for every valuation profile.

## References

* [S. J. Brams and A. D. Taylor, *An Envy-Free Cake Division Protocol*][BramsTaylor1995]
* [J. Robertson and W. Webb, *Cake-Cutting Algorithms: Be Fair If You Can*][RobertsonWebb1998]
-/

public section

namespace Cslib.GameTheory.FairDivision

open Cslib (FreeM)

/-! ### Finite `Fin 3` selection and permutation helpers -/

/-- The unique element of `Fin 3` distinct from `a` and `b` when `a ≠ b`. -/
private def thirdFin3 (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0
  else if a ≠ 1 ∧ b ≠ 1 then 1
  else 2

private theorem thirdFin3_ne_left {a b : Fin 3} (hab : a ≠ b) : thirdFin3 a b ≠ a := by
  fin_cases a <;> fin_cases b <;> simp_all [thirdFin3]

private theorem thirdFin3_ne_right {a b : Fin 3} (hab : a ≠ b) : thirdFin3 a b ≠ b := by
  fin_cases a <;> fin_cases b <;> simp_all [thirdFin3]

private theorem perm_three_of_ne {α : Type} {a b : Fin 3} (hab : a ≠ b) (f : Fin 3 → α) :
    [f (thirdFin3 a b), f b, f a].Perm [f 0, f 1, f 2] := by
  have hidx : [thirdFin3 a b, b, a].Perm [0, 1, 2] := by
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide
  simpa only [List.map_cons, List.map_nil] using hidx.map f

private theorem sum_three_of_ne {a b : Fin 3} (hab : a ≠ b) (g : Fin 3 → ℝ) :
    g (thirdFin3 a b) + g b + g a = g 0 + g 1 + g 2 := by
  have hp := (perm_three_of_ne hab g).sum_eq
  simp only [List.sum_cons, List.sum_nil, add_zero] at hp
  linarith

/-- Evaluate agent `i` on all three pieces of `P : Fin 3 → CakePiece`. -/
private noncomputable def evalThree (i : Fin 3) (P : Fin 3 → CakePiece) :
    FreeM (RWQuery (Fin 3)) (Fin 3 → ℝ) := do
  let v0 ← RWQuery.evalAsk i (P 0).left (P 0).right
  let v1 ← RWQuery.evalAsk i (P 1).left (P 1).right
  let v2 ← RWQuery.evalAsk i (P 2).left (P 2).right
  pure fun
    | 0 => v0
    | 1 => v1
    | 2 => v2

private theorem countQueries_evalThree
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) (i : Fin 3) (P : Fin 3 → CakePiece) :
    (evalThree i P).countQueries oracle = 3 := by
  simp only [evalThree, FreeM.countQueries_bind, RWQuery.countQueries_evalAsk,
    FreeM.countQueries_pure]

private theorem eval_evalThree {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle)
    (i : Fin 3) (P : Fin 3 → CakePiece) :
    (evalThree i P).eval oracle = fun k => (v i).pieceVal (P k) := by
  funext k
  simp only [evalThree, FreeM.eval_bind, FreeM.eval_pure, ho.eval_evalAsk]
  fin_cases k <;> rfl

/-- Top index maximizing `u : Fin 3 → ℝ`. -/
private noncomputable def topChoice (u : Fin 3 → ℝ) : Fin 3 :=
  Tuple.sortDesc u 0

private theorem le_topChoice (u : Fin 3 → ℝ) (k : Fin 3) :
    u k ≤ u (topChoice u) :=
  Equiv.apply_symm_apply (Tuple.sortDesc u) k ▸
    Tuple.antitone_sortDesc u (Fin.zero_le _)

/-- Best index maximizing `u : Fin 3 → ℝ` among `{k | k ≠ taken}`. -/
private noncomputable def bestOther (u : Fin 3 → ℝ) (taken : Fin 3) : Fin 3 :=
  let σ := Tuple.sortDesc u
  if σ 0 ≠ taken then σ 0 else σ 1

private theorem bestOther_ne (u : Fin 3 → ℝ) (taken : Fin 3) :
    bestOther u taken ≠ taken := by
  dsimp only [bestOther]
  set σ := Tuple.sortDesc u
  split_ifs with h0
  · exact h0
  · exact fun h1 => absurd (σ.injective (h1.trans (not_ne_iff.mp h0).symm)) (by decide)

private theorem le_bestOther_of_ne (u : Fin 3 → ℝ) {taken k : Fin 3} (hk : k ≠ taken) :
    u k ≤ u (bestOther u taken) := by
  dsimp only [bestOther]
  set σ := Tuple.sortDesc u
  split_ifs with h0
  · exact le_topChoice u k
  · have hsymm_ne : σ.symm k ≠ 0 := fun hz =>
      hk (by rw [← not_ne_iff.mp h0, ← hz, Equiv.apply_symm_apply])
    exact Equiv.apply_symm_apply σ k ▸
      Tuple.antitone_sortDesc u (Nat.succ_le_of_lt (Fin.pos_iff_ne_zero.mpr hsymm_ne))

private theorem perm_interleave_three {α : Type} (a0 b0 a1 b1 a2 b2 : α) :
    [a0, b0, a1, b1, a2, b2].Perm [a0, a1, a2, b0, b1, b2] := by
  simpa using (show ([0, 3, 1, 4, 2, 5] : List (Fin 6)).Perm [0, 1, 2, 3, 4, 5] by decide).map
    ![a0, a1, a2, b0, b1, b2]

/-! ### Pure Piece Constructors and Staged Sub-Programs -/

private def scTrimSubPieces (t u1 u2 r : ℝ) : Fin 3 → CakePiece
  | 0 => ⟨t, u1⟩
  | 1 => ⟨u1, u2⟩
  | 2 => ⟨u2, r⟩

private abbrev scInitialPieces (c1 c2 : ℝ) : Fin 3 → CakePiece :=
  scTrimSubPieces 0 c1 c2 1

private def scTrimmedPieces (c1 c2 : ℝ) (p0 : Fin 3) (t : ℝ) : Fin 3 → CakePiece :=
  fun k => if k = p0 then ⟨(scInitialPieces c1 c2 p0).left, t⟩ else scInitialPieces c1 c2 k

/-- Two sequential `RWQuery.cutIn` queries at target value `α = v i a b / 3` divide
`[a, b] ⊆ [0, 1]` into three ordered subintervals `scTrimSubPieces a u₁ u₂ b` of equal `v i`-value
`α`. -/
private theorem cutIntoThirds_spec {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle)
    (i : Fin 3) {a b α : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hα : α = v i a b / 3) :
    let u1 := (RWQuery.cutIn i a b α).eval oracle
    let u2 := (RWQuery.cutIn i u1 b α).eval oracle
    a ≤ u1 ∧ u1 ≤ u2 ∧ u2 ≤ b ∧
      (∀ k : Fin 3, (v i).pieceVal (scTrimSubPieces a u1 u2 b k) = α) := by
  have hv_nn : 0 ≤ v i a b := (v i).val_nonneg ha hb
  obtain ⟨⟨hu1_a, hu1_b⟩, hvu1⟩ :=
    ho.eval_cutIn_spec i (α := α) ha hab hb (by linarith) (by linarith)
  set u1 := (RWQuery.cutIn i a b α).eval oracle
  have hrem : v i u1 b = 2 * α := by linarith [(v i).val_add ha hu1_a hu1_b hb]
  obtain ⟨⟨hu2_u1, hu2_b⟩, hvu2⟩ :=
    ho.eval_cutIn_spec i (α := α) (ha.trans hu1_a) hu1_b hb (by linarith) (by linarith)
  set u2 := (RWQuery.cutIn i u1 b α).eval oracle
  have hvu3 : v i u2 b = α := by linarith [(v i).val_add (ha.trans hu1_a) hu2_u1 hu2_b hb]
  refine ⟨hu1_a, hu2_u1, hu2_b, fun k => ?_⟩
  fin_cases k <;> assumption

private noncomputable def scBuildUntrimmed (c1 c2 : ℝ) (u1 u2 : Fin 3 → ℝ) : DividedCake 3 :=
  let X := scInitialPieces c1 c2
  let q2 := topChoice u2
  let q1 := bestOther u1 q2
  let q0 := thirdFin3 q2 q1
  { cuts := [c1, c2]
    pieces := fun
      | 0 => [X q0]
      | 1 => [X q1]
      | 2 => [X q2] }

private noncomputable def scBuildTrimmed (c1 c2 : ℝ) (p0 p1 : Fin 3) (t : ℝ)
    (q2 : Fin 3) (u_cut1 u_cut2 : ℝ) (w_pa w_0 : Fin 3 → ℝ) : DividedCake 3 :=
  let r := (scInitialPieces c1 c2 p0).right
  let Y := scTrimmedPieces c1 c2 p0 t
  let T_sub := scTrimSubPieces t u_cut1 u_cut2 r
  let q1 : Fin 3 := if q2 = p0 then p1 else p0
  let q0 := thirdFin3 q2 q1
  let s_pa := topChoice w_pa
  let s_0 := bestOther w_0 s_pa
  let s_pd := thirdFin3 s_pa s_0
  let s1 : Fin 3 := if q2 = p0 then s_pd else s_pa
  let s2 : Fin 3 := if q2 = p0 then s_pa else s_pd
  let cuts5 : List ℝ :=
    match p0 with
    | 0 => [t, u_cut1, u_cut2, c1, c2]
    | 1 => [c1, t, u_cut1, u_cut2, c2]
    | 2 => [c1, c2, t, u_cut1, u_cut2]
  { cuts := cuts5
    pieces := fun
      | 0 => [Y q0, T_sub s_0]
      | 1 => [Y q1, T_sub s1]
      | 2 => [Y q2, T_sub s2] }

private noncomputable def scUntrimmedBranchQ (c1 c2 : ℝ) (u1 : Fin 3 → ℝ) :
    FreeM (RWQuery (Fin 3)) (DividedCake 3) := do
  let u2 ← evalThree 2 (scInitialPieces c1 c2)
  pure (scBuildUntrimmed c1 c2 u1 u2)

private noncomputable def scTrimmedBranchQ (c1 c2 : ℝ) (p0 p1 : Fin 3) (target : ℝ) :
    FreeM (RWQuery (Fin 3)) (DividedCake 3) := do
  let l := (scInitialPieces c1 c2 p0).left
  let r := (scInitialPieces c1 c2 p0).right
  let t ← RWQuery.cutIn 1 l r target
  let u2 ← evalThree 2 (scTrimmedPieces c1 c2 p0 t)
  let q2 := topChoice u2
  let pa : Fin 3 := if q2 = p0 then 2 else 1
  let pd : Fin 3 := if q2 = p0 then 1 else 2
  let w_pd ← RWQuery.evalAsk pd t r
  let u_cut1 ← RWQuery.cutIn pd t r (w_pd / 3)
  let u_cut2 ← RWQuery.cutIn pd u_cut1 r (w_pd / 3)
  let T_sub := scTrimSubPieces t u_cut1 u_cut2 r
  let w_pa ← evalThree pa T_sub
  let w_0 ← evalThree 0 T_sub
  pure (scBuildTrimmed c1 c2 p0 p1 t q2 u_cut1 u_cut2 w_pa w_0)

/-- **Selfridge–Conway discrete three-player envy-free cake-cutting protocol** in the
Robertson–Webb query model ([BramsTaylor1995]; [RobertsonWebb1998]). -/
noncomputable def selfridgeConwayQ : FreeM (RWQuery (Fin 3)) (DividedCake 3) := do
  let c1 ← RWQuery.cutIn 0 0 1 (1 / 3)
  let c2 ← RWQuery.cutIn 0 c1 1 (1 / 3)
  let u1 ← evalThree 1 (scInitialPieces c1 c2)
  let σ1 := Tuple.sortDesc u1
  let p0 := σ1 0
  let p1 := σ1 1
  if u1 p0 ≤ u1 p1 then
    scUntrimmedBranchQ c1 c2 u1
  else
    scTrimmedBranchQ c1 c2 p0 p1 (u1 p1)

/-- Canonical pure evaluation of `selfridgeConwayQ` against `RWQuery.oracleOf v`. -/
@[expose] noncomputable def selfridgeConway (v : Fin 3 → CakeValuation) : DividedCake 3 :=
  selfridgeConwayQ.eval (RWQuery.oracleOf v)

/-! ### Cut-Count, Query-Count, and Partition Validity Proofs -/

private theorem numCuts_selfridgeConwayQ_eq
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) :
    let c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
    let c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
    let u1 := (evalThree 1 (scInitialPieces c1 c2)).eval oracle
    let σ1 := Tuple.sortDesc u1
    (selfridgeConwayQ.eval oracle).numCuts = if u1 (σ1 0) ≤ u1 (σ1 1) then 2 else 5 := by
  have h5 (c1 c2 : ℝ) (p0 p1 : Fin 3) (t : ℝ) (q2 : Fin 3) (u_cut1 u_cut2 : ℝ)
      (w_pa w_0 : Fin 3 → ℝ) :
      (scBuildTrimmed c1 c2 p0 p1 t q2 u_cut1 u_cut2 w_pa w_0).numCuts = 5 := by
    fin_cases p0 <;> rfl
  rw [selfridgeConwayQ]
  simp only [FreeM.eval_bind]
  split_ifs <;> simp only [scUntrimmedBranchQ, scTrimmedBranchQ, FreeM.eval_bind,
    FreeM.eval_pure, h5]
  rfl

/-- `selfridgeConwayQ` makes either `2` physical cuts (untrimmed branch) or `5` physical cuts
(trimmed branch). -/
theorem numCuts_selfridgeConwayQ_eq_two_or_five
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) :
    (selfridgeConwayQ.eval oracle).numCuts = 2 ∨
      (selfridgeConwayQ.eval oracle).numCuts = 5 := by
  rw [numCuts_selfridgeConwayQ_eq]
  split_ifs <;> simp

/-- When Player `1` shares Player `0`'s valuation (`v 1 = v 0`), all three initial thirds have
equal `v₁`-value `1 / 3`, so `selfridgeConwayQ` takes the untrimmed `2`-cut branch. -/
theorem numCuts_selfridgeConwayQ_eq_two_of_eq {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle)
    (h10 : v 1 = v 0) :
    (selfridgeConwayQ.eval oracle).numCuts = 2 := by
  obtain ⟨_, _, _, hv0_X⟩ :=
    cutIntoThirds_spec ho 0 le_rfl (by norm_num : (0 : ℝ) ≤ 1) le_rfl
      (α := 1 / 3) (by rw [(v 0).apply_zero_one])
  rw [numCuts_selfridgeConwayQ_eq]
  set c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
  set c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
  have hu1_const : (evalThree 1 (scInitialPieces c1 c2)).eval oracle = fun _ => 1 / 3 := by
    rw [eval_evalThree ho 1]
    funext k
    simpa only [CakeValuation.pieceVal, h10] using hv0_X k
  simp [hu1_const]

/-- When Player `1` has a unique strictly largest initial piece among `[0, c₁], [c₁, c₂], [c₂, 1]`,
`selfridgeConwayQ` takes the trimmed `5`-cut branch. -/
theorem numCuts_selfridgeConwayQ_eq_five_of_strict_max {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle)
    (k : Fin 3)
    (hstrict : ∀ j : Fin 3, j ≠ k →
      let c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
      let c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
      let X : Fin 3 → CakePiece := fun | 0 => ⟨0, c1⟩ | 1 => ⟨c1, c2⟩ | 2 => ⟨c2, 1⟩
      (v 1).pieceVal (X j) < (v 1).pieceVal (X k)) :
    (selfridgeConwayQ.eval oracle).numCuts = 5 := by
  rw [numCuts_selfridgeConwayQ_eq]
  set c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
  set c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
  set u1 := (evalThree 1 (scInitialPieces c1 c2)).eval oracle
  set σ1 := Tuple.sortDesc u1
  have hlt (j : Fin 3) (hne : j ≠ k) : u1 j < u1 k := by
    simp only [u1, eval_evalThree ho 1]
    exact hstrict j hne
  have hp0_eq_k : σ1 0 = k :=
    by_contra fun hne => not_lt_of_ge (le_topChoice u1 k) (hlt (σ1 0) hne)
  have hp1_ne_k : σ1 1 ≠ k := fun h => absurd (σ1.injective (hp0_eq_k.trans h.symm)) (by decide)
  exact ite_eq_right (not_le.mpr (hp0_eq_k ▸ hlt (σ1 1) hp1_ne_k))

/-- **Five-cut bound:** `selfridgeConwayQ` makes at most `5` physical cuts (`2` in the untrimmed
branch and `5` in the trimmed branch) against every oracle. -/
theorem numCuts_selfridgeConwayQ_le
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) :
    (selfridgeConwayQ.eval oracle).numCuts ≤ 5 := by
  rcases numCuts_selfridgeConwayQ_eq_two_or_five oracle with h | h <;> omega

/-- Each player receives at most `2` interval pieces under `selfridgeConwayQ`. -/
theorem length_pieces_selfridgeConwayQ_le
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) (i : Fin 3) :
    ((selfridgeConwayQ.eval oracle).pieces i).length ≤ 2 := by
  rw [selfridgeConwayQ]
  simp only [FreeM.eval_bind]
  split_ifs <;> simp only [scUntrimmedBranchQ, scTrimmedBranchQ, FreeM.eval_bind, FreeM.eval_pure,
    scBuildUntrimmed, scBuildTrimmed] <;> fin_cases i <;> simp

/-- `selfridgeConwayQ` makes at most `18` Robertson–Webb queries (`8` untrimmed or `18` trimmed)
against every oracle. -/
theorem countQueries_selfridgeConwayQ_le
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) :
    selfridgeConwayQ.countQueries oracle ≤ 18 := by
  rw [selfridgeConwayQ]
  simp only [FreeM.countQueries_bind, RWQuery.countQueries_cutIn, countQueries_evalThree]
  split_ifs <;> simp only [scUntrimmedBranchQ, scTrimmedBranchQ, FreeM.countQueries_bind,
    RWQuery.countQueries_cutIn, countQueries_evalThree, RWQuery.countQueries_evalAsk,
    FreeM.countQueries_pure] <;> omega

private theorem isValidPartition_scBuildTrimmed {c1 c2 : ℝ}
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (hc2 : c2 ≤ 1)
    {p0 p1 : Fin 3} (hp01 : p0 ≠ p1)
    {t u_cut1 u_cut2 : ℝ}
    (ht_l : (scInitialPieces c1 c2 p0).left ≤ t)
    (hu1_t : t ≤ u_cut1) (hu2_u1 : u_cut1 ≤ u_cut2)
    (hu2_r : u_cut2 ≤ (scInitialPieces c1 c2 p0).right)
    (q2 : Fin 3) (w_pa w_0 : Fin 3 → ℝ) :
    (scBuildTrimmed c1 c2 p0 p1 t q2 u_cut1 u_cut2 w_pa w_0).IsValidPartition := by
  set r := (scInitialPieces c1 c2 p0).right
  set Y := scTrimmedPieces c1 c2 p0 t
  set T_sub := scTrimSubPieces t u_cut1 u_cut2 r
  set q1 : Fin 3 := if q2 = p0 then p1 else p0
  have hq21 : q2 ≠ q1 := by by_cases hq : q2 = p0 <;> simp [q1, hq, hp01]
  set q0 := thirdFin3 q2 q1
  set s_pa := topChoice w_pa
  set s_0 := bestOther w_0 s_pa
  have hspa0 : s_pa ≠ s_0 := (bestOther_ne w_0 s_pa).symm
  set s_pd := thirdFin3 s_pa s_0
  set s1 : Fin 3 := if q2 = p0 then s_pd else s_pa
  set s2 : Fin 3 := if q2 = p0 then s_pa else s_pd
  have hT_perm : [T_sub s_0, T_sub s1, T_sub s2].Perm [T_sub 0, T_sub 1, T_sub 2] := by
    have hbase := perm_three_of_ne hspa0 T_sub
    by_cases hq : q2 = p0 <;> simp only [s1, s2, hq, ↓reduceIte]
    · exact (List.Perm.swap (T_sub s_pd) (T_sub s_0) [T_sub s_pa]).trans hbase
    · exact ((List.Perm.cons (T_sub s_0) (List.Perm.swap (T_sub s_pd) (T_sub s_pa) [])).trans
        (List.Perm.swap (T_sub s_pd) (T_sub s_0) [T_sub s_pa])).trans hbase
  have hY_perm : [Y q0, Y q1, Y q2].Perm [Y 0, Y 1, Y 2] := perm_three_of_ne hq21 Y
  have hall_perm :
      [Y q0, T_sub s_0, Y q1, T_sub s1, Y q2, T_sub s2].Perm
        ([Y 0, Y 1, Y 2] ++ [T_sub 0, T_sub 1, T_sub 2]) :=
    (perm_interleave_three _ _ _ _ _ _).trans (hY_perm.append hT_perm)
  refine ⟨?_, hall_perm.trans ?_⟩
  · dsimp only [scBuildTrimmed]
    revert ht_l hu2_r
    fin_cases p0 <;> intro ht_l hu2_r
    exacts [⟨ht_l, hu1_t, hu2_u1, hu2_r, hc12, hc2⟩,
      ⟨hc1, ht_l, hu1_t, hu2_u1, hu2_r, hc2⟩,
      ⟨hc1, hc12, ht_l, hu1_t, hu2_u1, hu2_r⟩]
  · dsimp only [scBuildTrimmed, Y, T_sub, r]
    clear hall_perm hY_perm hT_perm s2 s1 q0 hq21 q1 T_sub Y r ht_l hu2_r hp01
    fin_cases p0
    exacts [List.Perm.cons _ (List.perm_append_comm ..),
      List.Perm.cons _ (List.Perm.cons _ (List.perm_append_comm ..)), List.Perm.refl _]

/-- `selfridgeConwayQ` produces a valid interval partition of `[0, 1]` against every oracle. -/
theorem isValidPartition_selfridgeConwayQ
    (oracle : {ι : Type} → RWQuery (Fin 3) ι → ι) :
    (selfridgeConwayQ.eval oracle).IsValidPartition := by
  rw [selfridgeConwayQ]
  simp only [FreeM.eval_bind]
  set c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
  have hc1 : c1 ∈ Set.Icc (0 : ℝ) 1 := RWQuery.eval_cutIn_mem_Icc oracle 0 (by norm_num) (1 / 3)
  set c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
  have hc2 : c2 ∈ Set.Icc c1 1 := RWQuery.eval_cutIn_mem_Icc oracle 0 hc1.2 (1 / 3)
  set u1 := (evalThree 1 (scInitialPieces c1 c2)).eval oracle
  set σ1 := Tuple.sortDesc u1
  set p0 := σ1 0
  set p1 := σ1 1
  have hp01 : p0 ≠ p1 := fun h => absurd (σ1.injective h) (by decide)
  split_ifs with htie
  · simp only [scUntrimmedBranchQ, FreeM.eval_bind, FreeM.eval_pure]
    exact ⟨⟨hc1.1, hc2.1, hc2.2⟩,
      perm_three_of_ne (bestOther_ne u1 (topChoice _)).symm (scInitialPieces c1 c2)⟩
  · simp only [scTrimmedBranchQ, FreeM.eval_bind, FreeM.eval_pure]
    have hlr : (scInitialPieces c1 c2 p0).left ≤ (scInitialPieces c1 c2 p0).right := by
      clear_value p0
      fin_cases p0
      exacts [hc1.1, hc2.1, hc2.2]
    set l := (scInitialPieces c1 c2 p0).left
    set r := (scInitialPieces c1 c2 p0).right
    set t := (RWQuery.cutIn (1 : Fin 3) l r (u1 p1)).eval oracle
    have ht : t ∈ Set.Icc l r := RWQuery.eval_cutIn_mem_Icc oracle 1 hlr (u1 p1)
    set q2 := topChoice ((evalThree 2 (scTrimmedPieces c1 c2 p0 t)).eval oracle)
    set pd : Fin 3 := if q2 = p0 then 1 else 2
    set w_pd := (RWQuery.evalAsk pd t r).eval oracle
    set u_cut1 := (RWQuery.cutIn pd t r (w_pd / 3)).eval oracle
    have hu1 : u_cut1 ∈ Set.Icc t r := RWQuery.eval_cutIn_mem_Icc oracle pd ht.2 (w_pd / 3)
    set u_cut2 := (RWQuery.cutIn pd u_cut1 r (w_pd / 3)).eval oracle
    have hu2 : u_cut2 ∈ Set.Icc u_cut1 r :=
      RWQuery.eval_cutIn_mem_Icc oracle pd hu1.2 (w_pd / 3)
    exact isValidPartition_scBuildTrimmed hc1.1 hc2.1 hc2.2 hp01 ht.1 hu1.1 hu2.1 hu2.2 q2 _ _

/-! ### Complete Case Analysis of Envy-Freeness -/

/-- **Selfridge–Conway Envy-Freeness Theorem:** for every three-player valuation profile
`v : Fin 3 → CakeValuation` and every valid Robertson–Webb oracle `oracle`, `selfridgeConwayQ`
produces an allocation in which **all three players (`0`, `1`, `2`) are envy-free**. -/
theorem isEnvyFree_selfridgeConwayQ {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    (selfridgeConwayQ.eval oracle).IsEnvyFree v := by
  rw [selfridgeConwayQ]
  simp only [FreeM.eval_bind]
  obtain ⟨hc1_0, hc2_c1, hc2_1, hv0_X⟩ :=
    cutIntoThirds_spec ho 0 le_rfl (by norm_num : (0 : ℝ) ≤ 1) le_rfl
      (α := 1 / 3) (by rw [(v 0).apply_zero_one])
  set c1 := (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval oracle
  set c2 := (RWQuery.cutIn (0 : Fin 3) c1 1 (1 / 3)).eval oracle
  set X := scInitialPieces c1 c2
  have hX_bounds (k : Fin 3) : 0 ≤ (X k).left ∧ (X k).left ≤ (X k).right ∧ (X k).right ≤ 1 := by
    fin_cases k
    exacts [⟨le_rfl, hc1_0, hc2_c1.trans hc2_1⟩, ⟨hc1_0, hc2_c1, hc2_1⟩,
      ⟨hc1_0.trans hc2_c1, hc2_1, le_rfl⟩]
  have hu1_eq : (evalThree 1 X).eval oracle = fun k => (v 1).pieceVal (X k) :=
    eval_evalThree ho 1 X
  set u1 := (evalThree 1 X).eval oracle
  set σ1 := Tuple.sortDesc u1
  set p0 := σ1 0
  set p1 := σ1 1
  have hp0_ne_p1 : p0 ≠ p1 := fun h => absurd (σ1.injective h) (by decide)
  have hu1_p1_le_p0 : u1 p1 ≤ u1 p0 :=
    Tuple.antitone_sortDesc u1 (by decide : (0 : Fin 3) ≤ 1)
  have hu1_top : ∀ k : Fin 3, u1 k ≤ u1 p0 := le_topChoice u1
  split_ifs with htie
  · -- Branch A: Player 1's top two pieces are tied (`u1 p0 = u1 p1`), 2 cuts total.
    simp only [scUntrimmedBranchQ, FreeM.eval_bind, FreeM.eval_pure]
    set u2 := (evalThree 2 X).eval oracle
    set q2 := topChoice u2
    set q1 := bestOther u1 q2
    set q0 := thirdFin3 q2 q1
    have hu1_tie_eq : u1 p0 = u1 p1 := le_antisymm htie hu1_p1_le_p0
    have hq1_val : u1 q1 = u1 p0 := by
      by_cases hq : σ1 0 ≠ q2 <;> simp [q1, bestOther, σ1, p0, p1, hq, hu1_tie_eq]
    have h1_fav (k : Fin 3) : (v 1).pieceVal (X k) ≤ (v 1).pieceVal (X q1) := by
      simpa only [hu1_eq] using (hq1_val ▸ hu1_top k : u1 k ≤ u1 q1)
    have h2_fav (k : Fin 3) : (v 2).pieceVal (X k) ≤ (v 2).pieceVal (X q2) := by
      simpa only [u2, q2, eval_evalThree ho 2 X] using le_topChoice u2 k
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [scBuildUntrimmed, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, CakeValuation.bundleVal_singleton]
    exacts [le_rfl, (hv0_X q1).trans_le (hv0_X q0).ge, (hv0_X q2).trans_le (hv0_X q0).ge,
      h1_fav q0, le_rfl, h1_fav q2, h2_fav q0, h2_fav q1, le_rfl]
  · -- Branch B: Trim needed (`u1 p1 < u1 p0`), 5 cuts total.
    simp only [scTrimmedBranchQ, FreeM.eval_bind, FreeM.eval_pure]
    set l := (X p0).left
    set r := (X p0).right
    obtain ⟨hl0, hlr, hr1⟩ := hX_bounds p0
    have hu1_p1_nonneg : 0 ≤ u1 p1 :=
      congrFun hu1_eq p1 ▸ (v 1).val_nonneg (hX_bounds p1).1 (hX_bounds p1).2.2
    have hu1_p1_le_lr : u1 p1 ≤ v 1 l r := by
      simpa only [congrFun hu1_eq p0, CakeValuation.pieceVal] using hu1_p1_le_p0
    obtain ⟨⟨ht_l, ht_r⟩, hvt1⟩ :=
      ho.eval_cutIn_spec 1 hl0 hlr hr1 hu1_p1_nonneg hu1_p1_le_lr
    set t := (RWQuery.cutIn (1 : Fin 3) l r (u1 p1)).eval oracle
    set Y := scTrimmedPieces c1 c2 p0 t
    -- Player 1 values Y p0 and Y p1 equally at u1 p1, dominating every Y k.
    have hv1_Y_p0 : (v 1).pieceVal (Y p0) = u1 p1 := by
      simpa only [Y, scTrimmedPieces, ↓reduceIte, CakeValuation.pieceVal] using hvt1
    have hv1_Y_p1 : (v 1).pieceVal (Y p1) = u1 p1 :=
      (congrArg (v 1).pieceVal (ite_eq_right hp0_ne_p1.symm)).trans (congrFun hu1_eq p1).symm
    have hv1_Y_le (k : Fin 3) : (v 1).pieceVal (Y k) ≤ u1 p1 := by
      rcases eq_or_ne k p0 with rfl | hk0
      · exact hv1_Y_p0.le
      · have hbo : bestOther u1 p0 = p1 := ite_eq_right (not_not.mpr rfl)
        simpa only [Y, scTrimmedPieces, hk0, ↓reduceIte, hu1_eq] using
          (hbo ▸ le_bestOther_of_ne u1 hk0 : u1 k ≤ u1 p1)
    -- Player 2 chooses favorite Y q2.
    set u2 := (evalThree 2 Y).eval oracle
    set q2 := topChoice u2
    have hv2_Y_le (k : Fin 3) : (v 2).pieceVal (Y k) ≤ (v 2).pieceVal (Y q2) := by
      simpa only [u2, q2, eval_evalThree ho 2 Y] using le_topChoice u2 k
    set q1 : Fin 3 := if q2 = p0 then p1 else p0
    have hq21 : q2 ≠ q1 := by by_cases hq : q2 = p0 <;> simp [q1, hq, hp0_ne_p1]
    have hv1_Y_q1 : (v 1).pieceVal (Y q1) = u1 p1 := by
      by_cases hq : q2 = p0 <;> simp only [q1, hq, ↓reduceIte, hv1_Y_p1, hv1_Y_p0]
    set q0 := thirdFin3 q2 q1
    -- Player 0 always receives an untrimmed piece Y q0 = X q0 of value 1 / 3.
    have hq0_ne_p0 : q0 ≠ p0 := by
      by_cases hq : q2 = p0
      · exact hq ▸ thirdFin3_ne_left hq21
      · exact (ite_eq_right hq : q1 = p0) ▸ thirdFin3_ne_right hq21
    have hv0_Y_q0 : (v 0).pieceVal (Y q0) = 1 / 3 := by
      simpa only [Y, scTrimmedPieces, hq0_ne_p0, ↓reduceIte] using hv0_X q0
    -- Phase 2: pd divides [t, r] into three equal pieces of value w_pd / 3.
    set pa : Fin 3 := if q2 = p0 then 2 else 1
    set pd : Fin 3 := if q2 = p0 then 1 else 2
    have hw_pd_eq : (RWQuery.evalAsk pd t r).eval oracle = v pd t r := ho.eval_evalAsk pd t r
    set w_pd := (RWQuery.evalAsk pd t r).eval oracle
    have ht0 : 0 ≤ t := hl0.trans ht_l
    obtain ⟨hu1_t, hu2_u1, hu2_r, hv_pd_T⟩ :=
      cutIntoThirds_spec ho pd ht0 ht_r hr1 (α := w_pd / 3) (by rw [hw_pd_eq])
    have hu1_r : (RWQuery.cutIn pd t r (w_pd / 3)).eval oracle ≤ r := hu2_u1.trans hu2_r
    set u_cut1 := (RWQuery.cutIn pd t r (w_pd / 3)).eval oracle
    set u_cut2 := (RWQuery.cutIn pd u_cut1 r (w_pd / 3)).eval oracle
    set T_sub := scTrimSubPieces t u_cut1 u_cut2 r
    have hT_nonneg (i m : Fin 3) : 0 ≤ (v i).pieceVal (T_sub m) := by
      fin_cases m
      exacts [(v i).val_nonneg ht0 (hu1_r.trans hr1),
        (v i).val_nonneg (ht0.trans hu1_t) (hu2_r.trans hr1),
        (v i).val_nonneg ((ht0.trans hu1_t).trans hu2_u1) hr1]
    -- Phase 2 choices: pa chooses first (s_pa), Player 0 second (s_0), pd last (s_pd).
    set w_pa := (evalThree pa T_sub).eval oracle
    set w_0 := (evalThree 0 T_sub).eval oracle
    set s_pa := topChoice w_pa
    set s_0 := bestOther w_0 s_pa
    have hspa0 : s_pa ≠ s_0 := (bestOther_ne w_0 s_pa).symm
    set s_pd := thirdFin3 s_pa s_0
    have hv_pa_T_le (m : Fin 3) : (v pa).pieceVal (T_sub m) ≤ (v pa).pieceVal (T_sub s_pa) := by
      simpa only [w_pa, s_pa, eval_evalThree ho pa T_sub] using le_topChoice w_pa m
    have hv0_T_pd_le_0 : (v 0).pieceVal (T_sub s_pd) ≤ (v 0).pieceVal (T_sub s_0) := by
      simpa only [w_0, eval_evalThree ho 0 T_sub, s_0, s_pd] using
        le_bestOther_of_ne w_0 (thirdFin3_ne_left hspa0)
    -- Irrevocable advantage of Player 0 over pa: Y p0 and T_sub 0, 1, 2 partition X p0.
    have hv0_irrevocable :
        (v 0).pieceVal (Y p0) + (v 0).pieceVal (T_sub s_pa) ≤ 1 / 3 := by
      have hT_012 : (v 0).pieceVal (T_sub 0) + (v 0).pieceVal (T_sub 1) +
          (v 0).pieceVal (T_sub 2) = v 0 t r := by
        dsimp only [T_sub, scTrimSubPieces, CakeValuation.pieceVal]
        linarith [(v 0).val_add ht0 hu1_t hu1_r hr1,
          (v 0).val_add (ht0.trans hu1_t) hu2_u1 hu2_r hr1]
      have hT_perm_sum := sum_three_of_ne hspa0 (fun m => (v 0).pieceVal (T_sub m))
      have hYp0_T : (v 0).pieceVal (Y p0) + v 0 t r = 1 / 3 := by
        simpa only [Y, scTrimmedPieces, ↓reduceIte, CakeValuation.pieceVal] using
          ((v 0).val_add hl0 ht_l ht_r hr1).trans (hv0_X p0)
      linarith [hT_nonneg 0 s_0, hT_nonneg 0 s_pd]
    set s1 : Fin 3 := if q2 = p0 then s_pd else s_pa
    set s2 : Fin 3 := if q2 = p0 then s_pa else s_pd
    -- Case split on who holds the trimmed piece: q2 = p0 vs q2 ≠ p0.
    have h1_T : ∀ m : Fin 3, (v 1).pieceVal (T_sub m) ≤ (v 1).pieceVal (T_sub s1) := fun m => by
      by_cases hq : q2 = p0 <;> simp only [pd, pa, s1, hq, ↓reduceIte] at hv_pd_T hv_pa_T_le ⊢
      · -- Subcase B1: Player 2 took the trimmed piece (pa = 2, pd = 1, q1 = p1 ≠ p0).
        rw [hv_pd_T m, hv_pd_T s_pd]
      · -- Subcase B2: Player 2 took an untrimmed piece, so Player 1 took Y p0 (pa = 1, pd = 2).
        exact hv_pa_T_le m
    have h2_T : ∀ m : Fin 3, (v 2).pieceVal (T_sub m) ≤ (v 2).pieceVal (T_sub s2) := fun m => by
      by_cases hq : q2 = p0 <;> simp only [pd, pa, s2, hq, ↓reduceIte] at hv_pd_T hv_pa_T_le ⊢
      · exact hv_pa_T_le m
      · rw [hv_pd_T m, hv_pd_T s_pd]
    have h0_other : ∀ (qk sk : Fin 3), (qk = p0 ∧ sk = s_pa) ∨ (qk ≠ p0 ∧ sk = s_pd) →
        (v 0).pieceVal (Y qk) + (v 0).pieceVal (T_sub sk) ≤
          (v 0).pieceVal (Y q0) + (v 0).pieceVal (T_sub s_0) := by
      rintro qk sk (⟨rfl, rfl⟩ | ⟨hne, rfl⟩)
      · linarith [hv0_Y_q0, hv0_irrevocable, hT_nonneg 0 s_0]
      · rw [hv0_Y_q0]
        simpa only [Y, scTrimmedPieces, scInitialPieces, hne, ↓reduceIte, hv0_X qk] using
          add_le_add le_rfl hv0_T_pd_le_0
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [scBuildTrimmed, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, CakeValuation.bundleVal_cons, CakeValuation.bundleVal_nil,
      add_zero]
    · exact le_rfl
    · exact h0_other q1 s1 (by by_cases hq : q2 = p0 <;> simp [q1, s1, hq, hp0_ne_p1.symm])
    · exact h0_other q2 s2 (by by_cases hq : q2 = p0 <;> simp [s2, hq])
    all_goals first
      | exact add_le_add ((hv1_Y_le _).trans_eq hv1_Y_q1.symm) (h1_T _)
      | exact add_le_add (hv2_Y_le _) (h2_T _)

/-- **Selfridge–Conway Proportionality Corollary:** under any valid Robertson–Webb oracle, every
player receives at least `1 / 3` of the cake according to their own valuation. -/
theorem isProportional_selfridgeConwayQ {v : Fin 3 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 3) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    (selfridgeConwayQ.eval oracle).IsProportional v :=
  (isEnvyFree_selfridgeConwayQ ho).isProportional (isValidPartition_selfridgeConwayQ oracle)

end Cslib.GameTheory.FairDivision
