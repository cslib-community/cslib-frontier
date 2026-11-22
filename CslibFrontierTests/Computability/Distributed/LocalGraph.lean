/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.LocalGraph.Coloring
import CslibFrontier.Computability.Distributed.LocalGraph.LubyMIS

/-! Synchronous general-graph `LOCAL` model, covering-map impossibility, deterministic
`(Δ + 1)`-coloring, and Luby's randomized `MIS` protocols (checked as an ordinary `module` client):

* `decide`-checked executions of `BroadcastProtocol` (including `seq`, `mapOutput`, `comapInput`,
  and `toPortProtocol`) and `PortProtocol` on `cycleGraph 6`, `cycleGraph 3`, and asymmetric
  port-numbered graphs, verifying fiber state equality and exercising asymmetric port conventions.
* Boundary witnesses on both sides of `GraphCovering` and `PortCovering`: positive instances
  (`C₆ → C₃`, `bipartiteDoubleCover`, `K₃,₃`) alongside negative boundary witnesses (`C₄ → K₂`
  violating neighborhood injectivity, and a single-vertex port swap on `C₆` breaking `PortCovering`
  and enabling 1-round anonymous symmetry breaking).
* `decide`-checked runs and boundary witnesses for `firstFreeColor`, `greedyColorReduction`,
  `kwBound` / `kwCompressProtocol` (including fixed low colors, recolored high colors, and the
  `m = Δ + 1` fixed point), and `deltaPlusOneColoring` (on `cycleGraph 6`, on an irregular graph
  with degree-`0` and degree-`1` vertices below `Δ = 3`, and at `Δ = 0` on an edgeless graph).
* `decide`-checked executions and non-vacuity instantiations for both randomized `LOCAL` `MIS`
  variants: 2-round-per-phase `priorityProtocol` / `localPriorityMIS` and `1 + 2 = 3`-round
  `liveDegreeProtocol` / `coinResolveProtocol` / `coinLubyMIS` (including `d_H = 0` isolated live
  vertices, asymmetric `(d_H, uid)` tie-breaking between equal-degree marked neighbors, concrete
  `isGoodVertex` witnesses, edge-contraction bounds, and `|V| ^ (-c)` tail bounds). -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.LocalGraph

open Cslib Cslib.Algorithms.Lean Cslib.Distributed.LocalGraph SimpleGraph
open scoped ENNReal

/-! ### 1. `BroadcastProtocol`, `PortProtocol`, and covering-map boundary witnesses -/

/-- One-round broadcast protocol computing the sum of neighbor inputs plus `10 * own`. -/
def weightedNbrSum : BroadcastProtocol ℕ ℕ ℕ ℕ :=
  BroadcastProtocol.fullInfo id (fun _ own ms => 10 * own + ms.sum) id

-- Under uniform input `1` on `C₆` and `C₃`, every vertex has degree `2`, so round-1 outputs equal
-- `10 * 1 + 2 = 12` on both graphs and agree along `cycleDoubleCoverMap`.
example :
    (List.finRange 6).map (weightedNbrSum.run (cycleGraph 6) (fun _ => 1) 1) =
      [12, 12, 12, 12, 12, 12] ∧
    (List.finRange 3).map (weightedNbrSum.run (cycleGraph 3) (fun _ => 1) 1) =
      [12, 12, 12] := by
  decide

-- Sequential composition `seq_run`: running `weightedNbrSum` for 1 round followed by itself for
-- 1 round on distinct inputs `0..5` on `C₆` matches two separate 1-round invocations.
example :
    (List.finRange 6).map
      ((weightedNbrSum.seq 1 weightedNbrSum).run (cycleGraph 6) Fin.val 2) =
    (List.finRange 6).map
      (weightedNbrSum.run (cycleGraph 6)
        (weightedNbrSum.run (cycleGraph 6) Fin.val 1) 1) := by
  decide

-- `toPortProtocol` agrees round-by-round with `BroadcastProtocol` on `cycleGraphPortNumbering`.
example (r : ℕ) (u : Fin 6) :
    weightedNbrSum.toPortProtocol.run (cycleGraphPortNumbering 3) Fin.val r u =
      weightedNbrSum.run (cycleGraph 6) Fin.val r u :=
  weightedNbrSum.toPortProtocol_run (cycleGraphPortNumbering 3) Fin.val r u

/-- Boundary witness for `PortProtocol.state_succ`: a port-sensitive protocol where each node sends
`10 * portIdx + 1` out port `portIdx` and records `100 * incoming(0) + incoming(1)` on degree-`2`
vertices. If `PortProtocol.state_succ` mistakenly read sender port `i` instead of the sender's own
incident port `N.port w ⟨u, _⟩`, the symmetric vs. reversed port tests below would disagree. -/
def portProbe : PortProtocol Unit ℕ ℕ ℕ where
  init _ _ := 0
  send _ _ _ p := 10 * p.val + 1
  recv _ d _ inc :=
    if h : d = 2 then 100 * inc ⟨0, by omega⟩ + inc ⟨1, by omega⟩ else 0
  output s := s

-- Under the oriented `cycleGraphPortNumbering 0` on `C₃`, a neighbor across local port `0`
-- (`u + 1`) sees `u` on its port `1` (sending `11`), while `u - 1` across port `1` sees `u` on its
-- port `0` (sending `1`), so every vertex computes `100 * 11 + 1 = 1101`.
example :
    (List.finRange 3).map (portProbe.run (cycleGraphPortNumbering 0) (fun _ => ()) 1) =
      [1101, 1101, 1101] := by
  decide

/-- Asymmetric port numbering on `C₆` obtained by swapping ports `0` and `1` at vertex `0` only. -/
def twistedC6PortNumbering : PortNumbering (cycleGraph 6) where
  port u :=
    if h : u = 0 then
      (cycleGraphPortNumbering 3).port u |>.trans
        (Equiv.swap ⟨0, h ▸ by decide⟩ ⟨1, h ▸ by decide⟩)
    else
      (cycleGraphPortNumbering 3).port u

-- Boundary witness: `cycleDoubleCoverMap` is a `GraphCovering` from `C₆` to `C₃`, yet swapping
-- ports at vertex `0` breaks `PortCovering` AND allows anonymous 1-round symmetry breaking via
-- `portProbe` (neighbors `1` and `5` of `0` receive swapped port tags `1111` and `101` vs `1101`).
example :
    ¬ PortCovering twistedC6PortNumbering (cycleGraphPortNumbering 0) cycleDoubleCoverMap := by
  intro hcov
  have hp := hcov.port_val_eq 0 ⟨1, by decide⟩
  change 0 = 1 at hp
  omega

example :
    (List.finRange 6).map (portProbe.run twistedC6PortNumbering (fun _ => ()) 1) =
      [111, 1111, 1101, 1101, 1101, 101] := by
  decide

example : ElectsUniqueLeader
    ((PortProtocol.mk (fun _ (_ : Unit) => 0) (portProbe.send) (portProbe.recv)
      (fun s => decide (s = 101))).run twistedC6PortNumbering (fun _ => ()) 1) := by
  rw [electsUniqueLeader_iff_card_eq_one]
  decide

-- Boundary witness on `GraphCovering`: the parity map `Fin 4 → Fin 2` (`i ↦ i % 2`) from `C₄` onto
-- `K₂` (`completeGraph (Fin 2)`) is surjective and preserves adjacency, yet is NOT a
-- `GraphCovering` because vertex `0`'s two neighbors `1` and `3` map to the same vertex `1`.
example : ¬ GraphCovering (cycleGraph 4) (completeGraph (Fin 2))
    (fun i : Fin 4 => ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩) := by
  intro hcov
  have h1 : (1 : Fin 4) ∈ (cycleGraph 4).neighborSet 0 := by decide
  have h3 : (3 : Fin 4) ∈ (cycleGraph 4).neighborSet 0 := by decide
  have heq : (⟨(1 : Fin 4).val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) =
      ⟨(3 : Fin 4).val % 2, Nat.mod_lt _ (by decide)⟩ := by decide
  have h13 : (1 : Fin 4) = 3 := hcov.injOn_neighborSet 0 h1 h3 heq
  exact absurd h13 (by decide)

-- Checked impossibility instantiations on `C₆`, `bipartiteDoubleCover C₃`, and `K₃,₃`.
example (B₁ : BroadcastProtocol Unit ℕ ℕ Bool) (B₂ : BroadcastProtocol Unit ℕ ℕ (Fin 2)) (r : ℕ) :
    ¬ ElectsUniqueLeader (B₁.run (cycleGraph 6) (fun _ => ()) r) ∧
    ¬ (cycleGraph 6).IsProperColoring (B₂.run (cycleGraph 6) (fun _ => ()) r) :=
  ⟨B₁.not_electsUniqueLeader_cycleGraph_six () r, B₂.not_twoColoring_cycleGraph_six () r⟩

example (P : PortProtocol Unit ℕ ℕ Bool) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run (cycleGraphPortNumbering 3) (fun _ => ()) r) :=
  P.not_electsUniqueLeader_cycleGraphPortNumbering_six () r

example (P : PortProtocol Unit ℕ ℕ (Fin 2)) (r : ℕ) :
    ¬ (cycleGraph 6).IsProperColoring (P.run (cycleGraphPortNumbering 3) (fun _ => ()) r) :=
  P.not_twoColoring_cycleGraphPortNumbering_six () r

example (P : PortProtocol Unit ℕ ℕ (Fin 2)) (r : ℕ) :
    (bipartiteDoubleCover (cycleGraph 3)).Colorable 2 ∧
    ¬ (bipartiteDoubleCover (cycleGraph 3)).IsProperColoring
      (P.run (cycleGraphPortNumbering 0).bipartiteDoubleCover (fun _ => ()) r) :=
  ⟨bipartiteDoubleCover_colorable_two (cycleGraph 3),
    PortProtocol.not_isProperColoring_bipartiteDoubleCover (cycleGraphPortNumbering 0)
      not_cycleGraph_three_colorable_two P () r⟩

example (P : PortProtocol Unit ℕ ℕ Bool) (Q : PortProtocol Unit ℕ ℕ (Fin 2)) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run k33PortNumbering (fun _ => ()) r) ∧
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsProperColoring
      (Q.run k33PortNumbering (fun _ => ()) r) :=
  ⟨P.not_electsUniqueLeader_k33PortNumbering () r,
    Q.not_isProperColoring_k33PortNumbering () r⟩

/-! ### 2. Deterministic `(Δ + 1)`-coloring building blocks and boundary witnesses -/

-- `firstFreeColor` picks the smallest unused color in `{0, …, Δ}`.
example :
    firstFreeColor 3 ({0, 2} : Finset ℕ) = 1 ∧
    firstFreeColor 2 ({0, 1} : Finset ℕ) = 2 ∧
    firstFreeColor 0 (∅ : Finset ℕ) = 0 := by
  decide

/-- Monotone proper `6`-coloring `[0, 1, 2, 3, 4, 5]` of `C₆` (`Δ = 2`). -/
def c6Init6 : Fin 6 → ℕ := ![0, 1, 2, 3, 4, 5]

-- Three rounds of `greedyColorReduction 2` peel off colors `5 → 4 → 3` one round at a time,
-- reaching the proper `3`-coloring `[0, 1, 2, 1, 0, 1]` of `C₆`.
example :
    (List.finRange 6).map ((greedyColorReduction 2).run (cycleGraph 6) c6Init6 1) =
      [0, 1, 2, 3, 4, 1] ∧
    (List.finRange 6).map ((greedyColorReduction 2).run (cycleGraph 6) c6Init6 2) =
      [0, 1, 2, 3, 0, 1] ∧
    (List.finRange 6).map ((greedyColorReduction 2).run (cycleGraph 6) c6Init6 3) =
      [0, 1, 2, 1, 0, 1] := by
  decide

-- Non-vacuity check of `greedyColorReduction_run` on `C₆` with `Δ = 2, q = 6, r = 3`.
example :
    (∀ u v, (cycleGraph 6).Adj u v →
      (greedyColorReduction 2).run (cycleGraph 6) c6Init6 3 u ≠
        (greedyColorReduction 2).run (cycleGraph 6) c6Init6 3 v) ∧
    ∀ u, (greedyColorReduction 2).run (cycleGraph 6) c6Init6 3 u < max (6 - 3) (2 + 1) :=
  greedyColorReduction_run (cycleGraph 6) (by decide) (by decide) (by decide) 3

-- Kuhn–Wattenhofer palette compression bounds for `Δ = 2`: `6 → 5 → 4 → 3 → 3` (stabilizing at
-- `Δ + 1 = 3`).
example :
    kwBound 2 6 = 5 ∧ kwBound 2 5 = 4 ∧ kwBound 2 4 = 3 ∧ kwBound 2 3 = 3 ∧
    (2 + 1 ≤ kwBound 2 6 ∧ kwBound 2 6 < 6) := by
  exact ⟨rfl, rfl, rfl, rfl, kwBound_lt (by decide)⟩

-- Boundary witness for `kwCompressProtocol 2 6` on `C₆`: colors `< 5` stay unchanged, while
-- vertex `5` (`own = 5 ≥ kwBound 2 6 = 5`) recolors into block `{0, 1, 2}` avoiding `{4, 0}`.
example :
    (List.finRange 6).map ((kwCompressProtocol 2 6).run (cycleGraph 6) c6Init6 1) =
      [0, 1, 2, 3, 4, 1] := by
  decide

example :
    (∀ u v, (cycleGraph 6).Adj u v →
      (kwCompressProtocol 2 6).run (cycleGraph 6) c6Init6 1 u ≠
        (kwCompressProtocol 2 6).run (cycleGraph 6) c6Init6 1 v) ∧
    ∀ u, (kwCompressProtocol 2 6).run (cycleGraph 6) c6Init6 1 u < kwBound 2 6 :=
  kwCompressProtocol_run (cycleGraph 6) (by decide) (by decide) (by decide)

-- Full `deltaPlusOneColoring 2 6` run on `C₆` (`Δ = 2, C = 6`, `deltaPlusOneRounds 2 6 = 34`):
-- produces a verified proper `Fin 3`-coloring from unique IDs `Fin.val`.
example :
    deltaPlusOneRounds 2 6 = 34 ∧
    deltaPlusOneRounds 2 6 ≤ 2 * Nat.logStar 6 + 10 * 2 ^ 2 + 1 :=
  ⟨by decide, deltaPlusOneRounds_le (by decide) 6⟩

example :
    (cycleGraph 6).IsProperColoring
      ((deltaPlusOneColoring 2 6).run (cycleGraph 6) Fin.val (deltaPlusOneRounds 2 6)) :=
  deltaPlusOneColoring_isProperColoring (cycleGraph 6) (by decide) Fin.val_injective
    (fun u => u.isLt) le_rfl

/-- Irregular 4-vertex graph with degrees `2, 1, 1, 0` (edge `{0, 1}`, edge `{0, 2}`, isolated `3`)
tested under upper bound `Δ = 3` to exercise `nbrUIDs[i]? = none` slots on low-degree and isolated
vertices. -/
def irregularGraph4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v => (u = 0 ∧ (v = 1 ∨ v = 2))

instance : DecidableRel irregularGraph4.Adj := by
  unfold irregularGraph4
  infer_instance

example :
    irregularGraph4.maxDegree ≤ 3 ∧
    irregularGraph4.IsProperColoring
      ((deltaPlusOneColoring 3 4).run irregularGraph4 Fin.val (deltaPlusOneRounds 3 4)) := by
  refine ⟨by decide, deltaPlusOneColoring_isProperColoring irregularGraph4 (by decide)
    Fin.val_injective (fun u => u.isLt) le_rfl⟩

-- Boundary witness at `Δ = 0` on the edgeless graph `⊥ : SimpleGraph (Fin 3)`:
-- `deltaPlusOneRounds 0 3 = 1 + 2 + 0 = 3` rounds produce the unique proper `Fin 1`-coloring.
example :
    deltaPlusOneRounds 0 3 = 3 ∧
    (⊥ : SimpleGraph (Fin 3)).IsProperColoring
      ((deltaPlusOneColoring 0 3).run (⊥ : SimpleGraph (Fin 3)) Fin.val 3) ∧
    (⊥ : SimpleGraph (Fin 3)).Colorable 1 :=
  ⟨by decide,
    deltaPlusOneColoring_isProperColoring (⊥ : SimpleGraph (Fin 3)) (by decide)
      Fin.val_injective (fun u => u.isLt) (by decide),
    ⟨deltaPlusOneGraphColoring (⊥ : SimpleGraph (Fin 3)) (by decide)
      Fin.val_injective (fun u => u.isLt) (r := 3) (by decide)⟩⟩

/-! ### 3. Luby's randomized `MIS` in `LOCAL`: Variant A and Variant B -/

-- Variant A (`priorityProtocol`): concrete 2-round execution on `C₄` with identity ranking
-- `0 < 1 < 2 < 3` selects vertex `0` in phase `0`, deactivates `{0, 1, 3}`, and selects `{0, 2}`
-- (a maximal independent set of `C₄`) after phase `1` (`4` synchronous `LOCAL` rounds).
example :
    let ranks : Fin 4 → ℕ → ℕ := fun v _ => v.val
    (List.finRange 4).map (priorityProtocol.run (cycleGraph 4) ranks 2) =
      [true, false, false, false] ∧
    (List.finRange 4).map (priorityProtocol.run (cycleGraph 4) ranks 4) =
      [true, false, true, false] := by
  decide

-- Non-vacuity instantiations of Variant A theorems on `C₄`.
example :
    (∀ S ∈ (ProbComp.eval (localPriorityMIS (cycleGraph 4) 4)).support,
      Maximal (cycleGraph 4).IsIndepSet (S : Set (Fin 4))) ∧
    (ProbComp.eval
      (localPriorityMIS (cycleGraph 4) ((1 + 2) * Nat.clog 2 (Fintype.card (Fin 4)) + 1))
      ).toOuterMeasure {S | ¬ Maximal (cycleGraph 4).IsIndepSet (S : Set (Fin 4))} ≤
        ((Fintype.card (Fin 4) : ℝ≥0∞) ^ 1)⁻¹ :=
  ⟨fun _ hS => maximal_of_mem_support_localPriorityMIS (cycleGraph 4) (by decide) hS,
    toOuterMeasure_not_maximal_localPriorityMIS_le_inv_pow (cycleGraph 4) 1⟩

-- Variant B (`liveDegreeProtocol` & `coinResolveProtocol`) boundary witness on `irregularGraph4`:
-- Suppose `s` has `chosen = {2}` and `live = {1, 3}` on `K₂ ⊕ isolated`, or test on
-- `irregularGraph4` with `s = LubyMIS.init` (`live = univ`, degrees `[2, 1, 1, 0]`):
-- * isolated vertex `3` has live degree `0` and `markProb = 1`;
-- * adjacent vertices `0` (deg `2`) and `1` (deg `1`) both marked `true`: higher-degree `0` wins
--   over `1` (`coinJoiners = {0, 3}`), deactivating `{0, 1, 2, 3}` in a single 3-round phase!
example :
    let s : LubyMIS.State (Fin 4) := LubyMIS.init
    (List.finRange 4).map
      (liveDegreeProtocol.run irregularGraph4 (fun v => decide (v ∈ s.live)) 1) = [2, 1, 1, 0] ∧
    markProb irregularGraph4 s 3 = 1 ∧
    markProb irregularGraph4 s 0 = 1 / 4 ∧
    markProb irregularGraph4 s 1 = 1 / 2 := by
  have hd3 : (LubyMIS.liveGraph irregularGraph4 (LubyMIS.init (V := Fin 4)).live).degree 3 = 0 := by
    decide
  have hd0 : (LubyMIS.liveGraph irregularGraph4 (LubyMIS.init (V := Fin 4)).live).degree 0 = 2 := by
    decide
  have hd1 : (LubyMIS.liveGraph irregularGraph4 (LubyMIS.init (V := Fin 4)).live).degree 1 = 1 := by
    decide
  have hm3 : (3 : Fin 4) ∈ (LubyMIS.init (V := Fin 4)).live := by decide
  have hm0 : (0 : Fin 4) ∈ (LubyMIS.init (V := Fin 4)).live := by decide
  have hm1 : (1 : Fin 4) ∈ (LubyMIS.init (V := Fin 4)).live := by decide
  refine ⟨by decide, ?_, ?_, ?_⟩
  · unfold markProb; dsimp only; simp only [hm3, hd3, ↓reduceIte]
  · unfold markProb; dsimp only; rw [ite_eq_left hm0, hd0]; norm_num
  · unfold markProb; dsimp only; rw [ite_eq_left hm1, hd1]; norm_num

-- Equal-degree asymmetric UID tie-breaking witness on `K₂` (`completeGraph (Fin 2)`):
-- both vertices have live degree `1`; when both flip `marked = true`, `uid = Fin.val` (`0 < 1`)
-- selects `1` (`coinJoiners = {1}`) rather than dropping both endpoints, and `coinResolveProtocol`
-- outputs `chosen = [false, true], live = [false, false]` after 2 rounds.
example :
    let G := completeGraph (Fin 2)
    let s : LubyMIS.State (Fin 2) := LubyMIS.init
    let m : Fin 2 → Bool := fun _ => true
    let inp : Fin 2 → CoinResolveInput := fun v =>
      { uid := v.val
        chosen := false
        live := true
        liveDeg := liveDegreeProtocol.run G (fun _ => true) 1 v
        marked := m v }
    coinJoiners G s Fin.val m = {1} ∧
    (List.finRange 2).map (coinResolveProtocol.run G inp 2) =
      [{ chosen := false, live := false }, { chosen := true, live := false }] := by
  decide

-- Concrete `isGoodVertex` check and non-vacuity of Variant B probabilistic bounds on `C₃`:
-- every vertex of `C₃` has `2` live neighbors of degree `2`, so `∑ 1 / (2 * 2) = 1 / 2 ≥ 1 / 6`.
theorem c3_zero_isGoodVertex :
    isGoodVertex (cycleGraph 3) LubyMIS.init (0 : Fin 3) := by
  unfold isGoodVertex
  dsimp only
  have hnbr : (LubyMIS.liveGraph (cycleGraph 3) (LubyMIS.init (V := Fin 3)).live).neighborFinset 0 =
      {1, 2} := by decide
  have hd1 : (LubyMIS.liveGraph (cycleGraph 3) (LubyMIS.init (V := Fin 3)).live).degree 1 = 2 := by
    decide
  have hd2 : (LubyMIS.liveGraph (cycleGraph 3) (LubyMIS.init (V := Fin 3)).live).degree 2 = 2 := by
    decide
  rw [hnbr, Finset.sum_pair (by decide), hd1, hd2]
  norm_num

example :
    (1 / 36 : ℝ) ≤
      ((ProbComp.eval (sampleMarks (cycleGraph 3) LubyMIS.init)).toOuterMeasure
        {m | (0 : Fin 3) ∉ (coinStep (cycleGraph 3) LubyMIS.init Fin.val m).live}).toReal ∧
    (1 : ℝ) / (2 * Fintype.card (Fin 3)) ≤
      ((ProbComp.eval (coinPhase (cycleGraph 3) Fin.val LubyMIS.init)).toOuterMeasure
        {t | t.live.card < (LubyMIS.init (V := Fin 3)).live.card}).toReal ∧
    72 * ∑' t, ProbComp.eval (coinPhase (cycleGraph 3) Fin.val LubyMIS.init) t *
        (LubyMIS.liveEdges (cycleGraph 3) t : ℝ≥0∞) ≤
      71 * (LubyMIS.liveEdges (cycleGraph 3) LubyMIS.init : ℝ≥0∞) ∧
    (ProbComp.eval
      (localCoinLubyMIS (cycleGraph 3) Fin.val
        (50 * (1 + 2) * Nat.clog 2 (Fintype.card (Fin 3)) + 1))).toOuterMeasure
      {S | ¬ Maximal (cycleGraph 3).IsIndepSet (S : Set (Fin 3))} ≤
        ((Fintype.card (Fin 3) : ℝ≥0∞) ^ 1)⁻¹ :=
  ⟨one_div_36_le_prob_removed_of_isGoodVertex (cycleGraph 3) c3_zero_isGoodVertex,
    inv_two_mul_card_le_prob_live_lt (cycleGraph 3) (by decide) Fin.val,
    seventyTwo_mul_expect_liveEdges_coinPhase_le (cycleGraph 3) Fin.val_injective LubyMIS.init,
    toOuterMeasure_not_maximal_localCoinLubyMIS_le_inv_pow (cycleGraph 3) Fin.val_injective 1⟩

end CslibFrontierTests.Distributed.LocalGraph
