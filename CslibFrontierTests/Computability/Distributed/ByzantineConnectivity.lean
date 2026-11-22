/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ByzantineGraph.Connectivity

/-! General-graph synchronous Byzantine agreement and the `2t + 1` vertex-connectivity bound
(checked as a `module` client with ordinary imports): non-vacuity on edgeless graphs with `Empty`
messages, `ownInput` on one process, supergraph and complete-graph (`G = ⊤`) bridges with
executable `om1` runs, cut-vertex impossibility on the `Fin 5` bowtie graph (`n = 5 > 3`, `t = 1`,
`κ = 1 < 3`) contrasted with `t = 0` solvability, `2`-cut impossibility on the `Fin 6` cycle
(`n = 6 > 3`, `t = 1`, `κ = 2 < 3`), uniqueness of `K₄` on four processes for `t = 1`, and concrete
`decide` executions plus full verification of `purifiedOM` on `K₅` minus an edge (`Fin 5`, `n = 5`,
`κ = 3`, non-complete) against an equivocating traitor. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ByzantineConnectivity

open Cslib.Distributed Cslib.Distributed.ByzantineGraph

/-! ### Edgeless graphs, `Empty` messages, and single-process agreement -/

/-- A silent protocol with `Empty` message type on the edgeless graph `⊥` over `Fin 2`. -/
def silentEmpty : GraphProtocol (⊥ : SimpleGraph (Fin 2)) Bool Empty where
  init _ b := b
  send _ _ _ _ hij := False.elim hij
  update _ _ s _ := s
  output _ s := s

-- `adv` is indexed only by actual edges of `⊥`, so `Empty` messages introduce no vacuity:
-- `silentEmpty` fails even fault-free (`t = 0`) agreement on `Fin 2`.
example : ¬ silentEmpty.SolvesByzantineAgreement 0 5 :=
  silentEmpty.not_solvesByzantineAgreement_of_not_isVertexConnected (by decide) fun hconn => by
    obtain ⟨_, hc⟩ := SimpleGraph.isVertexConnected_one.mp hconn
    obtain ⟨w⟩ := hc.preconnected 0 1
    cases w with
    | cons hadj _ => exact hadj

-- On a single process, `ownInput` solves Byzantine agreement on `⊥` against any fault bound.
example : (GraphProtocol.ownInput (⊥ : SimpleGraph (Fin 1))).SolvesByzantineAgreement 7 4 :=
  GraphProtocol.solvesByzantineAgreement_ownInput _ 7 4

/-! ### Complete-graph bridge (`G = ⊤`) and uniqueness of `K₄` on four processes -/

/-- `Byzantine.om1` restricted to `GraphProtocol ⊤` on `Fin 4`. -/
def graphOM1 : GraphProtocol (⊤ : SimpleGraph (Fin 4)) (Byzantine.OM1State (Fin 4))
    (Fin 4 → Bool) :=
  GraphProtocol.ofProtocol (Byzantine.om1 (Fin 4))

example : graphOM1.SolvesByzantineAgreement 1 2 :=
  (GraphProtocol.solvesByzantineAgreement_ofProtocol_iff (Byzantine.om1 (Fin 4)) 1 2).mpr
    (Byzantine.solvesByzantineAgreement_om1 (by decide) le_rfl)

-- Round-trip, fault-monotonicity, and independent-universe checks on `toProtocol` and
-- `exists_solvesByzantineAgreement_top_iff.{u, v, w}`.
example : graphOM1.toProtocol.SolvesByzantineAgreement 0 2 :=
  ((graphOM1.solvesByzantineAgreement_toProtocol_iff 1 2).mpr
    ((GraphProtocol.solvesByzantineAgreement_ofProtocol_iff (Byzantine.om1 (Fin 4)) 1 2).mpr
      (Byzantine.solvesByzantineAgreement_om1 (by decide) le_rfl))).mono (Nat.zero_le 1)

example : ∃ (S M : Type) (π : GraphProtocol (⊤ : SimpleGraph (Fin 4)) S M),
    π.SolvesByzantineAgreement 1 2 :=
  (exists_solvesByzantineAgreement_top_iff (P := Fin 4) 1 2).mpr
    ⟨_, _, Byzantine.om1 (Fin 4), Byzantine.solvesByzantineAgreement_om1 (by decide) le_rfl⟩

theorem top_iff_universes.{u, v, w} {P : Type u} [DecidableEq P] (t R : ℕ) :
    (∃ (S : Type v) (M : Type w) (π : GraphProtocol (⊤ : SimpleGraph P) S M),
        π.SolvesByzantineAgreement t R) ↔
      ∃ (S : Type v) (M : Type w) (π : Byzantine.Protocol P S M),
        π.SolvesByzantineAgreement t R :=
  exists_solvesByzantineAgreement_top_iff.{u, v, w} t R

-- Concrete execution of `graphOM1` against an equivocating process `3` on mixed inputs.
def topEquivocate : ℕ → ∀ j i : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj j i → Fin 4 → Bool :=
  fun r _ i _ _ => if r = 0 then decide (i = 0) else true

example : ∀ i : Fin 3,
    graphOM1.decision {3} topEquivocate ![true, false, true, false] 2 i.castSucc = false := by
  decide

-- On `Fin 4`, `⊤` (`K₄`) is the unique graph on which 1-resilient Byzantine agreement is solvable:
-- deleting an edge leaves a non-adjacent pair separated by the remaining 2 vertices (`2 ≤ 2 · 1`).
theorem fin4_exists_solves_one_iff_eq_top (G : SimpleGraph (Fin 4)) :
    (∃ (S M : Type) (R : ℕ) (π : GraphProtocol G S M), π.SolvesByzantineAgreement 1 R) ↔ G = ⊤ := by
  rw [exists_solvesByzantineAgreement_iff G 1]
  constructor
  · rintro (h1 | ⟨-, hconn⟩)
    · exfalso; revert h1; decide
    · ext u v
      simp only [SimpleGraph.top_adj]
      refine ⟨G.ne_of_adj, fun huv => ?_⟩
      by_contra hna
      let C : Finset (Fin 4) := (Finset.univ.erase u).erase v
      have huC : u ∉ C := by simp [C]
      have hvC : v ∉ C := by simp [C]
      have hsep : G.IsVertexSeparator u v C :=
        SimpleGraph.isVertexSeparator_of_forall_adj (S := {u}) (Finset.mem_singleton_self u)
          (by simp [huv.symm]) huC hvC fun x hx y hxy hy => by
            rw [Finset.mem_singleton] at hx
            have hyv : y ≠ v := fun h => hna (hx ▸ h ▸ hxy)
            have hyu : y ≠ u := by simpa using hy
            exact Finset.mem_erase.mpr ⟨hyv, Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ y⟩⟩
      have hcard : C.card ≤ 2 := by
        have h2 : (Finset.univ.erase u).card = 3 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
        have hv_mem : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
        rw [Finset.card_erase_of_mem hv_mem, h2]
      have hge := (SimpleGraph.isVertexConnected_iff_forall_isVertexSeparator.mp hconn).2 huv C hsep
      omega
  · rintro rfl
    refine Or.inr ⟨by decide, SimpleGraph.isVertexConnected_iff_forall_isVertexSeparator.mpr
      ⟨by rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]; exact_mod_cast (by decide : 3 < 4),
        fun u v huv T hT => ?_⟩⟩
    obtain ⟨huT, _, hwalk⟩ := SimpleGraph.isVertexSeparator_iff_forall_walk.mp hT
    obtain ⟨x, hx, hxT⟩ := hwalk (SimpleGraph.Adj.toWalk huv)
    simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact absurd hxT huT
    · exact absurd hxT hT.2.1

/-! ### Bowtie graph on `Fin 5`: `n = 5 > 3`, `κ = 1 < 3` (impossible for `t = 1`, `t = 0` ok) -/

/-- Two triangles `{0, 1, 2}` and `{2, 3, 4}` sharing cut-vertex `2`. -/
def bowtieAdj (u v : Fin 5) : Bool :=
  u != v && ((u.val ≤ 2 && v.val ≤ 2) || (2 ≤ u.val && 2 ≤ v.val))

def bowtie : SimpleGraph (Fin 5) where
  Adj u v := bowtieAdj u v = true
  symm := ⟨fun u v => by revert u v; decide⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel bowtie.Adj := fun u v => inferInstanceAs (Decidable (bowtieAdj u v = true))

-- Cut `{2}` (`|C| = 1 ≤ 2 · 1`) separates `{0, 1}` from `{3, 4}`: impossible for `t = 1` in any
-- number of rounds `R`, even though `n = 5 > 3 · 1`.
example {S M : Type} (π : GraphProtocol bowtie S M) (R : ℕ) :
    ¬ π.SolvesByzantineAgreement 1 R :=
  π.not_solvesByzantineAgreement_of_vertexCut (A := {0, 1}) (B := {3, 4}) (C := {2})
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

example : ¬ ∃ (S M : Type) (R : ℕ) (π : GraphProtocol bowtie S M),
    π.SolvesByzantineAgreement 1 R := by
  intro ⟨S, M, R, π, h⟩
  exact π.not_solvesByzantineAgreement_of_vertexCut (A := {0, 1}) (B := {3, 4}) (C := {2})
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) h

private theorem bowtie_reachable_two (u : Fin 5) : bowtie.Reachable 2 u :=
  match u with
  | 0 => (show bowtie.Adj 2 0 by decide).reachable
  | 1 => (show bowtie.Adj 2 1 by decide).reachable
  | 2 => SimpleGraph.Reachable.refl 2
  | 3 => (show bowtie.Adj 2 3 by decide).reachable
  | 4 => (show bowtie.Adj 2 4 by decide).reachable

-- Yet `bowtie` IS connected (`1`-vertex-connected), so fault-free (`t = 0`) agreement is solvable.
example : ∃ (S M : Type) (π : GraphProtocol bowtie S M), π.SolvesByzantineAgreement 0 4 := by
  rw [exists_solvesByzantineAgreement_of_le_iff bowtie 0 (by decide)]
  refine Or.inr ⟨by decide, SimpleGraph.isVertexConnected_one.mpr ⟨inferInstance, ?_⟩⟩
  exact ⟨fun u v => (bowtie_reachable_two u).symm.trans (bowtie_reachable_two v)⟩

/-! ### Cycle `C₆` on `Fin 6`: `n = 6 > 3`, `κ = 2 < 3` (impossible for `t = 1`) -/

def cycle6Adj (u v : Fin 6) : Bool :=
  (u.val + 1) % 6 == v.val || (v.val + 1) % 6 == u.val

def cycle6 : SimpleGraph (Fin 6) where
  Adj u v := cycle6Adj u v = true
  symm := ⟨fun u v => by revert u v; decide⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel cycle6.Adj := fun u v => inferInstanceAs (Decidable (cycle6Adj u v = true))

-- Cut `{1, 5}` (`|C| = 2 ≤ 2 · 1`) separates `{0}` from `{2, 3, 4}`: impossible for `t = 1`.
example {S M : Type} (π : GraphProtocol cycle6 S M) (R : ℕ) :
    ¬ π.SolvesByzantineAgreement 1 R :=
  π.not_solvesByzantineAgreement_of_vertexCut (A := {0}) (B := {2, 3, 4}) (C := {1, 5})
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Non-complete `3`-connected graph on `Fin 5`: `K₅` minus edge `{0, 1}` solves `t = 1` -/

/-- Complete graph on `Fin 5` with edge `{0, 1}` deleted (`n = 5`, `κ = 3`). -/
def k5MinusAdj (u v : Fin 5) : Bool :=
  u != v && !((u == 0 && v == 1) || (u == 1 && v == 0))

def k5Minus : SimpleGraph (Fin 5) where
  Adj u v := k5MinusAdj u v = true
  symm := ⟨fun u v => by revert u v; decide⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel k5Minus.Adj :=
  fun u v => inferInstanceAs (Decidable (k5MinusAdj u v = true))

-- `k5Minus` is strictly sparser than `⊤` (`0` and `1` cannot communicate directly).
example : ¬ k5Minus.Adj 0 1 ∧ k5Minus ≠ ⊤ :=
  ⟨by decide, fun h => (by decide : ¬ k5Minus.Adj 0 1) (h ▸ by decide)⟩

/-- Helper picking two distinct common neighbours in `k5Minus` when `u` and `v` are adjacent:
if both lie in `{2, 3, 4}` then `(0, 1)`, otherwise the two remaining universal vertices in
`{2, 3, 4} \ {u, v}`. -/
def twoCommonNbrs (u v : Fin 5) : Fin 5 × Fin 5 :=
  if 2 ≤ u.val && 2 ≤ v.val then (0, 1)
  else if u != 2 && v != 2 then (2, if u != 3 && v != 3 then 3 else 4)
  else (3, 4)

/-- Optional midpoint vertex of the `m`-th route from `u` to `v` in `k5Minus` (`none` for the
direct edge `u — v`). -/
def k5MinusMid (u v : Fin 5) (m : Fin 3) : Option (Fin 5) :=
  if k5MinusAdj u v then
    match m with
    | ⟨0, _⟩ => none
    | ⟨1, _⟩ => some (twoCommonNbrs u v).1
    | ⟨2, _⟩ => some (twoCommonNbrs u v).2
  else
    match m with
    | ⟨0, _⟩ => some 2
    | ⟨1, _⟩ => some 3
    | ⟨2, _⟩ => some 4

/-- Explicit 1- or 2-hop walk in `k5Minus` for path index `m : Fin 3`. -/
def k5MinusWalk (u v : Fin 5) (huv : u ≠ v) (m : Fin 3) : k5Minus.Walk u v :=
  if hadj : k5Minus.Adj u v then
    match k5MinusMid u v m with
    | none => hadj.toWalk
    | some w =>
      if hw : k5Minus.Adj u w ∧ k5Minus.Adj w v then .cons hw.1 hw.2.toWalk else hadj.toWalk
  else
    let w : Fin 5 := match m with | ⟨0, _⟩ => 2 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 4
    have hw : k5Minus.Adj u w ∧ k5Minus.Adj w v := by
      revert u v huv hadj m w
      decide
    .cons hw.1 hw.2.toWalk

private def k5MinusSupport (u v : Fin 5) (m : Fin 3) : List (Fin 5) :=
  match k5MinusMid u v m with
  | none => [u, v]
  | some w => [u, w, v]

private theorem k5MinusWalk_support :
    ∀ u v : Fin 5, ∀ huv : u ≠ v, ∀ m : Fin 3,
      (k5MinusWalk u v huv m).support = k5MinusSupport u v m := by
  decide

private theorem k5MinusSupport_nodup :
    ∀ u v : Fin 5, u ≠ v → ∀ m : Fin 3, (k5MinusSupport u v m).Nodup := by
  decide

private theorem k5MinusSupport_disjoint :
    ∀ u v : Fin 5, u ≠ v → ∀ i j : Fin 3, i ≠ j →
      ∀ x ∈ k5MinusSupport u v i, x ∈ k5MinusSupport u v j → x = u ∨ x = v := by
  decide

/-- Explicit computable routing system of `3` pairwise internally vertex-disjoint simple paths
between every ordered pair of distinct vertices in `K₅ - {0, 1}`. -/
def k5MinusRoutes : DisjointPaths k5Minus 3 where
  path := k5MinusWalk
  isPath u v huv m := SimpleGraph.Walk.IsPath.mk' <| by
    rw [k5MinusWalk_support]
    exact k5MinusSupport_nodup u v huv m
  internallyDisjoint u v huv i j hij x hxi hxj := by
    rw [k5MinusWalk_support] at hxi hxj
    exact k5MinusSupport_disjoint u v huv i j hij x hxi hxj

-- Full verification: `purifiedOM 1 k5MinusRoutes` solves 1-resilient Byzantine agreement on
-- `K₅ - {0, 1}` in `(1 + 1) * 4 = 8` physical rounds, and `k5Minus` is `3`-vertex-connected.
example : (purifiedOM 1 k5MinusRoutes).SolvesByzantineAgreement 1 8 :=
  solvesByzantineAgreement_purifiedOM 1 k5MinusRoutes (by simp) (by simp [epochLen])

example : k5Minus.IsVertexConnected 3 :=
  (isVertexConnected_iff_card_gt_and_nonempty_disjointPaths k5Minus 3).mpr
    ⟨by simp, ⟨k5MinusRoutes⟩⟩

/-- Equivocating Byzantine traitor on `k5Minus`: sends values depending on the physical round,
recipient, walk prefix length, and simulated `OM` path. -/
def k5MinusLiar : ℕ → ∀ j i : Fin 5, k5Minus.Adj j i → List (Fin 5) → List (Fin 5) → Bool :=
  fun r j i _ w τ => decide ((r + j.val + i.val + w.length + τ.length) % 2 = 0)

-- Concrete `decide` execution 1: unanimous `true` inputs on correct `{0, 1, 2, 3}`, apex `4`
-- faulty and equivocating; non-adjacent `0` and `1` both decide `true` after `8` physical rounds.
example : ∀ i : Fin 4,
    (purifiedOM 1 k5MinusRoutes).decision {4} k5MinusLiar (fun _ => true) 8 i.castSucc = true := by
  decide

-- Concrete `decide` execution 2: mixed inputs `![true, false, true, false, false]` with apex `4`
-- faulty and equivocating; all four correct processes agree on `false` after `8` physical rounds.
example : ∀ i : Fin 4,
    (purifiedOM 1 k5MinusRoutes).decision {4} k5MinusLiar ![true, false, true, false, false] 8
      i.castSucc = false := by
  decide

-- Concrete `decide` execution 3: mixed inputs `![false, false, true, false, true]` with apex `4`
-- faulty and equivocating; all four correct processes agree on `false` after `8` physical rounds.
example : ∀ i : Fin 4,
    (purifiedOM 1 k5MinusRoutes).decision {4} k5MinusLiar ![false, false, true, false, true] 8
      i.castSucc = false := by
  decide

-- Concrete `decide` execution 4: endpoint `0` faulty and equivocating on mixed inputs
-- `![false, true, true, false, true]`; all four correct processes `{1, 2, 3, 4}` agree on `true`.
example : ∀ i : Fin 4,
    (purifiedOM 1 k5MinusRoutes).decision {0} k5MinusLiar ![false, true, true, false, true] 8
      i.succ = true := by
  decide

-- Supergraph simulation (`k5Minus ≤ ⊤`) and rushing-adversary agreement on `k5Minus`.
example :
    ((purifiedOM 1 k5MinusRoutes).toSupergraph (le_top : k5Minus ≤ ⊤)).SolvesByzantineAgreement
      1 8 :=
  ((purifiedOM 1 k5MinusRoutes).solvesByzantineAgreement_toSupergraph_iff le_top 1 8).mpr
    (solvesByzantineAgreement_purifiedOM 1 k5MinusRoutes (by simp) (by simp [epochLen]))

example (strat : ℕ → (Fin 5 → PurifiedOMState (Fin 5)) →
    ∀ j i : Fin 5, k5Minus.Adj j i → List (Fin 5) → List (Fin 5) → Bool)
    (x : Fin 5 → Bool) :
    (purifiedOM 1 k5MinusRoutes).output 0
      ((purifiedOM 1 k5MinusRoutes).adaptiveState {4} strat x 8 0) =
    (purifiedOM 1 k5MinusRoutes).output 1
      ((purifiedOM 1 k5MinusRoutes).adaptiveState {4} strat x 8 1) :=
  ((solvesByzantineAgreement_purifiedOM 1 k5MinusRoutes (by simp) (by simp [epochLen])).adaptive
    (by decide) strat x).1 0 (by decide) 1 (by decide)

end CslibFrontierTests.Distributed.ByzantineConnectivity
