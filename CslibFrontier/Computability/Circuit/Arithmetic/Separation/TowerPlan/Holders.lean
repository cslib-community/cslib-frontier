/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Moves
import Mathlib.Tactic.FinCases

/-!
# The tower plan: holders of units

The two nodes that hold the units with a target of the tower plan of [AnthropicVPVNP2026] (proof
of Theorem H.2; module `Nc.Tow.Ends`) are determined by the target (`Target.holders`): the ends of
an edge, the outer parties of a relay, or the chambers at a pair of places of a vertex. The units
of a channel of a move and the initial units are held by these nodes, unless they are done.

## Main definitions

* `Target.holders`: the two nodes that hold the units with a target.
* `channelHolders`, `initialHolders`: the nodes at the ends of a channel of a move, and of a
  string between two base parties.

## Main results

* `holders_stepTarget`: the units on a step of a route are held by the chambers of the step.
* `holders_initialTarget`, `holders_target`: the holders of the initial units and of the units of
  the channels of the moves are those of their targets.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "Start" and "One stage"); module `Nc.Tow.Ends`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}

/-- The nodes that hold the units of a channel of a move: the nodes at its two ends. -/
@[expose] noncomputable def channelHolders (ν : MoveChannel R ch FL) : Sym2 T.Node :=
  s(ν.1.party (ν.1.law.channelEnd ν.2 false), ν.1.party (ν.1.law.channelEnd ν.2 true))

/-- The nodes that hold the units of the string between two base parties. -/
@[expose] def initialHolders (ch : Fin A ↪ T.X 0) (a c : Fin A) : Sym2 T.Node :=
  s(.ofChamber (Nat.zero_le J) (ch a), .ofChamber (Nat.zero_le J) (ch c))

/-- The nodes that hold the units with a target. -/
@[expose] noncomputable def Target.holders (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) :
    Target T m A → Sym2 T.Node
  | .done => s(.root, .root)
  | .edge j e => s(.ofChamber (Nat.le_of_lt_succ j.2) (T.e0 e),
      .ofChamber (Nat.le_of_lt_succ j.2) (T.e1 e))
  | .relay x => s(x.party R ch .source, x.party R ch .sink)
  | .segment j i ω q => q.map fun f => .ofChamber j.2 ((T.chamberEquiv j.2 i).symm (ω, f))

/-- A step of a route before its end has units. -/
theorem stepTarget_ne_done {c c' γ : T.X 0} {s : ℕ} (hs : s < R.pl c c' γ) :
    (stepTarget R c c' γ s : Target T m A) ≠ .done := by
  obtain ⟨e, h1, -⟩ := R.exists_edge c c' γ hs
  simp [stepTarget, h1, Option.elim]

/-- The units on a step of a route are held by the chambers of the step. -/
theorem holders_stepTarget {c c' γ : T.X 0} {s : ℕ} (hs : s < R.pl c c' γ) :
    (stepTarget R c c' γ s : Target T m A).holders R ch =
      s(.ofChamber (Nat.zero_le J) (R.pn c c' γ s),
        .ofChamber (Nat.zero_le J) (R.pn c c' γ (s + 1))) := by
  obtain ⟨e, h1, h2, -⟩ := R.exists_edge c c' γ hs
  rw [stepTarget, h1]
  exact congrArg (Sym2.map (Tower.Node.ofChamber (Nat.zero_le J))) h2

/-- The initial units are held by the nodes of their target. -/
theorem holders_initialTarget {a c : Fin A} {k : ℕ} (hd : initialTarget R ch a c k ≠ .done) :
    (initialTarget R ch a c k).holders R ch = initialHolders ch a c := by
  unfold initialTarget at hd ⊢
  split_ifs at hd ⊢ with hac hs
  · exact absurd rfl hd
  · simp only [Target.holders, Relay.party, initialHolders, Routes.pn_zero]
    rfl
  · have hpos := R.pl_pos (fun hh => hac (ch.injective hh)) (batchChamber ch a k)
    have hle := (R.pl_le (ch a) (ch c) (batchChamber ch a k)).trans (R.length_path _ _ _)
    have h2 := R.pn_pl (ch a) (ch c) (batchChamber ch a k)
    rw [show R.pl (ch a) (ch c) (batchChamber ch a k) = 0 + 1 by omega] at h2
    rw [holders_stepTarget hpos, h2, Routes.pn_zero, initialHolders]

private theorem map_segment {j : ℕ} (hj : j < J) (i : Fin h) (c : T.X j) :
    (s(T.co i (T.hostOf i c), T.co i c) : Sym2 T.Fl).map (fun f =>
      Tower.Node.ofChamber hj ((T.chamberEquiv hj i).symm (T.πV (T.vx i c), f))) =
        s(.ofChamber hj (T.hostOf i c), .ofChamber hj (T.π c)) := by
  have h1 : (T.chamberEquiv hj i).symm (T.πV (T.vx i c), T.co i (T.hostOf i c)) = T.hostOf i c := by
    rw [← T.host_vx hj i (T.vx i c)]
    exact T.chamberEquiv_symm_vx_co hj i _
  have h2 : (T.chamberEquiv hj i).symm (T.πV (T.vx i c), T.co i c) = T.π c := by
    rw [← T.π_vx hj i c, ← T.π_co hj i c]
    exact T.chamberEquiv_symm_vx_co hj i _
  rw [Sym2.map_mk, h1, h2]

private theorem Relay.holders_target {x : Relay T m A} (hx : x.Occurs R ch) {d : Bool}
    (hd : x.target R ch d ≠ .done) : (x.target R ch d).holders R ch =
      s(x.party R ch (relayChannelEnd d false), x.party R ch (relayChannelEnd d true)) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · obtain ⟨-, hs⟩ := hx
    have hle := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
    cases d
    · exact holders_stepTarget (by omega)
    · simp only [target]
      split_ifs with hs2
      · rfl
      · have h2 := R.pn_pl (ch a) (ch c) γ
        rw [show R.pl (ch a) (ch c) γ = s.1 + 1 + 1 by omega] at h2
        rw [holders_stepTarget hs, h2]
        rfl
  · exact absurd rfl hd
  · cases d <;> fin_cases s
    · exact absurd rfl hd
    · exact map_segment j.2 (T.ty e) (T.e0 e)
    · exact congrArg (Sym2.map (Tower.Node.ofChamber j.2)) (T.π_ends j.2 e)
    · exact (map_segment j.2 (T.ty e) (T.e1 e)).trans Sym2.eq_swap
    · by_cases hh : T.hostOf (T.ty e) (T.e0 e) = T.π (T.e0 e)
      · refine (congrArg (Target.holders R ch) (ite_eq_right (not_not.2 hh))).trans ?_
        exact congrArg (fun c => s(Tower.Node.ofChamber j.2 c, .ofChamber j.2.le (T.e1 e)))
          hh.symm
      · exact congrArg (Target.holders R ch) (ite_eq_left hh)
    · rfl
    · by_cases hh : T.π (T.e1 e) = T.hostOf (T.ty e) (T.e1 e)
      · exact absurd (ite_eq_right (not_not.2 hh)) hd
      · exact congrArg (Target.holders R ch) (ite_eq_left hh)
    · exact absurd rfl hd
  · exact absurd rfl hd

private theorem holders_target_vertex (l : VertexMove FL) (ν : (FL.law l.kind).Channel) :
    ((Move.vertex l : Move R ch FL).target ν).holders R ch =
      channelHolders (⟨.vertex l, ν⟩ : MoveChannel R ch FL) := by
  set p := (T.nr l.stage.2 l.type).symm (l.vertex, FL.nearPair l.kind ν)
  have hp : T.nr l.stage.2 l.type p = (l.vertex, FL.nearPair l.kind ν) :=
    Equiv.apply_symm_apply _ _
  have h2 := (FL.place_channelEnd l.kind ν).trans
    ((T.nr_co l.stage.2 l.type p).trans (by rw [hp])).symm
  have e0 : (T.chamberEquiv l.stage.2 l.type).symm (l.vertex, T.co l.type (T.e0 p.1)) =
      T.e0 p.1 := by
    rw [← ((T.nr_vx0 l.stage.2 l.type p).trans (congrArg Prod.fst hp) :
      T.vx l.type (T.e0 p.1) = l.vertex)]
    exact T.chamberEquiv_symm_vx_co _ _ _
  have e1 : (T.chamberEquiv l.stage.2 l.type).symm (l.vertex, T.co l.type (T.e1 p.1)) =
      T.e1 p.1 := by
    rw [← ((T.nr_vx1 l.stage.2 l.type p).trans (congrArg Prod.fst hp) :
      T.vx l.type (T.e1 p.1) = l.vertex)]
    exact T.chamberEquiv_symm_vx_co _ _ _
  exact (congrArg₂ (fun x y => s(Tower.Node.ofChamber l.stage.2 x, .ofChamber l.stage.2 y))
    e0 e1).symm.trans (congrArg (Sym2.map fun f => Tower.Node.ofChamber l.stage.2
      ((T.chamberEquiv l.stage.2 l.type).symm (l.vertex, f))) h2).symm

/-- The units of a channel of a move are held by the nodes of their target. -/
theorem holders_target (ν : MoveChannel R ch FL) (hd : ν.1.target ν.2 ≠ .done) :
    (ν.1.target ν.2).holders R ch = channelHolders ν := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · exact Relay.holders_target hx hd
  · exact holders_target_vertex l ν

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
