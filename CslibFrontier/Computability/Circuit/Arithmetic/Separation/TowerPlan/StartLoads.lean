/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.FinCases

/-!
# The tower plan: loads of relays, and the loads after the start

The load of a target in the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules
`Nc.Tow.Load2` and `Nc.Tow.Load0`) is the number of initial units with that target plus the alive
units of the channels of the relays and of the law moves with that target (`load_eq_sum`). A relay
uses at most the load of its input, and each of its channels carries at most the units of the
relay. Following the targets of the channels backwards, the relays of the route of a batch of
initial units use at most the size of the batch (`moveCount_start_le`), and the relays of the way
of an edge through the next level use at most the units on the edge, and none if the type of the
edge is not the chosen one (`moveCount_middle_le`). The routes use every edge of the level `0` at
most `Uu` times, which bounds the loads after the start (`load_start_le`).

## Main definitions

* `relayAlive`: the alive units of a channel of a relay, and `0` if the relay is not a move.
* `batchSize`: the number of initial units of a batch.

## Main results

* `relayAlive_of_occurs`, `relayAlive_of_not_occurs`: the values of `relayAlive`.
* `load_eq_sum`, `load_eq_relay`: the load of a target, by the channels with that target.
* `stepTarget_ne_relay`, `stepTarget_ne_segment`, `stepTarget_ne_edge_succ`: the units on a step
  of a route are done or lie on an edge of the level `0`.
* `alive_le_moveCount`, `moveCount_relay_le`: a relay and its channels.
* `time_initialTarget_le`, `initialLoad_eq_zero`: the initial units have their targets within the
  start.
* `Relay.of_target_eq_relay_middle`: the channels that give units to the way of an edge.
* `batchSize_le`, `moveCount_start_le`: the batches and the relays of their routes.
* `moveCount_middle_le`, `relayAlive_middle_le`: the relays of the way of an edge.
* `relayAlive_inner_le`, `relayAlive_final_le`: the inner relays of an edge, and the relays after
  the last stage.
* `load_start_le`: the loads after the start.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "Start", pp. 46–47, and "One stage", p. 47); modules `Nc.Tow.Load2`,
  `Nc.Tow.Load0`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {lhat : ℕ}
  {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}

/-! ### Loads by channels -/

/-- The moves are the relays of the plan and the law moves. -/
private def moveEquiv : Move R ch FL ≃ {x : Relay T m A // x.Occurs R ch} ⊕ VertexMove FL where
  toFun
    | .relay x hx => .inl ⟨x, hx⟩
    | .vertex l => .inr l
  invFun
    | .inl x => .relay x.val x.property
    | .inr l => .vertex l
  left_inv mv := by cases mv <;> rfl
  right_inv y := by rcases y with _ | _ <;> rfl

variable (lhat n o) in
/-- The alive units of the channel `d` of the relay `x`, and `0` if `x` is not a move of the
plan. -/
noncomputable def relayAlive (x : Relay T m A) (d : Bool) : ℕ :=
  if hx : x.Occurs R ch then alive lhat n o ⟨.relay x hx, d⟩ else 0

/-- The alive units of a channel of a relay of the plan. -/
theorem relayAlive_of_occurs {x : Relay T m A} (hx : x.Occurs R ch) (d : Bool) :
    relayAlive lhat n o x d = alive lhat n o ⟨.relay x hx, d⟩ :=
  dite_eq_left hx

/-- A relay that is not a move of the plan has no alive units. -/
theorem relayAlive_of_not_occurs {x : Relay T m A} (hx : ¬ x.Occurs R ch) (d : Bool) :
    relayAlive lhat n o x d = 0 :=
  dite_eq_right hx

/-- The load of a target, by the initial units, the relays and the law moves. -/
theorem load_eq_sum (τ : Target T m A) : load lhat n o τ = initialLoad R ch lhat n τ +
    (∑ x, ∑ d, if x.target R ch d = τ then relayAlive lhat n o x d else 0) +
    ∑ l, ∑ c, if (Move.vertex l : Move R ch FL).target c = τ then
      alive lhat n o ⟨.vertex l, c⟩ else 0 := by
  rw [load, loadGiven, add_assoc, Fintype.sum_sigma, ← moveEquiv.symm.sum_comp,
    Fintype.sum_sum_type]
  congr 2
  set g : Relay T m A → ℕ := fun x =>
    ∑ d, if x.target R ch d = τ then relayAlive lhat n o x d else 0
  calc _ = ∑ x : {x : Relay T m A // x.Occurs R ch}, g x.val :=
        sum_congr rfl fun x _ => sum_congr rfl fun d _ => by
          simp only [relayAlive_of_occurs x.property]
          rfl
    _ = ∑ x, if x.Occurs R ch then g x else 0 := by
        rw [← sum_filter]
        exact (sum_subtype _ (fun x => by simp) g).symm
    _ = ∑ x, g x := sum_congr rfl fun x _ => ite_eq_left_iff.2 fun hx => by
        simp [g, relayAlive_of_not_occurs hx]

/-- The load of a target that no law move gives, by the initial units and the relays. -/
theorem load_eq_relay {τ : Target T m A}
    (hτ : ∀ (l : VertexMove FL) c, (Move.vertex l : Move R ch FL).target c ≠ τ) :
    load lhat n o τ = initialLoad R ch lhat n τ +
      ∑ x, ∑ d, if x.target R ch d = τ then relayAlive lhat n o x d else 0 := by
  simp [load_eq_sum, hτ]

/-- A load that the relays give through one channel only. -/
theorem load_le_relayAlive {τ : Target T m A}
    (hτ : ∀ (l : VertexMove FL) c, (Move.vertex l : Move R ch FL).target c ≠ τ)
    (y : Relay T m A) (dy : Bool) (hy : ∀ x d, x.target R ch d = τ →
      relayAlive lhat n o x d ≠ 0 → x = y ∧ d = dy) :
    load lhat n o τ ≤ initialLoad R ch lhat n τ + relayAlive lhat n o y dy := by
  rw [load_eq_relay hτ, ← Fintype.sum_prod_type']
  gcongr
  refine (sum_le_sum_of_ne_zero (t := {(y, dy)}) fun ⟨x, d⟩ _ hxd => ?_).trans ?_
  · rw [sum_singleton]
    split_ifs <;> simp
  · obtain ⟨rfl, rfl⟩ := hy x d (ite_ne_right_iff.1 hxd).1 (ite_ne_right_iff.1 hxd).2
    exact mem_singleton_self _

/-! ### Relays -/

/-- A channel of a relay carries at most the units of the relay. -/
theorem alive_le_moveCount (x : Relay T m A) (hx : x.Occurs R ch) (d : Bool) :
    alive lhat n o ⟨.relay x hx, d⟩ ≤ moveCount lhat n o (.relay x hx) := by
  simp only [alive, aliveGiven]
  split_ifs <;> omega

/-- A relay uses at most the load of its input. -/
theorem moveCount_relay_le (x : Relay T m A) (hx : x.Occurs R ch) :
    moveCount lhat n o (.relay x hx) ≤ load lhat n o x.input := by
  rw [moveCount_eq, countOfLoad]
  split_ifs <;> omega

/-- A bound for the units of a relay, if it is a move of the plan, bounds its channels. -/
private theorem relayAlive_le_of_moveCount_le {x : Relay T m A} {M : ℕ}
    (hM : ∀ hx : x.Occurs R ch, moveCount lhat n o (.relay x hx) ≤ M) (d : Bool) :
    relayAlive lhat n o x d ≤ M := by
  by_cases hx : x.Occurs R ch
  · exact (relayAlive_of_occurs hx d).trans_le ((alive_le_moveCount x hx d).trans (hM hx))
  · exact (relayAlive_of_not_occurs hx d).trans_le (Nat.zero_le _)

/-- A channel of a relay carries at most the load of the input of the relay. -/
private theorem relayAlive_le_load (x : Relay T m A) (d : Bool) :
    relayAlive lhat n o x d ≤ load lhat n o x.input :=
  relayAlive_le_of_moveCount_le (moveCount_relay_le x) d

/-- The units on a step of a route are done or lie on an edge of the level `0`. -/
@[simp]
theorem stepTarget_ne_relay {c c' γ : T.X 0} {s : ℕ} {y : Relay T m A} :
    stepTarget R c c' γ s ≠ .relay y := by
  unfold stepTarget
  cases (R.path c c' γ)[s]? <;> simp [Option.elim]

/-- The units on a step of a route are not end segments. -/
@[simp]
theorem stepTarget_ne_segment {c c' γ : T.X 0} {s : ℕ} {j : Fin J} {i : Fin h}
    {ω : T.V (j + 1) i} {q : Sym2 T.Fl} :
    (stepTarget R c c' γ s : Target T m A) ≠ .segment j i ω q := by
  unfold stepTarget
  cases (R.path c c' γ)[s]? <;> simp [Option.elim]

/-- The units on a step of a route do not lie on an edge of a later level. -/
@[simp]
theorem stepTarget_ne_edge_succ {c c' γ : T.X 0} {s : ℕ} {j : Fin J} {e : T.Ed (j + 1)} :
    (stepTarget R c c' γ s : Target T m A) ≠ .edge j.succ e := by
  unfold stepTarget
  cases (R.path c c' γ)[s]? <;> simp only [Option.elim, reduceCtorEq, ne_eq, not_false_eq_true]
  exact fun h => Fin.succ_ne_zero j (Target.edge.inj h).1.symm

private theorem stepTarget_eq_edge {c c' γ : T.X 0} {s : ℕ} {e : T.Ed 0} :
    (stepTarget R c c' γ s : Target T m A) = .edge 0 e ↔ (R.path c c' γ)[s]? = some e := by
  unfold stepTarget
  cases (R.path c c' γ)[s]? <;> simp only [Option.elim, reduceCtorEq, Option.some.injEq]
  exact ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

/-- Only the channel `true` of the previous step of a route gives units to a step of the
route. -/
private theorem Relay.of_target_eq_relay_start {x : Relay T m A} {d : Bool} {a c : Fin A}
    {γ : T.X 0} {s : Fin (2 * m)} (hx : x.target R ch d = .relay (.start a c γ s)) :
    ∃ s' : Fin (2 * m), x = .start a c γ s' ∧ d = true ∧ s.val = s'.val + 1 := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;> cases d <;>
    (try fin_cases s') <;> simp only [Relay.target] at hx <;> (try split_ifs at hx) <;>
    first | (cases hx; exact ⟨_, rfl, rfl, rfl⟩) | simp_all

/-- The relays that give units to a step of the way of an edge through the next level: the
first step to the second, or to the third if the host of the first end of the edge is its
image; the second step to the third, and the third to the fourth. -/
theorem Relay.of_target_eq_relay_middle {x : Relay T m A} {d : Bool} {j : Fin J} {e : T.Ed j}
    {s : Fin 4} (hx : x.target R ch d = .relay (.middle j e s)) : d = true ∧
      ((s = 1 ∧ x = .middle j e 0) ∨
      (s = 2 ∧ ((x = .middle j e 0 ∧ T.hostOf (T.ty e) (T.e0 e) = T.π (T.e0 e)) ∨
        x = .middle j e 1)) ∨
      (s = 3 ∧ x = .middle j e 2)) := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;> cases d <;>
    (try fin_cases s') <;> simp only [Relay.target] at hx <;> (try split_ifs at hx) <;>
    first | (cases hx; simp_all) | simp_all

/-- Only the relays of the routes give units to the edges of the level `0`. -/
private theorem Relay.of_target_eq_edge_zero {x : Relay T m A} {d : Bool} {e : T.Ed 0}
    (hx : x.target R ch d = .edge 0 e) : ∃ a c γ s, x = .start a c γ s := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;> cases d <;>
    (try fin_cases s') <;> simp only [Relay.target] at hx <;> (try split_ifs at hx) <;>
    first | exact ⟨_, _, _, _, rfl⟩ | exact absurd (Target.edge.inj hx).1 (Fin.succ_ne_zero _) |
      simp_all

/-- The units of a channel of a relay of a route that lie on an edge are on step `s` or, for
the channel `true` of the last relay, on step `s + 1`. -/
private theorem Relay.start_target_eq_edge {a c : Fin A} {γ : T.X 0} {s : Fin (2 * m)}
    {d : Bool} {e : T.Ed 0}
    (h : (Relay.start a c γ s : Relay T m A).target R ch d = .edge 0 e) :
    (R.path (ch a) (ch c) γ)[s.val + d.toNat]? = some e ∧
      (d = true → R.pl (ch a) (ch c) γ ≤ s.val + 2) := by
  have := (R.pl_le (ch a) (ch c) γ).trans (R.length_path (ch a) (ch c) γ)
  cases d
  · exact ⟨stepTarget_eq_edge.1 h, nofun⟩
  · simp only [Relay.target] at h
    split_ifs at h with hs
    exact ⟨stepTarget_eq_edge.1 h, fun _ => by omega⟩

/-! ### Initial units -/

variable (ch lhat n) in
/-- The number of initial units from `a` to `c` that are led through the chamber `γ`; there are
none if a base party has too many units. -/
@[expose] noncomputable def batchSize (a c : Fin A) (γ : T.X 0) : ℕ :=
  if InitialBound lhat n then ((range (n a c)).filter fun k => batchChamber ch a k = γ).card
  else 0

/-- The batches have equal sizes up to one. -/
theorem batchSize_le (a c : Fin A) (γ : T.X 0) :
    batchSize ch lhat n a c γ ≤ n a c / Fintype.card (T.X 0) + 1 := by
  have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨γ⟩
  unfold batchSize
  split_ifs
  · rw [filter_congr fun k _ => show _ ↔ k ≡ Fintype.equivFin (T.X 0) γ [MOD _] by
      rw [Nat.ModEq, Nat.mod_eq_of_lt (Fintype.equivFin (T.X 0) γ).is_lt, batchChamber,
        Equiv.symm_apply_eq, Fin.ext_iff], ← Nat.count_eq_card_filter_range,
      Nat.count_modEq_card _ hX]
    split_ifs <;> omega
  · exact Nat.zero_le _

/-- The initial units with a target are at most the batches that can have it. -/
private theorem initialLoad_le {τ : Target T m A} (p : Fin A → Fin A → T.X 0 → Prop)
    [∀ a c γ, Decidable (p a c γ)]
    (hp : ∀ a c k, initialTarget R ch a c k = τ → p a c (batchChamber ch a k)) :
    initialLoad R ch lhat n τ ≤
      ∑ a, ∑ c, ∑ γ, if p a c γ then batchSize ch lhat n a c γ else 0 := by
  unfold initialLoad batchSize
  split_ifs with hv
  · refine sum_le_sum fun a _ => sum_le_sum fun c _ => ?_
    rw [card_eq_sum_card_fiberwise fun k _ => mem_univ (batchChamber ch a k)]
    refine sum_le_sum fun γ _ => ?_
    split_ifs with hγ
    · exact card_le_card fun k hk => by
        simp only [mem_filter] at hk ⊢
        exact ⟨hk.1.1, hk.2⟩
    · refine (card_eq_zero.2 (filter_eq_empty_iff.2 fun k hk hkγ => hγ ?_)).le
      exact hkγ ▸ hp a c k (mem_filter.1 hk).2
  · simp

/-- The initial units are done, or their target is made by the end of the start. -/
theorem time_initialTarget_le {a c : Fin A} {k : ℕ} (hd : initialTarget R ch a c k ≠ .done) :
    (initialTarget R ch a c k).time ≤ 2 * m := by
  unfold initialTarget at *
  split_ifs at *
  · exact absurd rfl hd
  · simp [Target.time, Relay.time]
  · revert hd
    unfold stepTarget
    cases (R.path (ch a) (ch c) (batchChamber ch a k))[0]? <;> simp [Option.elim, Target.time]

/-- No initial units have a target that is made after the start. -/
theorem initialLoad_eq_zero {τ : Target T m A} (hd : τ ≠ .done) (hτ : 2 * m < τ.time) :
    initialLoad R ch lhat n τ = 0 :=
  Nat.eq_zero_of_le_zero <| (initialLoad_le (fun _ _ _ => False) fun a c k hk =>
    absurd (hk ▸ time_initialTarget_le (hk ▸ hd)) (by omega)).trans (by simp)

/-! ### The relays of a route -/

/-- The relays of a route are given at most the units of its batch. -/
private theorem load_relay_start_le (a c : Fin A) (γ : T.X 0) (s : Fin (2 * m)) :
    load lhat n o (.relay (.start a c γ s)) ≤ batchSize ch lhat n a c γ := by
  have hinit {s : Fin (2 * m)} : initialLoad R ch lhat n (.relay (.start a c γ s)) ≤
      if s.val = 0 then batchSize ch lhat n a c γ else 0 := by
    refine (initialLoad_le (fun a' c' γ' => a' = a ∧ c' = c ∧ γ' = γ ∧ s.val = 0)
      fun a' c' k hk => ?_).trans ?_
    · unfold initialTarget at hk
      split_ifs at hk
      · cases hk
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact absurd hk stepTarget_ne_relay
    · split_ifs with hs <;> simp [hs, ite_and, sum_ite_irrel]
  obtain ⟨s, hs⟩ := s
  induction s with
  | zero =>
    rw [load_eq_relay fun _ _ => by simp [Move.target],
      sum_eq_zero fun x _ => sum_eq_zero fun d _ => ite_eq_right_iff.2 fun hx => by
        obtain ⟨s', -, -, h⟩ := Relay.of_target_eq_relay_start hx
        exact absurd h.symm (Nat.succ_ne_zero _)]
    exact hinit.trans_eq (ite_eq_left_iff.2 fun h => absurd rfl h)
  | succ s ih =>
    refine (load_le_relayAlive (fun _ _ => by simp [Move.target]) (.start a c γ ⟨s, by omega⟩)
      true fun x d hxd _ => ?_).trans ?_
    · obtain ⟨s', rfl, rfl, h⟩ := Relay.of_target_eq_relay_start hxd
      have hss : (⟨s, by omega⟩ : Fin (2 * m)) = s' := Fin.ext (Nat.succ.inj h)
      exact ⟨by rw [hss], rfl⟩
    · rw [(hinit.trans_eq (ite_eq_right_iff.2 fun h => absurd h s.succ_ne_zero)).antisymm
        (Nat.zero_le _), zero_add]
      exact (relayAlive_le_load _ _).trans (ih _)

/-- The relays of a route use at most the units of its batch. -/
theorem moveCount_start_le {a c : Fin A} {γ : T.X 0} {s : Fin (2 * m)}
    (hx : (Relay.start a c γ s).Occurs R ch) :
    moveCount lhat n o (.relay (.start a c γ s) hx) ≤ batchSize ch lhat n a c γ :=
  (moveCount_relay_le _ hx).trans (load_relay_start_le a c γ s)

/-! ### The way of an edge through the next level -/

/-- The relays of the way of an edge through the next level use at most the units on the edge,
and none if the type of the edge is not the chosen one. -/
theorem moveCount_middle_le {j : Fin J} {e : T.Ed j} {s : Fin 4}
    (hx : (Relay.middle j e s).Occurs R ch) :
    moveCount lhat n o (.relay (.middle j e s) hx) ≤
      if T.IsChosenType (edgeLoads (load lhat n o) j) (T.ty e) then
        load lhat n o (.edge j.castSucc e)
      else 0 := by
  set M := if T.IsChosenType (edgeLoads (load lhat n o) j) (T.ty e) then
    load lhat n o (.edge j.castSucc e) else 0
  have hA {s : Fin 4} (hs : ∀ hx, moveCount lhat n o (.relay (.middle j e s) hx) ≤ M)
      (d : Bool) : relayAlive lhat n o (.middle j e s) d ≤ M :=
    relayAlive_le_of_moveCount_le hs d
  have hstep {s : Fin 4} (hs : s ≠ 0) (s' : Fin 4) (hs' : ∀ x d, x.target R ch d =
      .relay (.middle j e s) → relayAlive lhat n o x d ≠ 0 → x = .middle j e s' ∧ d = true)
      (hM : relayAlive lhat n o (.middle j e s') true ≤ M) (hx) :
      moveCount lhat n o (.relay (.middle j e s) hx) ≤ M := by
    have hs0 : 0 < s.val := Fin.pos_iff_ne_zero.2 hs
    refine (moveCount_relay_le _ hx).trans ?_
    rw [Relay.input, ite_eq_right hs]
    refine (load_le_relayAlive (fun _ _ => by simp [Move.target]) _ _ hs').trans ?_
    rw [initialLoad_eq_zero (by simp) (by simp only [Target.time, Relay.time]; omega), zero_add]
    exact hM
  have h0 (hx : (Relay.middle j e 0 : Relay T m A).Occurs R ch) :
      moveCount lhat n o (.relay _ hx) ≤ M := by
    rw [moveCount_eq, countOfLoad]
    simp [M, Relay.Active, Relay.input]
  have h1 := hstep (s := 1) (by decide) 0 (fun x d hxd _ => by
    rcases Relay.of_target_eq_relay_middle hxd with ⟨rfl, ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;>
      first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)) (hA h0 true)
  have h2 := hstep (s := 2) (by decide)
    (if T.hostOf (T.ty e) (T.e0 e) = T.π (T.e0 e) then 0 else 1) (fun x d hxd hd => by
      rcases Relay.of_target_eq_relay_middle hxd with ⟨rfl, ⟨h, -⟩ | ⟨-, ⟨rfl, hh⟩ | rfl⟩ | ⟨h, -⟩⟩
      · exact absurd h (by decide)
      · exact ⟨by rw [ite_eq_left hh], rfl⟩
      · by_cases hx : (Relay.middle j e 1).Occurs R ch
        · exact ⟨by rw [ite_eq_right (hx.1 rfl)], rfl⟩
        · exact absurd (relayAlive_of_not_occurs hx true) hd
      · exact absurd h (by decide)) (by split_ifs; exacts [hA h0 true, hA h1 true])
  have h3 := hstep (s := 3) (by decide) 2 (fun x d hxd _ => by
    rcases Relay.of_target_eq_relay_middle hxd with ⟨rfl, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩⟩ <;>
      first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)) (hA h2 true)
  fin_cases s
  exacts [h0 hx, h1 hx, h2 hx, h3 hx]

/-- The channels of the relays of the way of an edge carry at most the units on the edge, and
none if the type of the edge is not the chosen one. -/
theorem relayAlive_middle_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (d : Bool) :
    relayAlive lhat n o (.middle j e s) d ≤
      if T.IsChosenType (edgeLoads (load lhat n o) j) (T.ty e) then edgeLoads (load lhat n o) j e
      else 0 := by
  rw [edgeLoads_of_lt _ (by omega)]
  exact relayAlive_le_of_moveCount_le moveCount_middle_le d

/-- The channels of an inner relay carry at most the units on its edge, and none if its type is
not the chosen one. -/
theorem relayAlive_inner_le (j : Fin J) (i : Fin h) (e : T.Ed j) (d : Bool) :
    relayAlive lhat n o (.inner j i e) d ≤
      if T.IsChosenType (edgeLoads (load lhat n o) j) i then edgeLoads (load lhat n o) j e
      else 0 := by
  rw [edgeLoads_of_lt _ (by omega)]
  exact relayAlive_le_of_moveCount_le (fun _ => (moveCount_eq _).le) d

/-- The channels of a relay after the last stage carry at most the units on its edge. -/
theorem relayAlive_final_le (e : T.Ed J) (d : Bool) :
    relayAlive lhat n o (.final e) d ≤ edgeLoads (load lhat n o) J e := by
  rw [edgeLoads_of_lt _ J.lt_succ_self]
  exact relayAlive_le_of_moveCount_le (moveCount_relay_le _) d

/-! ### The loads after the start -/

/-- The steps of a route over an edge: the initial units of its batch lie on its first step if
the route ends there, and the channels of its relays whose units lie on an edge lie on different
steps. -/
private theorem steps_le (a c : Fin A) (γ : T.X 0) (e : T.Ed 0) :
    (if a ≠ c ∧ R.pl (ch a) (ch c) γ ≤ 1 ∧ (R.path (ch a) (ch c) γ)[0]? = some e then 1 else 0) +
      ∑ s, ∑ d, (if (Relay.start a c γ s).Occurs R ch ∧
        (Relay.start a c γ s : Relay T m A).target R ch d = .edge 0 e then 1 else 0) ≤
      if a = c then 0 else (R.path (ch a) (ch c) γ).count e := by
  by_cases hac : a = c
  · simp [hac, Relay.Occurs]
  have hP := R.pl_pos (ch.injective.ne hac) γ
  have hPL := R.pl_le (ch a) (ch c) γ
  rw [ite_eq_right hac]
  by_cases hP1 : R.pl (ch a) (ch c) γ ≤ 1
  · rw [sum_eq_zero fun s _ => sum_eq_zero fun d _ => ite_eq_right_iff.2 fun h =>
      absurd h.1.2 (by omega), add_zero]
    split_ifs with h
    · exact List.count_pos_iff.2 (List.mem_of_getElem? h.2.2)
    · exact Nat.zero_le _
  rw [ite_eq_right fun h => hP1 h.2.1, zero_add, ← Fintype.sum_prod_type', sum_boole,
    Nat.cast_id]
  set L := R.path (ch a) (ch c) γ
  calc _ ≤ ((univ.filter fun i : Fin L.length => L[i] = e).map Fin.valEmbedding).card := by
        refine card_le_card_of_injOn (fun y => (y.fst : ℕ) + y.snd.toNat) (fun y hy => ?_)
          fun y hy y' hy' h => ?_
        · obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1
            (Relay.start_target_eq_edge (mem_filter.1 hy).2.2).1
          exact mem_map.2 ⟨⟨_, hlt⟩, mem_filter.2 ⟨mem_univ _, heq⟩, rfl⟩
        · obtain ⟨⟨-, h1⟩, h2⟩ := (mem_filter.1 hy).2
          obtain ⟨⟨-, h1'⟩, h2'⟩ := (mem_filter.1 hy').2
          have h3 := (Relay.start_target_eq_edge h2).2
          have h3' := (Relay.start_target_eq_edge h2').2
          obtain ⟨s, d⟩ := y
          obtain ⟨s', d'⟩ := y'
          dsimp only at h h1 h1' h3 h3'
          cases d <;> cases d' <;>
            simp only [Bool.toNat_false, Bool.toNat_true, true_implies, Prod.mk.injEq, Fin.ext_iff,
              Bool.false_eq_true, and_true, and_false] at h h3 h3' ⊢ <;> omega
    _ = L.count e := by
        rw [card_map]
        exact (List.Vector.count_toList e ⟨L, rfl⟩).symm

/-- The units on an edge of the level `0`, by the batches and the uses of the edge by their
routes. -/
private theorem load_edge_zero_le (e : T.Ed 0) : load lhat n o (.edge 0 e) ≤
    ∑ a, ∑ c, ∑ γ, if a = c then 0 else
      batchSize ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e := by
  rw [load_eq_relay (τ := .edge 0 e) fun l c h => Fin.succ_ne_zero _ (Target.edge.inj h).1,
    ← Fintype.sum_prod_type']
  calc _ ≤ (∑ a, ∑ c, ∑ γ, if a ≠ c ∧ R.pl (ch a) (ch c) γ ≤ 1 ∧
          (R.path (ch a) (ch c) γ)[0]? = some e then batchSize ch lhat n a c γ else 0) +
        ∑ a, ∑ c, ∑ γ, batchSize ch lhat n a c γ * ∑ s, ∑ d,
          if (Relay.start a c γ s).Occurs R ch ∧
            (Relay.start a c γ s : Relay T m A).target R ch d = .edge 0 e then 1 else 0 := by
        gcongr ?_ + ?_
        · refine initialLoad_le _ fun a c k hk => ?_
          have := (R.pl_le (ch a) (ch c) (batchChamber ch a k)).trans (R.length_path _ _ _)
          unfold initialTarget at hk
          split_ifs at hk with hac hs
          exact ⟨hac, by omega, stepTarget_eq_edge.1 hk⟩
        · refine (sum_le_sum_of_ne_zero (t := univ.image
            fun (⟨⟨a, c, γ, s⟩, d⟩ : (Fin A × Fin A × T.X 0 × Fin (2 * m)) × Bool) =>
              (Relay.start a c γ s, d)) fun ⟨x, d⟩ _ hxd => ?_).trans
            ((sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans ?_)
          · simp only [Fintype.sum_prod_type, mul_sum]
            gcongr with a _ c _ γ _ s _ d _
            split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, zero_le]
            · exact (relayAlive_le_load _ _).trans (load_relay_start_le a c γ s)
            · exact (relayAlive_of_not_occurs (fun hx => h2 ⟨hx, h1⟩) d).le
          · obtain ⟨a, c, γ, s, rfl⟩ := Relay.of_target_eq_edge_zero (ite_ne_right_iff.1 hxd).1
            exact mem_image.2 ⟨((a, c, γ, s), d), mem_univ _, rfl⟩
    _ ≤ _ := by
        simp only [← sum_add_distrib]
        refine sum_le_sum fun a _ => sum_le_sum fun c _ => sum_le_sum fun γ _ => ?_
        have := Nat.mul_le_mul_left (batchSize ch lhat n a c γ)
          (steps_le (R := R) (ch := ch) a c γ e)
        simpa only [mul_add, mul_ite, mul_one, mul_zero] using this

/-- The batches on an edge of the level `0`, by the uses of the edge by the routes. -/
private theorem sum_batchSize_le (e : T.Ed 0) :
    (∑ a, ∑ c, ∑ γ, if a = c then 0 else
      batchSize ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) ≤
      Uu * (lhat / Fintype.card (T.X 0) + 2 * A) := by
  set w : Fin A → T.X 0 → ℕ := fun a γ => (R.rt (ch a) γ).count e
  have hw : ∑ a, ∑ γ, w a γ ≤ Uu :=
    ((sum_map univ ch fun c => ∑ γ, (R.rt c γ).count e).symm.trans_le
      (sum_le_sum_of_subset (subset_univ _))).trans (R.use e)
  have hB (a : Fin A) (γ : T.X 0) : ∑ c, (if c = a then 0 else
      batchSize ch lhat n a c γ + batchSize ch lhat n c a γ) ≤
        lhat / Fintype.card (T.X 0) + 2 * A := by
    by_cases hv : InitialBound lhat n
    · have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨γ⟩
      calc _ ≤ ∑ c, ((if c = a then 0 else n a c + n c a) / Fintype.card (T.X 0) + 2) :=
            sum_le_sum fun c _ => by
              have := batchSize_le (ch := ch) (lhat := lhat) (n := n) a c γ
              have := batchSize_le (ch := ch) (lhat := lhat) (n := n) c a γ
              have := Nat.div_add_div_le_add_div (x := n a c) (y := n c a)
                (z := Fintype.card (T.X 0))
              split_ifs
              exacts [Nat.zero_le _, by omega]
        _ ≤ (∑ c, if c = a then 0 else n a c + n c a) / Fintype.card (T.X 0) + 2 * A := by
              rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
              gcongr
              rw [Nat.le_div_iff_mul_le hX, sum_mul]
              exact sum_le_sum fun c _ => Nat.div_mul_le_self _ _
        _ ≤ lhat / Fintype.card (T.X 0) + 2 * A := by gcongr; exact hv a
    · simp [batchSize, hv]
  calc _ = ∑ a, ∑ γ, w a γ * ∑ c, (if c = a then 0 else
        batchSize ch lhat n a c γ + batchSize ch lhat n c a γ) := by
        have h1 (a c : Fin A) (γ : T.X 0) : (if a = c then 0 else
            batchSize ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) =
            (if a = c then 0 else batchSize ch lhat n a c γ * w a γ) +
              if a = c then 0 else batchSize ch lhat n a c γ * w c γ := by
          split_ifs
          · rfl
          · rw [Routes.path_def, List.count_append, List.count_reverse, mul_add]
        simp only [h1, sum_add_distrib, mul_sum]
        rw [sum_comm (s := univ) (t := univ) (f := fun a c => ∑ γ,
          if a = c then 0 else batchSize ch lhat n a c γ * w c γ), ← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        simp only [← sum_add_distrib]
        rw [sum_comm]
        refine sum_congr rfl fun γ _ => sum_congr rfl fun c _ => ?_
        by_cases h : c = a
        · subst h
          simp
        · rw [ite_eq_right (Ne.symm h), ite_eq_right h, ite_eq_right h]
          ring
    _ ≤ ∑ a, ∑ γ, w a γ * (lhat / Fintype.card (T.X 0) + 2 * A) := by
        gcongr with a _ γ _
        exact hB a γ
    _ ≤ Uu * (lhat / Fintype.card (T.X 0) + 2 * A) := by
        simp only [← sum_mul]
        gcongr

/-- **The loads after the start** ([AnthropicVPVNP2026], Theorem H.2, proof, "Start",
pp. 46–47): an edge of the level `0` carries at most `Uu * (lhat / |X 0| + 2 * A)` alive units,
where every base party has at most `lhat` initial units (otherwise there are none) and the routes
use every edge at most `Uu` times. -/
theorem load_start_le (e : T.Ed 0) :
    load lhat n o (.edge 0 e) ≤ Uu * (lhat / Fintype.card (T.X 0) + 2 * A) :=
  (load_edge_zero_le e).trans (sum_batchSize_le e)

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
