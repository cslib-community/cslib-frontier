/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Moves

/-!
# The tower plan: numbers of units

The numbers of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules
`Nc.Tow.Flow` and `Nc.Tow.Tree`) are functions of the numbers `n` of initial units and of the
outcomes `o` of the moves, the number of units on every channel. A unit is *alive* when the plan
still moves it: all units of a channel of a relay with the expected outcome, and all units but the
last of a channel of a law move with a short outcome. The *load* of a target is the number of
alive units with that target. A move uses a number of units that is determined by the loads of
the targets of earlier moves: a relay takes the load of its input when it is active, and a law
move takes the least number of units into which the end segments at its vertex fit, for the first
kind of law that attains it. Whether a relay of a stage is active depends on the type that the
loads of the edges of the stage (`edgeLoads`) choose in the tree of the tower
(`Cslib.CoveringTower.Tower.IsChosenType`).

## Main definitions

* `InitialBound`, `initialLoad`: the bound for the initial units, and the initial units with a
  target.
* `VertexMove.OutcomeShort`, `aliveGiven`, `loadGiven`: the outcomes of a law move that are
  short, the alive units of a channel and the load of a target when the numbers of units of the
  moves are given.
* `edgeLoads`, `Relay.Active`: the loads of the edges of every level, from the loads of the
  targets, and the relays that are used.
* `VertexMove.Fits`, `VertexMove.minUnits`, `VertexMove.IsPicked`: the choice of the number of
  units and of the kind of law at a vertex.
* `countOfLoad`, `countBefore`, `moveCount`, `alive`, `load`, `GoodOutcome`: the number of units
  of a move from the loads and by recursion on time, the alive units of a channel, the load of a
  target, and the outcomes of a move that are allowed.

## Main results

* `moveCount_eq`: the number of units of a move is determined by the loads.
* `VertexMove.kind_eq_of_isPicked`: the kind of law that is used at a vertex is unique.
* `moveCount_congr`, `load_congr`, `goodOutcome_congr`: the numbers depend on the outcomes of
  earlier moves only.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage"); modules `Nc.Tow.Flow`, `Nc.Tow.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}

section Loads

variable (L : Target T m A → ℕ)

/-- The loads of the edges of the level `j`, from the loads of the targets; `0` above the last
level. -/
@[expose] def edgeLoads (j : ℕ) : T.Ed j → ℕ :=
  fun e => if hj : j < J + 1 then L (.edge ⟨j, hj⟩ e) else 0

/-- The loads of the edges of a level `j ≤ J`. -/
theorem edgeLoads_of_lt {j : ℕ} (hj : j < J + 1) (e : T.Ed j) :
    edgeLoads L j e = L (.edge ⟨j, hj⟩ e) :=
  dite_eq_left hj

/-- The relay is used: an inner relay goes through the hosts of the chosen type of the loads of
the edges of its stage (`Cslib.CoveringTower.Tower.IsChosenType`), and the way through the next
level is taken by the edges of the chosen type. -/
@[expose] def Relay.Active : Relay T m A → Prop
  | .inner j i _ => T.IsChosenType (edgeLoads L j) i
  | .middle j e s => s = 0 → T.IsChosenType (edgeLoads L j) (T.ty e)
  | _ => True

instance : DecidablePred (Relay.Active L)
  | .start .. => inferInstanceAs (Decidable True)
  | .inner .. => inferInstanceAs (Decidable (Tower.IsChosenType ..))
  | .middle .. => inferInstanceAs (Decidable (_ → Tower.IsChosenType ..))
  | .final _ => inferInstanceAs (Decidable True)

variable {L} {L' : Target T m A → ℕ}

private theorem edgeLoads_congr {j : Fin J}
    (hL : ∀ e, L (.edge j.castSucc e) = L' (.edge j.castSucc e)) :
    edgeLoads L j = edgeLoads L' j :=
  funext fun e => (edgeLoads_of_lt L (by omega) e).trans
    ((hL e).trans (edgeLoads_of_lt L' (by omega) e).symm)

/-- Whether a relay is used depends on the loads of earlier targets only. -/
theorem Relay.active_congr {x : Relay T m A} (hL : ∀ τ, τ.time ≤ x.time m → L τ = L' τ) :
    x.Active L ↔ x.Active L' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact Iff.rfl
  · simp only [Relay.Active, edgeLoads_congr (j := j) fun e =>
      hL _ (by simp [Target.time, Relay.time])]
  · simp only [Relay.Active, edgeLoads_congr (j := j) fun e =>
      hL _ (by simp [Target.time, Relay.time])]
  · exact Iff.rfl

namespace VertexMove

variable {FL : VertexLaws F T} (L)

/-- The end segments at the vertex fit into `t` units at every slot of the law. -/
@[expose] def Fits (l : VertexMove FL) (t : ℕ) : Prop :=
  ∀ q : Sym2 T.Fl, ¬ q.IsDiag →
    L (.segment l.stage l.type l.vertex q) ≤ FL.slotCount l.kind q * t

instance (l : VertexMove FL) (t : ℕ) : Decidable (l.Fits L t) :=
  inferInstanceAs (Decidable (∀ q : Sym2 T.Fl, ¬ q.IsDiag → _ ≤ _))

/-- The number of units at a vertex: the least number into which the end segments fit, for some
kind of law. -/
@[expose] noncomputable def minUnits (l : VertexMove FL) : ℕ :=
  sInf {t | ∃ d, (l.withKind d).Fits L t}

/-- The kind of law that is used at a vertex: the first one into which the end segments fit with
the least number of units. -/
@[expose] def IsPicked (l : VertexMove FL) : Prop :=
  l.Fits L (l.minUnits L) ∧ ∀ d, Fintype.equivFin FL.Kind d < Fintype.equivFin FL.Kind l.kind →
    ¬ (l.withKind d).Fits L (l.minUnits L)

noncomputable instance (l : VertexMove FL) : Decidable (l.IsPicked L) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → ¬ _))

variable {L} {l : VertexMove FL}

private theorem minUnits_congr
    (hL : ∀ q, L (.segment l.stage l.type l.vertex q) = L' (.segment l.stage l.type l.vertex q)) :
    l.minUnits L = l.minUnits L' := by
  simp only [minUnits, Fits, withKind, hL]

/-- Which kind of law is used at a vertex depends on the end segments at the vertex only. -/
theorem isPicked_congr
    (hL : ∀ q, L (.segment l.stage l.type l.vertex q) = L' (.segment l.stage l.type l.vertex q)) :
    l.IsPicked L ↔ l.IsPicked L' := by
  simp only [IsPicked, minUnits, Fits, withKind, hL]

/-- The kind of law that is used at a vertex is unique. -/
theorem kind_eq_of_isPicked {d : FL.Kind} (h1 : l.IsPicked L) (h2 : (l.withKind d).IsPicked L) :
    l.kind = d := by
  rcases lt_trichotomy (Fintype.equivFin FL.Kind d) (Fintype.equivFin FL.Kind l.kind)
    with hlt | heq | hlt
  · exact absurd h2.1 (h1.2 d hlt)
  · exact ((Fintype.equivFin FL.Kind).injective heq).symm
  · exact absurd h1.1 (h2.2 l.kind hlt)

end VertexMove

end Loads

variable {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}

/-- The number of units of a move, from the loads: a relay that is used takes the units of its
input, and the law move of the kind that is used takes the number of units at its vertex. -/
@[expose] noncomputable def countOfLoad (L : Target T m A → ℕ) : Move R ch FL → ℕ
  | .relay x _ => if x.Active L then L x.input else 0
  | .vertex l => if l.IsPicked L then l.minUnits L else 0

private theorem countOfLoad_congr {L L' : Target T m A → ℕ} {mv : Move R ch FL}
    (hL : ∀ τ, τ.time ≤ mv.time → L τ = L' τ) :
    countOfLoad L mv = countOfLoad L' mv := by
  rcases mv with ⟨x, hx⟩ | l
  · simp only [countOfLoad, Relay.active_congr hL, hL _ x.time_input_le]
  · have h1 q : L (.segment l.stage l.type l.vertex q) = L' (.segment l.stage l.type l.vertex q) :=
      hL _ le_rfl
    simp only [countOfLoad, VertexMove.isPicked_congr h1, VertexMove.minUnits_congr h1]

variable (R ch) (lhat : ℕ) (n : Fin A → Fin A → ℕ)

/-- Every base party has at most `lhat` units at the beginning. -/
@[expose] def InitialBound : Prop := ∀ a, ∑ c, (if c = a then 0 else n a c + n c a) ≤ lhat

instance : Decidable (InitialBound lhat n) :=
  inferInstanceAs (Decidable (∀ a, ∑ c, (if c = a then 0 else n a c + n c a) ≤ lhat))

/-- The number of initial units with the target `τ`; there are none if a base party has too many
units. -/
@[expose] noncomputable def initialLoad (τ : Target T m A) : ℕ :=
  if InitialBound lhat n then
    ∑ a, ∑ c, ((range (n a c)).filter fun k => initialTarget R ch a c k = τ).card
  else 0

variable {R ch} (o : MoveChannel R ch FL → ℕ)

/-- The outcome of a law move is short for `t` units. -/
@[expose] def VertexMove.OutcomeShort (l : VertexMove FL) (t : ℕ) : Prop :=
  r * b * ∑ ν : (FL.law l.kind).Channel, o ⟨.vertex l, ν⟩ ^ 2 ≤ FL.lengthBound * t ^ 2

instance (l : VertexMove FL) (t : ℕ) : Decidable (l.OutcomeShort o t) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The number of alive units of a channel, if `t` units are given in its move: the units of a
channel of a relay if their number is `t`; all units but the last of a channel of a law move if
the outcome is short, and at most `t` of them otherwise. -/
@[expose] def aliveGiven : MoveChannel R ch FL → ℕ → ℕ
  | ⟨.relay x hx, ν⟩, t => if o ⟨.relay x hx, ν⟩ = t then t else 0
  | ⟨.vertex l, ν⟩, t => if l.OutcomeShort o t then o ⟨.vertex l, ν⟩ else min (o ⟨.vertex l, ν⟩) t

/-- The number of alive units with the target `τ`, if the moves use the numbers `N` of units. -/
@[expose] noncomputable def loadGiven (N : Move R ch FL → ℕ) (τ : Target T m A) : ℕ :=
  initialLoad R ch lhat n τ +
    ∑ ν : MoveChannel R ch FL, if ν.1.target ν.2 = τ then aliveGiven o ν (N ν.1) else 0

/-- The numbers of units of the moves with times less than `t`; the other moves have none. -/
noncomputable def countBefore : ℕ → Move R ch FL → ℕ
  | 0, _ => 0
  | t + 1, mv =>
    if mv.time = t then countOfLoad (loadGiven lhat n o (countBefore t)) mv
    else countBefore t mv

/-- The number of units of a move. -/
@[expose] noncomputable def moveCount (mv : Move R ch FL) : ℕ :=
  countBefore lhat n o (endTime J m) mv

/-- The number of alive units of a channel. -/
@[expose] noncomputable def alive (ν : MoveChannel R ch FL) : ℕ :=
  aliveGiven o ν (moveCount lhat n o ν.1)

/-- The load of a target: the number of alive units with the target `τ`. -/
@[expose] noncomputable def load (τ : Target T m A) : ℕ :=
  loadGiven lhat n o (moveCount lhat n o) τ

/-- The outcome of a move is good: exact for a relay; short, and with at least as many units on
every channel as the move uses, for a law move. -/
@[expose] def GoodOutcome : Move R ch FL → Prop
  | .relay x hx => ∀ ν : Bool, o ⟨.relay x hx, ν⟩ = moveCount lhat n o (.relay x hx)
  | .vertex l => l.OutcomeShort o (moveCount lhat n o (.vertex l)) ∧
      ∀ ν : (FL.law l.kind).Channel, moveCount lhat n o (.vertex l) ≤ o ⟨.vertex l, ν⟩

variable {lhat n o}

theorem aliveGiven_le (ν : MoveChannel R ch FL) (t : ℕ) : aliveGiven o ν t ≤ o ν := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩ <;> simp only [aliveGiven] <;> split_ifs <;> omega

/-- If no units are given in a move, none of the units of its channels are alive. -/
theorem aliveGiven_zero (hr : 0 < r) (hb : 0 < b) (ν : MoveChannel R ch FL) :
    aliveGiven o ν 0 = 0 := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · simp [aliveGiven]
  · simp only [aliveGiven]
    split_ifs with hs
    · exact (show ∀ ν' : (FL.law l.kind).Channel, o ⟨.vertex l, ν'⟩ = 0 by
        simpa [VertexMove.OutcomeShort, hr.ne', hb.ne', Finset.sum_eq_zero_iff] using hs) ν
    · exact Nat.min_zero _

@[simp]
theorem countBefore_zero (mv : Move R ch FL) : countBefore lhat n o 0 mv = 0 := by
  rfl

theorem countBefore_succ (t : ℕ) (mv : Move R ch FL) : countBefore lhat n o (t + 1) mv =
    if mv.time = t then
      countOfLoad (loadGiven lhat n o (countBefore lhat n o t)) mv
    else countBefore lhat n o t mv := by
  rfl

private theorem countBefore_of_le {t : ℕ} {mv : Move R ch FL} (ht : t ≤ mv.time) :
    countBefore lhat n o t mv = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [countBefore_succ, ite_eq_right (by omega)]; exact ih (by omega)

private theorem countBefore_of_lt {t : ℕ} {mv : Move R ch FL} (ht : mv.time < t) :
    countBefore lhat n o t mv = countOfLoad
      (loadGiven lhat n o (countBefore lhat n o mv.time)) mv := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [countBefore_succ]
    split_ifs with h1
    · rw [h1]
    · exact ih (by omega)

/-- The numbers of units of the moves before the time `t`. -/
theorem countBefore_eq (t : ℕ) (mv : Move R ch FL) : countBefore lhat n o t mv =
    if mv.time < t then moveCount lhat n o mv else 0 := by
  split_ifs with ht
  · rw [countBefore_of_lt ht, moveCount, countBefore_of_lt mv.time_lt_endTime]
  · exact countBefore_of_le (not_lt.1 ht)

private theorem loadGiven_countBefore {τ : Target T m A} {t : ℕ} (hτ : τ.time ≤ t) :
    loadGiven lhat n o (countBefore lhat n o t) τ = load lhat n o τ := by
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun ν _ => ?_)
  split_ifs with hν
  · have := hν ▸ ν.1.time_lt_time_target ν.2
    rw [countBefore_eq, ite_eq_left (by omega)]
  · rfl

/-- **The numbers of units**: the number of units of a move is determined by the loads. -/
theorem moveCount_eq (mv : Move R ch FL) : moveCount lhat n o mv =
    countOfLoad (load lhat n o) mv := by
  rw [moveCount, countBefore_of_lt mv.time_lt_endTime]
  exact countOfLoad_congr fun τ hτ => loadGiven_countBefore (o := o) hτ

section Causal

variable {o' : MoveChannel R ch FL → ℕ}

/-- The alive units of a channel depend on the outcome of its move only. -/
theorem aliveGiven_congr {ν : MoveChannel R ch FL}
    (hν : ∀ ν' : MoveChannel R ch FL, ν'.1 = ν.1 → o ν' = o' ν') (t : ℕ) :
    aliveGiven o ν t = aliveGiven o' ν t := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · simp only [aliveGiven, hν ⟨_, ν⟩ rfl]
  · have hν' (c : (FL.law l.kind).Channel) : o ⟨.vertex l, c⟩ = o' ⟨.vertex l, c⟩ :=
      hν ⟨.vertex l, c⟩ rfl
    have hs : l.OutcomeShort o t ↔ l.OutcomeShort o' t := by
      simp only [VertexMove.OutcomeShort, hν']
    simp only [aliveGiven, hν ⟨_, ν⟩ rfl]
    exact if_congr hs rfl rfl

private theorem loadGiven_congr (hr : 0 < r) (hb : 0 < b) {N : Move R ch FL → ℕ}
    (hN : ∀ ν : MoveChannel R ch FL, N ν.1 ≠ 0 → o ν = o' ν) (τ : Target T m A) :
    loadGiven lhat n o N τ = loadGiven lhat n o' N τ := by
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun ν _ => ?_)
  split_ifs
  · by_cases h0 : N ν.1 = 0
    · rw [h0, aliveGiven_zero hr hb, aliveGiven_zero hr hb]
    · exact aliveGiven_congr (fun ν' h => hN ν' (h ▸ h0)) _
  · rfl

private theorem loadGiven_countBefore_congr (hr : 0 < r) (hb : 0 < b) {t : ℕ}
    (ho : ∀ ν : MoveChannel R ch FL, ν.1.time < t → o ν = o' ν) (τ : Target T m A) :
    loadGiven lhat n o (countBefore lhat n o t) τ =
      loadGiven lhat n o' (countBefore lhat n o t) τ :=
  loadGiven_congr hr hb (fun ν hν => ho ν (not_le.1 fun hc => hν (countBefore_of_le hc))) τ

private theorem countBefore_congr (hr : 0 < r) (hb : 0 < b) {t : ℕ}
    (ho : ∀ ν : MoveChannel R ch FL, ν.1.time < t → o ν = o' ν) :
    countBefore lhat n o t = countBefore lhat n o' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ho' : ∀ ν : MoveChannel R ch FL, ν.1.time < t → o ν = o' ν := fun ν hν => ho ν (by omega)
    funext mv
    rw [countBefore_succ, countBefore_succ, ← ih ho']
    split_ifs
    · exact countOfLoad_congr fun τ _ => loadGiven_countBefore_congr hr hb ho' τ
    · rfl

/-- The number of units of a move depends on the outcomes of earlier moves only. -/
theorem moveCount_congr (hr : 0 < r) (hb : 0 < b) {mv : Move R ch FL}
    (ho : ∀ ν : MoveChannel R ch FL, ν.1.time < mv.time → o ν = o' ν) :
    moveCount lhat n o mv = moveCount lhat n o' mv := by
  rw [moveCount, moveCount, countBefore_of_lt mv.time_lt_endTime,
    countBefore_of_lt mv.time_lt_endTime, ← countBefore_congr hr hb ho]
  exact countOfLoad_congr fun τ _ => loadGiven_countBefore_congr hr hb ho τ

/-- The load of a target depends on the outcomes of the moves before its time only. -/
theorem load_congr (hr : 0 < r) (hb : 0 < b) {τ : Target T m A} {t : ℕ} (hτ : τ.time ≤ t)
    (ho : ∀ ν : MoveChannel R ch FL, ν.1.time < t → o ν = o' ν) :
    load lhat n o τ = load lhat n o' τ := by
  rw [← loadGiven_countBefore hτ, ← loadGiven_countBefore hτ, ← countBefore_congr hr hb ho]
  exact loadGiven_countBefore_congr hr hb ho τ

/-- Whether an outcome of a move is good depends on the outcomes up to that move only. -/
theorem goodOutcome_congr (hr : 0 < r) (hb : 0 < b) {mv : Move R ch FL}
    (ho : ∀ ν : MoveChannel R ch FL, ν.1.time < mv.time → o ν = o' ν)
    (ho' : ∀ ν : MoveChannel R ch FL, ν.1 = mv → o ν = o' ν) :
    GoodOutcome lhat n o mv ↔ GoodOutcome lhat n o' mv := by
  have hnum := moveCount_congr (lhat := lhat) (n := n) hr hb ho
  rcases mv with ⟨x, hx⟩ | l
  · have ho'' (c : Bool) : o ⟨.relay x hx, c⟩ = o' ⟨.relay x hx, c⟩ :=
      ho' ⟨.relay x hx, c⟩ rfl
    simp only [GoodOutcome, hnum, ho'']
  · have ho'' (c : (FL.law l.kind).Channel) : o ⟨.vertex l, c⟩ = o' ⟨.vertex l, c⟩ :=
      ho' ⟨.vertex l, c⟩ rfl
    simp only [GoodOutcome, VertexMove.OutcomeShort, hnum, ho'']

end Causal

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
