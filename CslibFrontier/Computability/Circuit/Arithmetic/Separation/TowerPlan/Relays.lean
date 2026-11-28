/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Path
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Tree
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-!
# The tower plan: relays and targets

The tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module `Nc.Tow.Net`) moves the
units of a network along a covering tower until all of them join a node and its parent in the
tree of the tower (`Cslib.CoveringTower.Tower.Node`), whose nodes are the chambers of all levels
and a root. The units of two base parties are led by relays along a route between their chambers
(`Relay.start`); at a stage, the units on an edge whose type is not the chosen one are relayed
through the host of the edge (`Relay.inner`), those on an edge of the chosen type are relayed in
four steps through the hosts and the images of its ends (`Relay.middle`), and after the last stage
all units are relayed through the root (`Relay.final`).

Every channel of a move has a *target* (`Target`) that says what becomes of its units: they stay
between a node and its parent (`Target.done`), they lie on an edge of a stage (`Target.edge`),
they are given in a relay (`Target.relay`), or they are end segments on a pair of places of a
vertex, to which a law is applied (`Target.segment`).

## Main definitions

* `Relay`, `Relay.party`, `Relay.Occurs`, `Relay.time`: the relays, their three parties, the
  condition under which a relay is a move of the plan, and the order of the relays.
* `Target`, `Target.time`, `endTime`, `stepTarget`, `Relay.target`, `Relay.input`: targets and
  their times; the target of a step of a route, the targets of the two channels of a relay and
  the target whose units are given in a relay.
* `batchChamber`, `initialTarget`: the chamber through which an initial unit is led, and the
  target of an initial unit.

## Main results

* `Relay.sum_eq`: a sum over the relays, by their kinds.
* `Relay.party_injective`: the three parties of a relay of the plan are different.
* `Relay.time_lt_time_target`, `Relay.time_input_le`: the units of the channels of a relay are
  given later, and the units given in a relay are made earlier.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "Start" and "One stage"); module `Nc.Tow.Net`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

variable {h b D J r m Uu A : ℕ}

/-- The relays of the tower plan. -/
inductive Relay (T : Tower h b D J r) (m A : ℕ) where
  /-- Step `s` of the route of the units from the base party `a` to the base party `c` that are
  led through the chamber `γ`. -/
  | start (a c : Fin A) (γ : T.X 0) (s : Fin (2 * m))
  /-- The units on the edge `e` of the stage `j`, relayed through the host of type `i` of its
  ends. -/
  | inner (j : Fin J) (i : Fin h) (e : T.Ed j)
  /-- Step `s` of the way of the units on the edge `e` of the stage `j` through the hosts and
  the images of its ends in the next level. -/
  | middle (j : Fin J) (e : T.Ed j) (s : Fin 4)
  /-- The units on an edge of the last stage, relayed through the root. -/
  | final (e : T.Ed J)
  deriving DecidableEq, Fintype

/-- A sum over the relays, by their kinds. -/
theorem Relay.sum_eq {T : Tower h b D J r} {M : Type*} [AddCommMonoid M] (g : Relay T m A → M) :
    ∑ x, g x = (∑ a, ∑ c, ∑ γ, ∑ s, g (.start a c γ s)) + ((∑ j, ∑ i, ∑ e, g (.inner j i e)) +
      ((∑ j, ∑ e, ∑ s, g (.middle j e s)) + ∑ e, g (.final e))) := by
  rw [← (proxy_equiv% (Relay T m A)).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

/-- The targets: what becomes of the units of a channel. -/
inductive Target (T : Tower h b D J r) (m A : ℕ) where
  /-- The units stay between a node and its parent. -/
  | done
  /-- The units lie on an edge of the stage `j`. -/
  | edge (j : Fin (J + 1)) (e : T.Ed j)
  /-- The units are given in a relay. -/
  | relay (x : Relay T m A)
  /-- The units are end segments on the pair `q` of places of the vertex `ω`. -/
  | segment (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl)
  deriving DecidableEq, Fintype

variable {T : Tower h b D J r}

namespace Relay

variable (R : Routes T m Uu) (ch : Fin A ↪ T.X 0)

/-- The three parties of a relay: the units between `source` and `sink` are led through
`via`. -/
@[expose] def party : Relay T m A → RelayRole → T.Node
  | .start a c γ s => RelayRole.elim (.ofChamber (Nat.zero_le J) (R.pn (ch a) (ch c) γ s))
      (.ofChamber (Nat.zero_le J) (R.pn (ch a) (ch c) γ (s + 1)))
      (.ofChamber (Nat.zero_le J) (ch c))
  | .inner j i e => RelayRole.elim (.ofChamber j.isLt.le (T.e0 e))
      (.ofChamber j.isLt (T.hostOf i (T.e0 e))) (.ofChamber j.isLt.le (T.e1 e))
  | .middle j e s =>
    let host₀ : T.Node := .ofChamber j.isLt (T.hostOf (T.ty e) (T.e0 e))
    let host₁ : T.Node := .ofChamber j.isLt (T.hostOf (T.ty e) (T.e1 e))
    let image₀ : T.Node := .ofChamber j.isLt (T.π (T.e0 e))
    let image₁ : T.Node := .ofChamber j.isLt (T.π (T.e1 e))
    RelayRole.elim (![.ofChamber j.isLt.le (T.e0 e), host₀, image₀, image₁] s)
      (![host₀, image₀, image₁, host₁] s) (.ofChamber j.isLt.le (T.e1 e))
  | .final e => RelayRole.elim (.ofChamber le_rfl (T.e0 e)) .root (.ofChamber le_rfl (T.e1 e))

/-- The relay is a move of the plan: its three parties are different. A step of a route is
before the first visit of the last chamber, the host of an inner relay is of another type than
the edge, and trivial steps of the way of an edge are omitted. -/
@[expose] def Occurs : Relay T m A → Prop
  | .start a c γ s => a ≠ c ∧ s.val + 1 < R.pl (ch a) (ch c) γ
  | .inner _ i e => T.ty e ≠ i
  | .middle _ e s => (s = 1 → T.hostOf (T.ty e) (T.e0 e) ≠ T.π (T.e0 e)) ∧
      (s = 3 → T.π (T.e1 e) ≠ T.hostOf (T.ty e) (T.e1 e))
  | .final _ => True

instance : DecidablePred (Occurs R ch : Relay T m A → Prop)
  | .start .. => inferInstanceAs (Decidable (_ ∧ _))
  | .inner .. => inferInstanceAs (Decidable (_ ≠ _))
  | .middle .. => inferInstanceAs (Decidable (_ ∧ _))
  | .final _ => inferInstanceAs (Decidable True)

variable {R ch}

/-- The three parties of a relay of the plan are different. -/
theorem party_injective {x : Relay T m A} (hx : x.Occurs R ch) :
    Function.Injective (x.party R ch) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · have hs := hx.2
    obtain ⟨-, -, -, h3⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by omega)
    exact RelayRole.elim_injective (by simpa using h3) (by simpa using R.pn_ne _ _ _ (by omega))
      (by simpa using R.pn_ne _ _ _ hs)
  · exact RelayRole.elim_injective (Tower.Node.ofChamber_ne_of_ne (by omega))
      (by simpa using T.e_ne e) (Tower.Node.ofChamber_ne_of_ne (by omega))
  · have h1 := T.π_ne j.isLt e
    have h2 := T.e_ne e
    have h3 {c : T.X j} {c' : T.X (j + 1)} :
        (.ofChamber j.isLt.le c : T.Node) ≠ .ofChamber j.isLt c' :=
      Tower.Node.ofChamber_ne_of_ne (by omega)
    refine RelayRole.elim_injective ?_ ?_ ?_ <;> fin_cases s <;> simp_all [Occurs, h3.symm]
  · exact RelayRole.elim_injective Tower.Node.ofChamber_ne_root (by simpa using T.e_ne e)
      Tower.Node.ofChamber_ne_root.symm

variable (m) in
/-- The time of a relay: the relays of the routes come first, then those of the stages. -/
@[expose] def time : Relay T m A → ℕ
  | .start _ _ _ s => s
  | .inner j _ _ => 2 * m + 6 * j
  | .middle j _ s => 2 * m + 6 * j + s
  | .final _ => 2 * m + 6 * J

end Relay

/-- The end of time: all moves are earlier. -/
@[expose] def endTime (J m : ℕ) : ℕ := 2 * m + 6 * J + 1

/-- The time until which all channels with a target have been made. -/
@[expose] def Target.time : Target T m A → ℕ
  | .done => endTime J m
  | .edge j _ => 2 * m + 6 * j
  | .relay x => x.time m
  | .segment j _ _ _ => 2 * m + 6 * j + 4

/-- The target of the units on step `s` of the route from `c` to `c'` through `γ`: the edge of
the step, if there is one. -/
@[expose] def stepTarget (R : Routes T m Uu) (c c' γ : T.X 0) (s : ℕ) : Target T m A :=
  ((R.path c c' γ)[s]?).elim .done (.edge 0)

private theorem two_mul_le_time_stepTarget (R : Routes T m Uu) (c c' γ : T.X 0) (s : ℕ) :
    2 * m ≤ (stepTarget R c c' γ s : Target T m A).time := by
  unfold stepTarget
  cases (R.path c c' γ)[s]? <;> simp [Option.elim, Target.time, endTime]
  omega

namespace Relay

variable (R : Routes T m Uu) (ch : Fin A ↪ T.X 0)

/-- The targets of the two channels of a relay. -/
@[expose] def target : Relay T m A → Bool → Target T m A
  | .start a c γ s, false => stepTarget R (ch a) (ch c) γ s
  | .start a c γ s, true =>
    if hs : s.val + 1 < 2 * m ∧ s.val + 2 < R.pl (ch a) (ch c) γ then
      .relay (.start a c γ ⟨s.val + 1, hs.1⟩)
    else stepTarget R (ch a) (ch c) γ (s + 1)
  | .inner _ _ _, _ => .done
  | .middle j e s, false =>
    ![.done,
      .segment j (T.ty e) (T.πV (T.vx (T.ty e) (T.e0 e)))
        s(T.co (T.ty e) (T.hostOf (T.ty e) (T.e0 e)), T.co (T.ty e) (T.e0 e)),
      .edge j.succ (T.πE e),
      .segment j (T.ty e) (T.πV (T.vx (T.ty e) (T.e1 e)))
        s(T.co (T.ty e) (T.hostOf (T.ty e) (T.e1 e)), T.co (T.ty e) (T.e1 e))] s
  | .middle j e s, true =>
    ![if T.hostOf (T.ty e) (T.e0 e) ≠ T.π (T.e0 e) then .relay (.middle j e 1)
      else .relay (.middle j e 2),
      .relay (.middle j e 2),
      if T.π (T.e1 e) ≠ T.hostOf (T.ty e) (T.e1 e) then .relay (.middle j e 3) else .done,
      .done] s
  | .final _, _ => .done

/-- The target whose units are given in a relay. -/
@[expose] def input : Relay T m A → Target T m A
  | .inner j _ e => .edge j.castSucc e
  | .middle j e s => if s = 0 then .edge j.castSucc e else .relay (.middle j e s)
  | .final e => .edge (Fin.last J) e
  | x => .relay x

variable {R ch}

/-- The units of the channels of a relay are given later. -/
theorem time_lt_time_target (x : Relay T m A) (d : Bool) :
    x.time m < (x.target R ch d).time := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · have hs := s.isLt
    have h1 := two_mul_le_time_stepTarget (A := A) R (ch a) (ch c) γ
    cases d
    · exact hs.trans_le (h1 s)
    · simp only [target]
      split_ifs
      · simp [Target.time, Relay.time]
      · exact hs.trans_le (h1 _)
  · have := j.isLt
    simp only [target, Relay.time, Target.time, endTime]
    omega
  · have := j.isLt
    cases d <;> fin_cases s <;> simp [target, Relay.time, Target.time, endTime] <;> grind
  · exact Nat.lt_succ_self _

/-- The units given in a relay are made earlier. -/
theorem time_input_le (x : Relay T m A) : x.input.time ≤ x.time m := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;> simp only [input] <;> try split_ifs
  all_goals simp [Target.time, Relay.time]

theorem time_lt_endTime (x : Relay T m A) : x.time m < endTime J m := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;> simp only [Relay.time, endTime] <;>
    omega

@[simp]
theorem input_ne_done {x : Relay T m A} : x.input ≠ .done := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;> simp only [input] <;> try split_ifs
  all_goals simp

@[simp]
theorem input_ne_segment {x : Relay T m A} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i}
    {q : Sym2 T.Fl} : x.input ≠ .segment j i ω q := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;> simp only [input] <;> try split_ifs
  all_goals simp

end Relay

/-- The chamber through which the unit `k` of the base party `a` is led: the units of a string
are divided into batches, one for every chamber of the level `0`. -/
@[expose] noncomputable def batchChamber (ch : Fin A ↪ T.X 0) (a : Fin A) (k : ℕ) : T.X 0 :=
  (Fintype.equivFin (T.X 0)).symm
    ⟨k % Fintype.card (T.X 0), Nat.mod_lt _ (Fintype.card_pos_iff.2 ⟨ch a⟩)⟩

/-- The target of the unit `k` of the string from the base party `a` to the base party `c`: it
is given in the first relay of its route, or it lies on the only edge of the route. -/
@[expose] noncomputable def initialTarget (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (a c : Fin A)
    (k : ℕ) : Target T m A :=
  if a = c then .done
  else if hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (batchChamber ch a k) then
    .relay (.start a c (batchChamber ch a k) ⟨0, hs.1⟩)
  else stepTarget R (ch a) (ch c) (batchChamber ch a k) 0

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
