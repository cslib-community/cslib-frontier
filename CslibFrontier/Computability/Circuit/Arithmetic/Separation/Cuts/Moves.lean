/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Codes
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Law
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Units
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Moves, units and plans

The play of the cutting argument of [AnthropicVPVNP2026] (Appendix H.2 and Appendix J; module
`Nc.G.Defs`) is run by *moves*. A move has a law (`Cut.Law`) and a party for every role of the
law (`Cut.Moves`). In a move, units are given at every slot of the law (a slot given fewer units
than the move uses reads zeros after them; a move whose given units are not all present
contributes zero), and the strings on a channel of the law, a label and the string of the law
for every bit, are cut into new units.

Units have names (`Cut.UnitId`): the *initial* units of the strings between two base parties, and
the *new* units of the channels of the moves. A *plan* (`Cut.Plan`) says which units are given at
every slot and how many units a move uses, as functions of the numbers of initial units and of
the outcomes of the earlier moves; an *outcome* gives the number of units of every channel.

## Main definitions

* `Cut.Moves`, with `Cut.Moves.Role`, `Cut.Moves.Slot`, `Cut.Moves.Channel`, the roles and
  parties at the ends `Cut.Moves.slotRole`, `Cut.Moves.channelRole`, `Cut.Moves.roleParty`,
  `Cut.Moves.slotParty`, `Cut.Moves.channelParty`, and `Cut.Moves.setOutcome`.
* `Cut.UnitId`, `Cut.UnitId.holder`, `Cut.UnitId.index`, `Cut.UnitId.count`, `Cut.UnitId.list`:
  names of units, their two holders, their number in their string, the number of units of that
  string, and all units in a fixed order.
* `Cut.initialUnits`, `Cut.newUnits`: the units at the beginning, and those made by a move.
* `Cut.slotBits`, `Cut.ChannelOk`, `Cut.roleTable`: the bits given at a slot, the condition on
  the copies of the new units of a channel, and the table of a role of a move.
* `Cut.Plan`, with `Cut.Plan.seenAt`, `Cut.Plan.used`, `Cut.Plan.cur`, `Cut.Plan.ids`,
  `Cut.Plan.Possible` and the rules `Cut.Plan.Ok`.
* `Cut.roleTableAt`, `Cut.partyTable`: the tables of the roles and of the parties in the play.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix H.2 and Appendix J; module `Nc.G.Defs`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset

/-- The moves: a law for every move, and a party for every role of its law. -/
structure Moves (F : Type*) [CommSemiring F] (A E : ℕ) where
  /-- The law of a move. -/
  law : Fin E → Law F
  /-- The parties of a move. -/
  party : ∀ x, (law x).Role → Fin A
  party_injective : ∀ x, Function.Injective (party x)

namespace Moves

variable {F : Type*} [CommSemiring F] {A E : ℕ} (M : Moves F A E)

/-- All roles of all moves. -/
abbrev Role : Type := Σ x, (M.law x).Role

/-- All slots of all moves. -/
abbrev Slot : Type := Σ x, (M.law x).Slot

/-- All channels of all moves. -/
abbrev Channel : Type := Σ x, (M.law x).Channel

/-- The party of a role. -/
@[expose] def roleParty (r : M.Role) : Fin A := M.party r.1 r.2

/-- The role at an end of a slot. -/
@[expose] def slotRole (z : M.Slot) (d : Bool) : M.Role := ⟨z.1, (M.law z.1).slotEnd z.2 d⟩

/-- The role at an end of a channel. -/
@[expose] def channelRole (ν : M.Channel) (d : Bool) : M.Role :=
  ⟨ν.1, (M.law ν.1).channelEnd ν.2 d⟩

/-- The party at an end of a slot. -/
@[expose] def slotParty (z : M.Slot) (d : Bool) : Fin A := M.roleParty (M.slotRole z d)

/-- The party at an end of a channel. -/
@[expose] def channelParty (ν : M.Channel) (d : Bool) : Fin A := M.roleParty (M.channelRole ν d)

/-- Set the outcome of the move `x`. -/
@[expose] def setOutcome {U1 : ℕ} (o : M.Channel → Fin U1) (x : Fin E)
    (oo : (M.law x).Channel → Fin U1) : M.Channel → Fin U1 :=
  fun ν => if h : ν.1 = x then oo (h ▸ ν.2) else o ν

end Moves

/-- Names of units. `init a b k` is unit number `k` of the string from the party `a` to the party
`b` (only the `A` base parties have strings at the beginning); `new ν k` is unit number `k` of
the channel `ν` of a move. -/
inductive UnitId (A U0 : ℕ) (N : Type*) (U1 : ℕ) where
  /-- A unit of a string at the beginning. -/
  | init (a b : Fin A) (k : Fin U0)
  /-- A unit made by a move. -/
  | new (ν : N) (k : Fin U1)
  deriving DecidableEq, Fintype

namespace UnitId

variable {A A' U0 U1 : ℕ} {N : Type*}

/-- The two holders of a unit; `np` gives the parties at the ends of the channels. There are `A`
base parties and `A'` extra parties. -/
@[expose] def holder (np : N → Bool → Fin (A + A')) : UnitId A U0 N U1 → Bool → Fin (A + A')
  | .init a b _, d => Fin.castAdd A' (bif d then b else a)
  | .new ν _, d => np ν d

/-- The number of a unit in its string. -/
@[expose] def index : UnitId A U0 N U1 → ℕ
  | .init _ _ k => k
  | .new _ k => k

/-- The number of units of the string to which a unit belongs: `n a b` units at the beginning,
and `o ν + 1` units on the channel `ν`. -/
@[expose] def count (n : Fin A → Fin A → Fin (U0 + 1)) (o : N → Fin U1) : UnitId A U0 N U1 → ℕ
  | .init a b _ => n a b
  | .new ν _ => o ν + 1

/-- All units, in a fixed order. -/
@[expose] noncomputable def list (A U0 : ℕ) (N : Type*) [Fintype N] (U1 : ℕ) :
    List (UnitId A U0 N U1) :=
  (univ : Finset (UnitId A U0 N U1)).toList

/-- The holders of an initial unit are the two base parties of its string. -/
theorem holds_init {np : N → Bool → Fin (A + A')} {p : Fin (A + A')} {a b : Fin A}
    {k : Fin U0} : Play.Holds (holder np) p (.init a b k : UnitId A U0 N U1) ↔
      p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b := by
  simp [Play.Holds, holder, eq_comm]

/-- A sum over all units: the initial units and the new units. -/
theorem sum_eq {M : Type*} [Fintype N] [AddCommMonoid M] (f : UnitId A U0 N U1 → M) :
    ∑ u, f u = (∑ a, ∑ c, ∑ k, f (.init a c k)) + ∑ ν, ∑ k, f (.new ν k) := by
  rw [← (proxy_equiv% (UnitId A U0 N U1)).sum_comp, Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma]
  rfl

/-- The number of units: `A * A * U0` initial units and `U1` units of every channel. -/
theorem card_eq [Fintype N] :
    Fintype.card (UnitId A U0 N U1) = A * A * U0 + Fintype.card N * U1 := by
  rw [Fintype.card_eq_sum_ones, sum_eq]
  simp [Nat.mul_assoc]

end UnitId

section Units

variable {F : Type*} [CommSemiring F] {A A' E U0 U1 ub : ℕ} {N : Type*} [Fintype N]

/-- The units at the beginning: the first `n a b` units of the string from `a` to `b`. -/
def initialUnits (n : Fin A → Fin A → Fin (U0 + 1)) : Finset (UnitId A U0 N U1) :=
  univ.filter fun id => (match id with
    | .init a b k => decide ((k : ℕ) < n a b)
    | .new _ _ => false) = true

@[simp]
theorem init_mem_initialUnits {n : Fin A → Fin A → Fin (U0 + 1)} {a b : Fin A} {k : Fin U0} :
    (.init a b k : UnitId A U0 N U1) ∈ initialUnits n ↔ (k : ℕ) < n a b := by
  simp [initialUnits]

@[simp]
theorem new_notMem_initialUnits {n : Fin A → Fin A → Fin (U0 + 1)} {ν : N} {k : Fin U1} :
    (.new ν k : UnitId A U0 N U1) ∉ initialUnits n := by
  simp [initialUnits]

variable (M : Moves F (A + A') E)

/-- The new units of the move `x` for the outcome `o`: the first `o ν + 1` units of every channel
`ν` of the move. -/
def newUnits (x : Fin E) (o : M.Channel → Fin U1) : Finset (UnitId A U0 M.Channel U1) :=
  univ.filter fun id => (match id with
    | .init _ _ _ => false
    | .new ν k => decide (ν.1 = x ∧ k ≤ o ν)) = true

variable {M}

@[simp]
theorem new_mem_newUnits {x : Fin E} {o : M.Channel → Fin U1} {ν : M.Channel} {k : Fin U1} :
    (.new ν k : UnitId A U0 M.Channel U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

@[simp]
theorem init_notMem_newUnits {x : Fin E} {o : M.Channel → Fin U1} {a b : Fin A} {k : Fin U0} :
    (.init a b k : UnitId A U0 M.Channel U1) ∉ newUnits M x o := by
  simp [newUnits]

/-- The bits given at a slot: the bits of the units `ids`, then zeros for the `t - ids.length`
units that are not given. An absent unit has no bits (`UnitContent.bits none = []`); `roleTable`
excludes that case. -/
@[expose] def slotBits (t : ℕ) (ids : List (UnitId A U0 N U1))
    (y : UnitId A U0 N U1 → UnitContent ub) : List Bool :=
  (ids.flatMap fun id => (y id).bits) ++ List.replicate ((t - ids.length) * ub) false

/-- The copies `y` of the new units of the channel `ν` are the `J + 1` units of the string
`str`. -/
@[expose] def ChannelOk (ν : N) (J : ℕ) (str : List Bool)
    (y : UnitId A U0 N U1 → UnitContent ub) : Prop :=
  unitCount ub str = J + 1 ∧ ∀ k : Fin U1, y (.new ν k) = unitsOf ub str k

instance (ν : N) (J : ℕ) (str : List Bool) (y : UnitId A U0 N U1 → UnitContent ub) :
    Decidable (ChannelOk ν J str y) :=
  inferInstanceAs (Decidable (unitCount ub str = J + 1 ∧
    ∀ k : Fin U1, y (.new ν k) = unitsOf ub str k))

variable (M)

/-- The table of the role `p` of the move `x`. The units `ids e` are given at the slot `e`, the
move uses `t` units, and `o` is the outcome. The table reads the copies `y` of the units given at
the slots of the role and of the new units of its channels: for every one of the `t * ub` bits
there are an index and strings of the law, and the strings on a channel, with the labels of the
indices, are the string that is cut into the new units of the channel. The table is zero if a
unit given at a slot of the role is absent; otherwise the slots are read through `slotBits`. -/
@[expose] def roleTable (x : Fin E) (p : (M.law x).Role) (t : ℕ)
    (ids : (M.law x).SlotAt p → List (UnitId A U0 M.Channel U1)) (o : M.Channel → Fin U1)
    (y : UnitId A U0 M.Channel U1 → UnitContent ub) : F :=
  if ∀ e, ∀ id ∈ ids e, y id ≠ none then
    ∑ i : Fin (t * ub) → (M.law x).Index,
      ∑ g : ∀ k, ∀ ν : (M.law x).ChannelAt p, BitString ((M.law x).length (i k) ν),
        if ∀ ν : (M.law x).ChannelAt p, ChannelOk ⟨x, ν.val⟩ (o ⟨x, ν.val⟩)
          (sideString (M.law x).label (fun j => (M.law x).length j ν) i fun k => g k ν) y
        then ∏ k : Fin (t * ub),
          (M.law x).table p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k)
        else 0
  else 0

end Units

/-- A plan: which units are given at every slot, and the number of units that every move uses
(slots given fewer units read zeros after them), as functions of the numbers `n` of units at the
beginning and of the outcomes `o` of the earlier moves; and which outcomes are allowed. -/
structure Plan {F : Type*} [CommSemiring F] {A A' E : ℕ} (M : Moves F (A + A') E)
    (U0 U1 : ℕ) where
  /-- The units given at a slot. -/
  given : (Fin A → Fin A → Fin (U0 + 1)) → (M.Channel → Fin U1) → M.Slot →
    Finset (UnitId A U0 M.Channel U1)
  /-- The number of units that a move uses. -/
  count : (Fin A → Fin A → Fin (U0 + 1)) → (M.Channel → Fin U1) → Fin E → ℕ
  /-- The outcomes of a move that are allowed. -/
  Good : (Fin A → Fin A → Fin (U0 + 1)) → (M.Channel → Fin U1) → Fin E → Prop

namespace Plan

variable {F : Type*} [CommSemiring F] {A A' E U0 U1 : ℕ} {M : Moves F (A + A') E}
  (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.Channel → Fin U1)

/-- The units seen before the move `x` (for `x = E`: in the end). -/
@[expose] def seenAt (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.Channel → Fin U1) (x : ℕ) :
    Finset (UnitId A U0 M.Channel U1) :=
  initialUnits n ∪ (univ.filter fun x' : Fin E => (x' : ℕ) < x).biUnion fun x' => newUnits M x' o

/-- The units given before the move `x`. -/
@[expose] def used (x : ℕ) : Finset (UnitId A U0 M.Channel U1) :=
  (univ.filter fun z : M.Slot => (z.1 : ℕ) < x).biUnion fun z => P.given n o z

/-- The current units before the move `x`. -/
@[expose] def cur (x : ℕ) : Finset (UnitId A U0 M.Channel U1) := seenAt n o x \ P.used n o x

/-- The units given at a slot, in the order of `UnitId.list`. -/
@[expose] noncomputable def ids (z : M.Slot) : List (UnitId A U0 M.Channel U1) :=
  (UnitId.list A U0 M.Channel U1).filter fun id => id ∈ P.given n o z

/-- The outcome of the move `x` is possible: there is an index for every bit such that the
strings on the channels have the numbers of units of the outcome. -/
@[expose] def Possible (ub : ℕ) (x : Fin E) : Prop :=
  ∃ ι : Fin (P.count n o x * ub) → (M.law x).Index, ∀ ν : (M.law x).Channel,
    (o ⟨x, ν⟩ : ℕ) = (∑ k, ((M.law x).labelLength + (M.law x).length (ι k) ν)) / ub

/-- The rules that a plan obeys; `cap` bounds the number of units that a move uses. -/
structure Ok (cap : ℕ) : Prop where
  /-- The units given at a slot depend on the outcomes of earlier moves only. -/
  given_congr : ∀ n o o' z, (∀ ν : M.Channel, ν.1 < z.1 → o ν = o' ν) →
    P.given n o z = P.given n o' z
  /-- The number of units of a move depends on the outcomes of earlier moves only. -/
  count_congr : ∀ n o o' x, (∀ ν : M.Channel, ν.1 < x → o ν = o' ν) →
    P.count n o x = P.count n o' x
  /-- Whether an outcome of a move is allowed depends on the outcomes up to that move only. -/
  good_congr : ∀ n o o' x, (∀ ν : M.Channel, ν.1 ≤ x → o ν = o' ν) →
    (P.Good n o x ↔ P.Good n o' x)
  /-- Only current units are given. -/
  given_subset : ∀ n o z, P.given n o z ⊆ P.cur n o z.1
  /-- The holders of a unit given at a slot are the parties at the ends of the slot. -/
  holder_given : ∀ n o z, ∀ id ∈ P.given n o z, ∃ d : Bool, ∀ d' : Bool,
    UnitId.holder M.channelParty id d' = M.slotParty z (d ^^ d')
  /-- No unit is given at two slots of a move. -/
  given_disjoint : ∀ n o (x : Fin E) e e', e ≠ e' →
    Disjoint (P.given n o ⟨x, e⟩) (P.given n o ⟨x, e'⟩)
  /-- A slot is given at most as many units as the move uses. -/
  card_given_le : ∀ n o z, (P.given n o z).card ≤ P.count n o z.1
  /-- A move uses at most `cap` units. -/
  count_le : ∀ n o x, P.count n o x ≤ cap

end Plan

section Tables

variable {F : Type*} [CommSemiring F] {A A' E U0 U1 ub : ℕ} {M : Moves F (A + A') E}

/-- The table of a role in the play. -/
@[expose] noncomputable def roleTableAt (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1))
    (o : M.Channel → Fin U1) (r : M.Role) (y : UnitId A U0 M.Channel U1 → UnitContent ub) : F :=
  roleTable M r.1 r.2 (P.count n o r.1) (fun e => P.ids n o ⟨r.1, e.val⟩) o y

/-- The table of the party `a` after all moves, as a function of its copies of all units that it
has ever held: its table `init` at the beginning times the tables of its roles. -/
@[expose] noncomputable def partyTable (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1))
    (o : M.Channel → Fin U1)
    (init : (UnitId A U0 M.Channel U1 → UnitContent ub) → F) (a : Fin (A + A'))
    (y : UnitId A U0 M.Channel U1 → UnitContent ub) : F :=
  init y * ∏ r : M.Role, if M.roleParty r = a then roleTableAt P n o r y else 1

end Tables

end Cslib.Circuits.Arithmetic.Separation.Cut
