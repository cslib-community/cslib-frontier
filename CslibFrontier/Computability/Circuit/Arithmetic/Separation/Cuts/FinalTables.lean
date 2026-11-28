/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves

/-!
# Units that are present in the tables after the moves

The tables of the parties vanish on absent copies of units ([AnthropicVPVNP2026], Proposition
J.2; module `Nc.G.Exact`). The table of a base party at the beginning (`Cut.initialTable`)
requires its copies of the initial units to be the units of strings, and the table of a role
(`Cut.roleTable`) requires the copies of the new units of its channels to be the units of the
strings on the channels. So the table of a party after the moves of a plan (`Cut.partyTable`,
`Cut.finalTable`) vanishes unless its copies of all units seen in the end that it holds are
present, and the value of a group of parties (`Cut.Plan.groupValue`) vanishes unless the units
that the group shares with other groups are present.

## Main results

* `Cut.partyTable_ne_none`, `Cut.initialTables_ne_none`, `Cut.finalTable_ne_none`: the copies of
  the units that a party holds are present if its table is not zero.
* `Cut.Plan.ne_none_of_groupValue_ne_zero`: the contents of the units that a group shares with
  other groups are present if the value of the group is not zero.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2; modules `Nc.G.Exact` and `Nc.G.Start`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset Tape

variable {F Γ S Q : Type*} [CommSemiring F] {A A' E K U0 U1 c ub : ℕ}

section Party

variable {M : Moves F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)}
  {o : M.Channel → Fin U1}

/-- If the table of a party after the moves is not zero, its copies of the units seen in the end
that it holds are present; `init` is its table at the beginning. -/
theorem partyTable_ne_none {init : (UnitId A U0 M.Channel U1 → UnitContent ub) → F}
    {a : Fin (A + A')} {y : UnitId A U0 M.Channel U1 → UnitContent ub}
    (hinit : init y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder M.channelParty) a id → y id ≠ none)
    (h : partyTable P n o init a y ≠ 0) {id : UnitId A U0 M.Channel U1}
    (hid : id ∈ Plan.seenAt n o E) (ha : Play.Holds (UnitId.holder M.channelParty) a id) :
    y id ≠ none := by
  rw [partyTable] at h
  obtain ⟨b, c, k⟩ | ⟨⟨x, ν⟩, k⟩ := id
  · exact hinit (left_ne_zero_of_mul h) _
      (init_mem_initialUnits.2 (Plan.init_mem_seenAt.1 hid)) ha
  · obtain ⟨d, rfl⟩ := ha
    have h1 : roleTableAt P n o ⟨x, (M.law x).channelEnd ν d⟩ y ≠ 0 := fun h0 =>
      right_ne_zero_of_mul h (prod_eq_zero (mem_univ ⟨x, (M.law x).channelEnd ν d⟩)
        ((ite_eq_left rfl).trans h0))
    exact roleTable_new_ne_none h1 (Play.holds_end _ ν d) (Plan.new_mem_seenAt.1 hid).2

end Party

variable [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → BitString c}
  {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}

variable {ρ : Option S → Fin (K + K) → RowData (K + K)}

/-- If the table of a party at the beginning is not zero, its copies of the initial units that it
holds are present. An extra party holds no initial unit. -/
theorem initialTables_ne_none {N : Type*} [Fintype N] {np : N → Bool → Fin (K + K + A')}
    {p : Fin (K + K + A')} {y : UnitId (K + K) U0 N U1 → UnitContent ub}
    (h : initialTables mu T cb A' q x ρ n p y ≠ 0) :
    ∀ id ∈ initialUnits n, Play.Holds (UnitId.holder np) p id → y id ≠ none := by
  induction p using Fin.addCases with
  | left p =>
    rw [initialTables, Fin.addCases_left] at h
    exact initialTable_ne_none h
  | right p =>
    rintro (⟨a, b, k⟩ | ⟨ν, k⟩) hid ⟨d, hd⟩
    · have h1 := congrArg Fin.val hd
      have h2 := (bif d then b else a).isLt
      simp only [UnitId.holder, Fin.val_castAdd, Fin.val_natAdd] at h1
      omega
    · exact absurd hid new_notMem_initialUnits

variable {M : Moves F (K + K + A') E} {P : Plan M U0 U1} {o : M.Channel → Fin U1}

/-- If the table of a party after the moves of a plan is not zero, its copies of the units seen
in the end that it holds are present. -/
theorem finalTable_ne_none {p : Fin (K + K + A')}
    {y : UnitId (K + K) U0 M.Channel U1 → UnitContent ub}
    (h : finalTable P mu T cb q x ρ n o p y ≠ 0) {id : UnitId (K + K) U0 M.Channel U1}
    (hid : id ∈ Plan.seenAt n o E) (ha : Play.Holds (UnitId.holder M.channelParty) p id) :
    y id ≠ none :=
  partyTable_ne_none initialTables_ne_none h hid ha

/-- If the value of a group of parties after the moves of a plan is not zero, the contents of the
current units that the group shares with other groups are present. -/
theorem Plan.ne_none_of_groupValue_ne_zero {G : Type*} [DecidableEq G]
    {grp : Fin (K + K + A') → G} {g : G} {b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub}
    (h : P.groupValue mu T cb q x ρ n o grp g b ≠ 0) {id : UnitId (K + K) U0 M.Channel U1}
    (hid : id ∈ P.cur n o E) {d : Bool} (hd : grp (UnitId.holder M.channelParty id d) = g)
    (hd' : grp (UnitId.holder M.channelParty id !d) ≠ g) : b id ≠ none :=
  Play.ne_empty_of_groupValue_ne_zero sdiff_subset
    (fun _ _ h0 _ hi ha => finalTable_ne_none h0 hi ha) h hid hd hd'

end Cslib.Circuits.Arithmetic.Separation.Cut
