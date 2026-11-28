/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Rows
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Segments

/-!
# The tables of the parties at the beginning and after the moves

The play of the cutting argument of [AnthropicVPVNP2026] (Lemma I.2 and Proposition J.2; module
`Nc.G.Defs`) on a run of a tape automaton has `K` blocks and `K` input parties, the *base*
parties, and `A'` extra parties that the moves use. At the beginning, a base party has the table
`Cut.initialTable`: the sum of its weight (`Cut.partyWeight`) over what it writes and reads,
subject to the condition `Cut.InitialOk` that its row data are the given ones and that its copies
of the initial units are the units of the strings that it writes for, and reads from, every other
base party. An extra party has the table `1`. After the moves of a plan, the table of a party is
its table at the beginning times the tables of its roles (`Cut.finalTable`), and a group of
parties has a value for given contents of the units that it shares with other groups
(`Cut.Plan.groupValue`).

## Main definitions

* `Cut.InitialOk`: the condition in the table of a base party at the beginning.
* `Cut.initialTable`, `Cut.initialTables`: the table of a base party, and of all parties, at the
  beginning.
* `Cut.finalTable`: the table of a party after the moves of a plan.
* `Cut.Plan.groupValue`: the value of a group of parties after the moves of a plan.

## Main results

* `Cut.initialTable_congr`: the table of a base party depends on its copies of initial units
  only.
* `Cut.initialTable_ne_none`: it vanishes unless the initial units that the party holds are
  present.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 and Proposition J.2; modules `Nc.G.Defs`, `Nc.G.Start` and `Nc.G.Exact`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset Tape

variable {F Γ S Q N : Type*} {A A' E K U0 U1 c ub : ℕ}

/-- The condition in the table of the base party `p` at the beginning, for what it writes (`R`)
and reads (`C`): the row data `ρ` are those of `R`, and for every base party `b` the string that
`p` writes for `b` has `n p b` units, of which the copies `y` of `p` are the first `U0`, and
likewise for the string that `p` reads from `b`. -/
@[expose] def InitialOk (ub : ℕ) (cb : Option Γ → BitString c) [Fintype S]
    (ρ : Option S → RowData A) (n : Fin A → Fin A → ℕ) (p : Fin A)
    (y : UnitId A U0 N U1 → UnitContent ub) (R C : Option S → Fin A → List Γ) : Prop :=
  (∀ s, (ρ s).Ok (R s)) ∧
    (∀ b, unitCount ub (segmentString cb fun s => R s b) = n p b ∧
      ∀ k : Fin U0, y (.init p b k) = unitsOf ub (segmentString cb fun s => R s b) k) ∧
    ∀ b, unitCount ub (segmentString cb fun s => C s b) = n b p ∧
      ∀ k : Fin U0, y (.init b p k) = unitsOf ub (segmentString cb fun s => C s b) k

noncomputable instance (ub : ℕ) (cb : Option Γ → BitString c) [Fintype S]
    (ρ : Option S → RowData A) (n : Fin A → Fin A → ℕ) (p : Fin A)
    (y : UnitId A U0 N U1 → UnitContent ub) (R C : Option S → Fin A → List Γ) :
    Decidable (InitialOk ub cb ρ n p y R C) :=
  inferInstanceAs (Decidable ((∀ s, (ρ s).Ok (R s)) ∧
    (∀ b, unitCount ub (segmentString cb fun s => R s b) = n p b ∧
      ∀ k : Fin U0, y (.init p b k) = unitsOf ub (segmentString cb fun s => R s b) k) ∧
    ∀ b, unitCount ub (segmentString cb fun s => C s b) = n b p ∧
      ∀ k : Fin U0, y (.init b p k) = unitsOf ub (segmentString cb fun s => C s b) k))

section Tables

variable [CommSemiring F] [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → BitString c)

/-- The table of the base party `p` at the beginning, as a function of its copies `y` of units:
the sum of its weight over what it writes and reads, of at most `T` letters each, under the
condition `InitialOk`. -/
@[expose] noncomputable def initialTable (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K))
    (y : UnitId (K + K) U0 N U1 → UnitContent ub) : F :=
  ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) =>
      List.wordsLe Γ T,
    ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) =>
        List.wordsLe Γ T,
      if InitialOk ub cb ρ n p y R C then partyWeight mu T q x p R C else 0

/-- The tables of all parties at the beginning: a base party has its `initialTable`, and an extra
party the table `1`. -/
@[expose] noncomputable def initialTables (A' : ℕ) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (p : Fin (K + K + A')) :
    (UnitId (K + K) U0 N U1 → UnitContent ub) → F :=
  Fin.addCases (motive := fun _ => (UnitId (K + K) U0 N U1 → UnitContent ub) → F)
    (fun p => initialTable mu T cb q x (fun s => ρ s p) (fun a b => n a b) p) (fun _ _ => 1) p

variable {mu T cb} in
/-- The table of a party after all moves of the plan `P`: its table at the beginning times the
tables of its roles. -/
@[expose] noncomputable def finalTable {M : Moves F (K + K + A') E} (P : Plan M U0 U1)
    (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → BitString c)
    (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (p : Fin (K + K + A')) : (UnitId (K + K) U0 M.Channel U1 → UnitContent ub) → F :=
  partyTable P n o (initialTables mu T cb A' q x ρ n p) p

/-- The value of the group `g` of parties after all moves of the plan `P`, for the contents `b`
of the units that it shares with other groups. -/
@[expose] noncomputable def Plan.groupValue {G : Type*} [DecidableEq G]
    {M : Moves F (K + K + A') E} (P : Plan M U0 U1) (mu : Letter S Unit Γ → Matrix Q Q F)
    (T : ℕ) (cb : Option Γ → BitString c) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    F :=
  Play.groupValue (UnitId.holder M.channelParty) none (Plan.seenAt n o E) (P.cur n o E) grp
    (finalTable P mu T cb q x ρ n o) g b

section Properties

variable {mu T cb} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}

/-- The table of a base party at the beginning depends on its copies of initial units only. -/
theorem initialTable_congr {ρ : Option S → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)}
    {y y' : UnitId (K + K) U0 N U1 → UnitContent ub}
    (h : ∀ a b k, y (.init a b k) = y' (.init a b k)) :
    initialTable mu T cb q x ρ n p y = initialTable mu T cb q x ρ n p y' :=
  sum_congr rfl fun R _ => sum_congr rfl fun C _ => if_congr (by simp only [InitialOk, h]) rfl rfl

variable [Fintype N]

/-- All initial units held by a base party are present if its table at the beginning is not
zero. -/
theorem initialTable_ne_none {np : N → Bool → Fin (K + K + A')}
    {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {p : Fin (K + K)} {y : UnitId (K + K) U0 N U1 → UnitContent ub}
    (h : initialTable mu T cb q x ρ (fun a b => n a b) p y ≠ 0) :
    ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder np) (Fin.castAdd A' p) id → y id ≠ none := by
  obtain ⟨R, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨⟨-, h1, h2⟩, -⟩ := ite_ne_right_iff.1 h
  rintro (⟨a, b, k⟩ | ⟨ν, k⟩) hid hp <;>
    grind [UnitId.holds_init, unitsOf_eq_none, Fin.castAdd_inj, init_mem_initialUnits,
      new_notMem_initialUnits]

end Properties

end Tables

end Cslib.Circuits.Arithmetic.Separation.Cut
