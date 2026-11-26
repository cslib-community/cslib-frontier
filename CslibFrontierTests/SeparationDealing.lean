/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.InitialCounts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.AllRuns
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ScriptSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Theorem
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the dealing program, as a client that sees only the public statements.

* Closed examples: the flags of a row as a tree, row data valid after a given party, a unit with
  one holder in a group and one with both, a value of the trie of a function, and the dealing
  program with no steps and no templates.
* For the plan of two parties with one move with the equality law (the fixtures of
  `CslibFrontierTests.SeparationGroupTheorem`): the size of the script of the group of both
  parties, for concrete arguments.
* Under hypotheses: the sum over all runs of the dealing program with the scripts that its
  templates give.
* The units of a base party whose table at the beginning is not zero: for the parts of an input
  (under hypotheses), and for two base parties with too many units (closed). -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SeparationDealing

open Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut
  Cslib.Circuits.Arithmetic.Separation.Interpreter Cslib.Circuits.Arithmetic.Separation.Dealing
  Cslib.Circuits.Arithmetic.Separation.GroupProgram Finset

/-! ### Closed examples -/

/-- The flags of a row of a party that writes for the partners `1` to `3`, last partner first. -/
example : flagsTree (⟨false, 1, 3⟩ : RowData 4) =
    listT [Tree.num 1, Tree.num 2, Tree.num 1, Tree.num 0] := by
  decide

/-- Row data from the partner `1` to `3` are valid after a row that ends at `1`, not after a row
that ends at `2`. -/
example : RowValidAfter 1 (⟨false, 1, 3⟩ : RowData 4) ∧
    ¬RowValidAfter 2 (⟨false, 1, 3⟩ : RowData 4) := by
  decide

/-- The unit `()` with the holders `false` and `true` has one holder in the group `true`. -/
example : OneIn (fun (_ : Unit) (d : Bool) => d) id true () := by decide

/-- A unit whose two holders are both in the group `()` does not have exactly one holder in it. -/
example : ¬OneIn (fun (_ : Unit) (_ : Bool) => ()) id () () := by
  rw [oneIn_iff, not_not]

/-- The trie of the bits `bit b` at the paths `[b]` has `bit true` at `[true]`. -/
example : tget [true] (trieOf (fun b : Bool => [b]) Tree.bit) = Tree.bit true :=
  tget_trieOf (fun _ _ h => List.singleton_injective h) _ true

/-- With no steps and no templates, the dealing program has outcomes of weighted sum `1`. -/
example (z : Tree) : ∃ Q : List (ℤ × Tree),
    Does (fun _ => 0) (dealFormula .nil .nil [] [] [] [] [] []) z Q
      (60 * z.size + z.size * 100 + 300) ∧
      wsum Q (pvProd fun _ => 0) = 1 := by
  obtain ⟨Q, hQ, -, hw⟩ := dealFormula_does (A := ℤ) (θ := fun _ => 0) .nil .nil [] [] [] [] [] []
    z (Ln := 0) (by simp) (I := fun l _ => l = []) (c := fun _ => 0) (ct := 0) (c9 := 0)
    (fun _ _ _ h => absurd h (List.cons_ne_nil _ _)) rfl fun σ _ =>
      ⟨⟨fun l _ => l = [], fun _ => 0, fun _ _ _ h => absurd h (List.cons_ne_nil _ _), rfl,
        le_rfl⟩, fun _ _ _ h => absurd h List.not_mem_nil⟩
  exact ⟨Q, hQ.mono (by simp), by simpa [execAll] using hw⟩

/-! ### The script of a group for one move -/

/-- The equality law of `CslibFrontierTests.SeparationGroupTheorem`. -/
private def equalityLaw (F : Type) [CommSemiring F] : Law F where
  Role := Bool
  Slot := Unit
  Channel := Unit
  Index := Unit
  slotEnd _ d := d
  slotEnd_ne _ := by decide
  channelEnd _ d := d
  channelEnd_ne _ := by decide
  labelLength := 0
  label _ := Fin.elim0
  label_injective _ _ _ := rfl
  length _ _ := 1
  table p _ x g := if x ⟨(), p, rfl⟩ = g ⟨(), p, rfl⟩ 0 then 1 else 0
  identity X := by
    rw [Fintype.sum_unique, ← ((Equiv.funUnique Unit (BitString 1)).trans
      (Equiv.funUnique (Fin 1) Bool)).symm.sum_comp, Fintype.sum_bool]
    have hg (b : Bool) : ((Equiv.funUnique Unit (BitString 1)).trans
        (Equiv.funUnique (Fin 1) Bool)).symm b () 0 = b := rfl
    simp only [Fintype.prod_bool, hg]
    rcases Bool.eq_false_or_eq_true (X false ()) with hf | hf <;>
      rcases Bool.eq_false_or_eq_true (X true ()) with ht | ht <;> simp [hf, ht]
  connected _ _ _ _ := rfl

/-- One move with the equality law between the parties `0` and `1`. -/
private def moves (F : Type) [CommSemiring F] : Moves F (1 + 1 + 0) 1 where
  law _ := equalityLaw F
  party _ (d : Bool) := if d then 1 else 0
  party_injective _ := by
    rintro (_ | _) (_ | _) h <;> first | rfl | simp at h

/-- The plan that gives the units from the party `0` to the party `1` at the slot of the move. -/
private def plan (F : Type) [CommSemiring F] (U0 U1 : ℕ) : Plan (moves F) U0 U1 where
  given n _ _ := (univ.filter fun k : Fin U0 => (k : ℕ) < n 0 1).image (UnitId.init 0 1)
  count _ _ _ := U0
  Good _ _ _ := True

/-- The number of a role among the two roles of the equality law. -/
private def tag (r : (moves ℤ).Role) : ℕ := (show Bool from r.2).toNat

/-- **The size of a tiny script.** The script of the group of both parties, with one input
letter and no units, has size at most `200 * 4 ^ 3` plus `6` for the letter. -/
example (ρ : Option Empty → Fin 2 → RowData 2) (cb : Option Unit → Fin 1 → Bool) :
    (scriptEnc [] [] (groupScript (fun _ => 0) cb (plan ℤ 0 1) (fun _ => ()) (fun _ => [()]) ρ
      (fun _ _ => 0) (fun _ => 0) (fun _ => ()) () (fun _ => []) (fun _ => []) tag
      (fun _ => (none : UnitContent 0)))).size ≤
      200 * 4 ^ 3 * 1 + (∑ κ : Fin 1 with (fun _ => ()) (Fin.castAdd 0 (Fin.natAdd 1 κ)) = (),
        ([()] : List Unit).length) * (4 * 1 + 2) +
      (((plan ℤ 0 1).cur (fun _ _ => 0) (fun _ => 0) 1).filter
        (OneIn (UnitId.holder (moves ℤ).channelParty) (fun _ => ()) ())).card * (4 * 0) :=
  size_scriptEnc_le (X := 4) (Lc := 1) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by decide) (by decide)
    (fun _ => (Fintype.card_subtype_le _).trans (show Fintype.card Unit ≤ 4 by decide))
    (fun _ => (Fintype.card_subtype_le _).trans (show Fintype.card Unit ≤ 4 by decide))
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => (Bool.toNat_le _).trans (by norm_num))
    (fun _ => by simp [plan]) (by simp) (by simp) _

/-! ### The dealing theorem under hypotheses -/

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K A' E U0 U1 D nI pS mm ub c : ℕ} {M : Moves F (K + K + A') E}
  {P : Plan M U0 U1} {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}

/-- **The runs of the dealing program, with their scripts.** For the parts of the codes of the
letters of `x`, there are states with the values of the end such that the sum over the runs of the
dealing program is the sum over the choices that pass the checks and over the contents of the cut
units, and at each of them the template of the script of every group gives the script of the
group. -/
example (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D nI pS) [DecidablePred tab.Valid]
    [∀ n o x, Decidable (P.Good n o x)] (hK : 0 < K) (cb : Option Γ → Fin c → Bool)
    (x : Fin K → List Γ) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) (hD : 1 < D)
    (hmm : mm ≤ D) (tg : M.Role → ℕ) (bT bub : List Bool) :
    ∃ st : (Fin (K + 1) → Q) → (Option S → Fin (K + K) → RowData (K + K)) →
      (Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) → (M.Channel → Fin U1) →
        (UnitId (K + K) U0 M.Channel U1 → UnitContent ub) → PlanName S M U0 U1 pS → Tree,
      (∀ q ρ n o b g, (C.scriptTm tab tg bT bub hD hmm g).expand
        (Function.extend C.name (st q ρ n o b) fun _ => .nil) =
          scriptEnc bT bub (groupScript qn cb P q x ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg b)) ∧
      ((execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (Function.extend C.name
          (initialState fun κ => wordsEnc (((x κ).map (letterCode cb)).reverse))
            fun _ => .nil)).map fun _ => (1 : ℤ)).sum =
        ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
          ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
            ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
              ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
                ∑ b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub,
                  if ∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty)
                    (grp ⟨n, o⟩) (P.cur n o E) then 1 else 0
              else 0 else 0 else 0 else 0 := by
  obtain ⟨st, hf, hs⟩ := sum_execAll_allSteps (ub := ub) C tab
    (fun κ => wordsEnc (((x κ).map (letterCode cb)).reverse)) qn hU0 hU1 hK i e
  exact ⟨st, fun q ρ n o b g => expand_scriptTm (hf q ρ n o b) (fun _ => rfl) tg bT bub g,
    hs ℤ fun _ => 1⟩

/-! ### The units of a base party at the beginning -/

/-- **The units of a base party at the beginning** (Lemma I.2, its last bound), as the
proposition on pieces uses it: for the parts of `ℓ ≤ T` letters of the input and numbers of units
below `U0 + 1`, a base party whose table at the beginning is not zero holds at most
`2 * ((T + (K + K) * (|S| + 1)) * c / ub + (K + K))` units. -/
example [DecidableEq Γ] {N : Type} {T ℓ : ℕ} {mu : Tape.Letter S Unit Γ → Matrix Q Q F}
    {cb : Option Γ → Fin c → Bool} (hℓ : ℓ ≤ T) (u : Unit → List Γ) (q : Fin (K + 1) → Q)
    (ρ : Option S → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (p : Fin (K + K)) (y : UnitId (K + K) U0 N U1 → UnitContent ub)
    (h : initialTable mu T cb q (parts ℓ (u ())) ρ (fun a b => n a b) p y ≠ 0) :
    ∑ b, ((n p b : ℕ) + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) :=
  sum_count_le_of_initialTable_ne_zero (fun _ => (length_parts_le _ _ _).trans hℓ) h

/-- With one block of one step, one tape, and codes and units of one bit, a base party whose
table at the beginning is not zero holds at most `2 * ((1 + 2 * 2) * 1 / 1 + 2) = 14` units. So
the table of a base party with four units to and from each of the two base parties is zero. -/
example (mu : Tape.Letter Unit Unit Unit → Matrix Unit Unit ℤ) (cb : Option Unit → Fin 1 → Bool)
    (q : Fin (1 + 1) → Unit) (ρ : Option Unit → RowData (1 + 1)) (p : Fin (1 + 1))
    (y : UnitId (1 + 1) 4 Empty 0 → UnitContent 1) :
    initialTable mu 1 cb q (fun _ => []) ρ (fun _ _ => 4) p y = 0 := by
  by_contra h
  have := sum_count_le_of_initialTable_ne_zero (fun _ => Nat.zero_le 1) h
  simp at this

end CslibFrontierTests.SeparationDealing
