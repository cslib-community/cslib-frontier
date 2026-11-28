/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.InitialCounts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.AllRuns
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Generators
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.GroupTime
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Instances
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Numbers
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ProgramSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.ScriptSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.TemplateCost
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Theorem
import CslibFrontier.Foundations.Data.BitString.Binary
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
  (under hypotheses), and for two base parties with too many units (closed).
* One cut: the integers have a finite table of generators; and, under hypotheses, the cut of the
  dealing program with weaker bounds, the cost of its templates along its runs, and its size at a
  scale.
* Numbers: closed examples of the numbers of units, row data and names, of a binary value, of
  the time of a small dealing program, and of the bounds of one cut at the scale `10000`; under
  hypotheses, the cut of the dealing program with the numbers of Theorem J.3. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SeparationDealing

open Cslib.BitString (lsbValue lsbValue_eq_binaryValue_reverse)

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

/-! ### One cut, its costs and its size -/

/-- The integers have a finite table of named generators in which every integer is the value of a
formula. -/
example : ∃ θ : List Bool → ℤ, (Function.support θ).Finite ∧ ∀ a, ∃ w : WE, w.val θ = a :=
  WE.exists_table ℤ

/-- **One cut, with weaker bounds.** Under the hypotheses of the dealing theorem, the dealing
program also cuts into pieces of size at most `s' + 1`, with at most `mm + 1` pieces, in time
`2 * t`. -/
example [DecidableEq Γ] {θ : List Bool → F} {mu : Tape.Letter S Unit Γ → Matrix Q Q F}
    (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D nI pS) [DecidablePred tab.Valid]
    [∀ n o x, Decidable (P.Good n o x)] {qn : Q → ℕ} {tg : M.Role → ℕ}
    {bT bub nl nub : List Bool} {hD : 1 < D} {hmm : mm ≤ D} {gp : Tree}
    {cb : Option Γ → Fin c → Bool} {bt : Bool → Γ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D}
    {τ s τ' s' t T ℓ : ℕ} (hK : 0 < K) (hnl : lsbValue nl = ℓ) (hnub : lsbValue nub = ub)
    (hU : ∀ z : Tree, z.size ≤ s → Plain θ τ z →
      Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) = pv θ z)
    (hval : ∀ z : Tree, z.size ≤ s → Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
            ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
              ∑ b ∈ Play.common (none : UnitContent ub)
                (Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)),
                ∏ g, P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b
            else 0 else 0 else 0 else 0)
    (hdoes : ∀ z : Tree, z.size ≤ s → ∃ Qs : List (F × Tree),
      Does θ (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1) z Qs t ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (Function.extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt))))
          fun _ => .nil),
        q.2 = listT (((List.finRange mm).map (C.pieceTm tab tg bT bub hD hmm gp)).map
          fun t => t.expand σ)) ∧
      wsum Qs (pvProd θ) = ((execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
        (Function.extend C.name (initialState (partTree cb (parts ℓ ((tbits z).map bt))))
          fun _ => .nil)).map fun σ => (((List.finRange mm).map
            (C.pieceTm tab tg bT bub hD hmm gp)).map fun t => pv θ (t.expand σ)).prod).sum)
    (hpc : ∀ z : Tree, z.size ≤ s → ∀ (q : Fin (K + 1) → Q)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.Channel → Fin U1) (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) (g : Fin mm),
      ValidRows ρ → tab.Valid n → (∀ x, P.Good n o x) →
      (∀ u, b u ≠ none ↔ u ∈ Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩)
        (P.cur n o E)) →
      let y := Tree.cons gp (scriptEnc bT bub (groupScript qn cb P q (parts ℓ ((tbits z).map bt))
        ρ n o (grp ⟨n, o⟩) g C.key C.dkey tg b))
      y.size ≤ s' ∧ Plain θ τ' y ∧
        pv θ y = P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b) :
    IsCut θ τ s τ' (s' + 1) (mm + 1) (2 * t)
      (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1).code :=
  (isCut_dealProgram C tab hK hnl hnub hU hval hdoes hpc).mono le_rfl (by omega) (by omega)
    (by omega)

/-- **The templates along the runs.** At every state after all steps of the dealing program,
filling the template of every piece costs at most `pieceBound Lc X`. -/
example (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D nI pS) [DecidablePred tab.Valid]
    [∀ n o x, Decidable (P.Good n o x)] (hK : 0 < K) {pt : Fin K → Tree} {qn : Q → ℕ} {i e : Q}
    {hU0 : U0 < D} {hU1 : U1 ≤ D} {hD : 1 < D} {hmm : mm ≤ D} {Lc X : ℕ}
    (hnm : ∀ y, (C.name y).length ≤ Lc) (hdc : ∀ d, (C.digit d).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X)
    (hId : Fintype.card (UnitId (K + K) U0 M.Channel U1) ≤ X)
    (hSl : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X)
    (hCn : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X) (hXU0 : U0 + 1 ≤ X)
    (hR : Fintype.card M.Role ≤ X) (tg : M.Role → ℕ) (bT bub : List Bool) (gp : Tree)
    {σ : List Bool → Tree} (hσ : σ ∈ execAll ub (C.dealSteps tab qn i e hU0 hU1 ++ C.contentSteps)
      (Function.extend C.name (initialState pt) fun _ => .nil)) (g : Fin mm) :
    (C.pieceTm tab tg bT bub hD hmm gp g).cost σ ≤ pieceBound Lc X := by
  obtain ⟨q, ρ, n, o, b, st, -, -, -, -, -, hst, rfl⟩ := mem_execAll_allSteps C tab hK hσ
  exact cost_pieceTm_le hst hnm hdc hS hK2 hId hSl hCn hXU0 hR tg bT bub hmm gp g

/-- **The size of the dealing program at a scale.** If `X * Lc ≤ v`, the dealing program has size
at most `(dealBaseSize + 3000) * v ^ 4`. -/
example (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D nI pS) {qn : Q → ℕ} {tg : M.Role → ℕ}
    {X Lc v : ℕ} (H : C.SizeBounds qn tg X Lc) (hv : X * Lc ≤ v) (hmX : mm ≤ X) (hc : c ≤ X)
    {nl nub bT bub : List Bool} (hnl : nl.length ≤ Lc) (hnub : nub.length ≤ Lc)
    (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc) (hD : 1 < D) (hmm : mm ≤ D) {gp : Tree}
    (hgp : gp.size ≤ X) (cb : Option Γ → Fin c → Bool) (bt : Bool → Γ) (i e : Q)
    (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    (C.dealProgram tab qn tg bT bub nl nub hD hmm gp cb bt i e hU0 hU1).code.size ≤
      (dealBaseSize + 3000) * v ^ 4 :=
  (size_dealProgram_le tab H hmX hc hnl hnub hbT hbub hmm hgp cb bt i e hU0 hU1).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hv 4))

/-! ### Numbers -/

/-- Two base parties with one unit per string and one channel of three units have seven units. -/
example : Fintype.card (UnitId 2 1 Unit 3) = 7 := by
  rw [UnitId.card_eq]
  rfl

/-- Two parties have eight row data. -/
example : Fintype.card (RowData 2) = 8 := RowData.card_eq 2

/-- With one block, one move, one step, and one tape, channel and unit, there are `39` names. -/
example : Fintype.card (Name 1 1 1 Unit Unit Unit) = 39 := by
  rw [Name.card_eq]
  simp

/-- The word `[true, false]` is `2`, most significant bit first. -/
example : BitString.binaryValue [true, false] = 2 := by
  rw [show [true, false] = [false, true].reverse from rfl, ← lsbValue_eq_binaryValue_reverse]
  rfl

/-- The time bound of the dealing program with codes of two bits, numbers at most `3`, one block,
two groups, units of four bits, one cut unit and an argument of size `5`. -/
example : dealTime 2 3 1 2 4 1 5 = 355586 := by
  norm_num [dealTime, stepBound, pieceBound]

/-- The numbers of one cut at the scale `v = m = 10000`: an instance of size `5` and time
`τ = 10000 ^ 321`, cut by `2` into two blocks of three steps with parts of three letters, units of
two bits, three units at the beginning of a base party, codes of four bits and letters of one bit,
`X = 2`, and two groups, each with one base party, one unit with one holder in it and five cells
and units read by its roles. -/
private theorem cutNumbers :
    CutNumbers 10000 2 (10000 ^ 321) 5 2 3 3 2 3 2 4 10000 1 1 1 5 2 where
  le_m := le_rfl
  m_le_v := le_rfl
  k_pos := by norm_num
  k_le_K := le_rfl
  KT_le := le_trans (b := 1 * 10000) (by norm_num)
    (Nat.mul_le_mul_right _ (one_le_pow₀ (by norm_num)))
  ℓ_eq := by norm_num
  ub_pos := by norm_num
  ub_le := by norm_num
  lh_mul_ub_le := by norm_num
  Lc_lt := by norm_num
  c_le := by norm_num
  K_le_X := le_rfl
  ιb_mul_le := by norm_num
  ιb_le_X := by norm_num
  bd_le := by
    rw [show 321 = 21 + 300 from rfl, pow_add]
    generalize 10000 ^ 300 = a
    exact le_trans (b := 10000 ^ 21 * a) (Nat.mul_le_mul_right _ (by norm_num))
      (Nat.le_mul_of_pos_right _ (by positivity))
  ev_le := le_trans (b := 1 * 10000 ^ 2) (by norm_num)
    (Nat.mul_le_mul_right _ (one_le_pow₀ (by norm_num)))
  mm_le := by norm_num
  mm_le_X := le_rfl
  small := by
    rw [show 321 = 21 + 300 from rfl, pow_add]
    exact Nat.mul_le_mul_right _ (by norm_num)

/-- **The time of the dealing program at the scale `10000`**, with at most `2 * 1` cut units. -/
example : dealTime 4 2 2 2 2 (2 * 1) 5 ≤ (5 + 10000 ^ 321 * 2 / 10000 ^ 256) * 10000 ^ 10 :=
  cutNumbers.dealTime_le

/-- **The size of the pieces at the scale `10000`.** -/
example : 2 + 1 + (200 * 2 ^ 3 * 4 + 1 * 3 * (4 * 1 + 2) + 1 * (4 * 2)) ≤
    (5 / 2 + 10000 ^ 321 / 10000 ^ 256) * 10000 ^ 10 :=
  cutNumbers.size_le

/-- **The time of the pieces at the scale `10000`**, for `κ = 3`. -/
example : 3 * ((4 + 1) * (3 + 2 + 2) + 1 * 3 + 3 * (5 + 1 * 3) * (2 + 4 + 1) + 10 * 2 ^ 3) ≤
    10000 ^ 321 * 10000 ^ 10 / 2 :=
  cutNumbers.time_le (by norm_num)

section OneCut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {K A' E U0 U1 D nI pS mm c : ℕ}
  {M : Moves F (K + K + A') E} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm}

/-- **One cut by the dealing program, with the numbers of Theorem J.3.** If GROUP evaluates the
groups, the numbers of the cut are those of `CutNumbers`, and every choice that passes the checks
has at most `lh` units at the beginning of every base party and at most `ev` cells and units read
by the roles of every group, then the dealing program cuts `(τ, s)` into
`(τ * m ^ 10 / k, (s / k + τ / v ^ 256) * m ^ 10)` with at most `k * m ^ 10` pieces in
`(s + τ * k / v ^ 256) * m ^ 10` steps. -/
example {θ : List Bool → F} {mu : Tape.Letter S Unit Γ → Matrix Q Q F}
    {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : Law F, L.Role)} {qn : Q → ℕ}
    {tg : M.Role → ℕ} {GROUP : Fm} {κ : ℕ} {bT bub nl nub : List Bool} {hD : 1 < D}
    {hmm : mm ≤ D} {bt : Bool → Γ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D}
    {v τ s k T ℓ ub lh X Lc m cap bd ιb ev : ℕ} (C : Codes S M U0 U1 D pS)
    (tab : SlpTab P grp D nI pS) [DecidablePred tab.Valid] [∀ n o x, Decidable (P.Good n o x)]
    (hK : 0 < K) (H : C.SizeBounds qn tg X Lc) (hkey : Function.Injective (Sum.elim C.key C.dkey))
    (hGR : EvaluatesGroups θ mu cb kinds qn GROUP κ)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.law r.1, r.2⟩) (hP : P.Ok cap)
    (hT : BitString.binaryValue bT = T) (hub : BitString.binaryValue bub = ub)
    (hnl : lsbValue nl = ℓ) (hnub : lsbValue nub = ub) (hℓ : ℓ ≤ T) (hlbT : bT.length ≤ Lc)
    (hlbub : bub.length ≤ Lc) (hlnl : nl.length ≤ Lc) (hlnub : nub.length ≤ Lc)
    (hN : CutNumbers v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm) (hκ : κ ≤ m)
    (hU : ∀ z : Tree, z.size ≤ s → Plain θ τ z →
      Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) = pv θ z)
    (hval : ∀ z : Tree, z.size ≤ s → Tape.runVal mu i e (K * T) (fun _ => (tbits z).map bt) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1), if tab.Valid n then
            ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
              ∑ b ∈ Play.common (none : UnitContent ub)
                (Play.cutUnits (UnitId.holder M.channelParty) (grp ⟨n, o⟩) (P.cur n o E)),
                ∏ g, P.groupValue mu T cb q (parts ℓ ((tbits z).map bt)) ρ n o (grp ⟨n, o⟩) g b
            else 0 else 0 else 0 else 0)
    (hbd : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ g,
      #((P.cur n o E).filter (OneIn (UnitId.holder M.channelParty) (grp ⟨n, o⟩) g)) ≤ bd)
    (hbase : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ g,
      #{p : Fin (K + K) | grp ⟨n, o⟩ (Fin.castAdd A' p) = g} ≤ ιb)
    (hlh : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ p, ∑ b, ((n p b : ℕ) + n b p) ≤ lh)
    (hev : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ g,
      cellCount n o (grp ⟨n, o⟩) g + roleUnitCount P n o (grp ⟨n, o⟩) g ≤ ev)
    (hcount : ∀ n o, tab.Valid n → (∀ x, P.Good n o x) → ∀ y, P.count n o y ≤ X)
    (hgp : GROUP.code.size ≤ X) :
    IsCut θ τ s (τ * m ^ 10 / k) ((s / k + τ / v ^ 256) * m ^ 10) (k * m ^ 10)
      ((s + τ * k / v ^ 256) * m ^ 10)
      (C.dealProgram tab qn tg bT bub nl nub hD hmm GROUP.code cb bt i e hU0 hU1).code :=
  (isCut_dealProgram_of_evaluatesGroups tab hK H hkey hGR hkind hP hT hub hN.ub_pos hnl hnub hℓ
    hlbT hlbub hlnl hlnub hU hval hbd hbase hcount hgp fun q x ρ n o g b hx hn ho =>
      groupTime_le_of_sizeBounds H hT hub hlbT hlbub hP hx (hbase n o hn ho g) hN.ιb_le_X
        (fun p _ => hlh n o hn ho p) (hev n o hn ho g) b).mono (hN.time_le hκ) hN.size_le
    (hN.mm_le.trans (Nat.mul_le_mul_left k (Nat.le_self_pow (by norm_num) m))) hN.dealTime_le

end OneCut

end CslibFrontierTests.SeparationDealing
