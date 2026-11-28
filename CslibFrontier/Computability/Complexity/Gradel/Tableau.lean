/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ImmermanVardi.Tableau.Step
public import CslibFrontier.Logics.FirstOrder.Ordered.Constants
public import CslibFrontier.Logics.SecondOrder.Horn
import CslibFrontier.Computability.Complexity.ImmermanVardi.Tableau.FixedPoint
import CslibFrontier.Logics.FirstOrder.Ordered.BitArithmetic
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-!
# Deterministic polynomial-time tableaux as SO∃-Horn sentences

Given a deterministic native multi-tape Turing machine `tm` and first-order formulas `inputFormula`
interpreting the three input-tape symbols over `Ordered.language L`, this module constructs a single
uniform SO∃-Horn sentence `acceptanceHornSentence L tm inputFormula` over `Ordered.language L`.

Its definite clauses mirror the positive local rules `ImmermanVardi.Tableau.rowStep` and initial
configuration `ImmermanVardi.Tableau.initial`, using auxiliary relation variables for positive
work-tape reads, running situations, head-elsewhere witnesses, and clamped/signed head predecessor
positions. On any finite ordered domain `Fin B` (`2 ≤ B`) large enough to hold the input plus both
endmarkers (`input.length + 1 < B`), the `.tag` relations in the sentence's least model equal the
exact run rows `row (tm.runFrom (tm.initCfg input) t.val)`. Goal clauses at the maximum time `B - 1`
forbid every non-halted control state `some s` and every output view other than `OutView.one true`,
so the sentence holds on `Fin B` iff `tm` has halted with output `[true]` by step `B - 1`.

## Main definitions

* `Cslib.Complexity.Gradel.Tableau.TableauVar`: binary relation variables of the Horn tableau
  sentence.
* `Cslib.Complexity.Gradel.Tableau.acceptanceHornSentence`: uniform SO∃-Horn sentence expressing
  bounded deterministic machine acceptance.

## Main results

* `Cslib.Complexity.Gradel.Tableau.realize_acceptanceHornSentence`: the sentence holds on `Fin B`
  iff the machine halts with output `[true]` within `B - 1` steps.

## References

* [E. Grädel, *Finite Model Theory and Descriptive Complexity*][Gradel2007], Theorem 3.2.18
  (p. 148), encoding polynomial-time deterministic computation tableaux by Horn clauses.
* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for the SO∃-Horn characterization of polynomial time. Section and theorem locators are
  unverified.
-/

public section

namespace Cslib.Complexity.Gradel.Tableau

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature
open FirstOrder Language
open Cslib.Logic
open Cslib.Logic.FO
open Cslib.Complexity.ImmermanVardi.Tableau

/-- Binary relation variables of the deterministic computation tableau in SO∃-Horn form.
All variables have arity `2` (`(time, pos)`), ignoring the position coordinate on global features
such as `.read`, `.state`, and `.out`. -/
inductive TableauVar (m : ℕ) (State : Type) where
  /-- Basic row feature `q` at `(time, pos)`. -/
  | tag (q : Tag m State)
  /-- Positive work-head read witness `read R i s` at `(time, _)`. -/
  | read (i : Fin m) (s : Option Bool)
  /-- Positive running-situation witness `situation input R y a` at `(time, pos)`. -/
  | sit (y : Situation m State)
  /-- Positive head-elsewhere witness `elsewhere R i sign a` at `(time, pos)`. -/
  | elsewhere (i : Fin m) (sign : Bool)
  /-- Input-head predecessor `inputPrev input R d a` at `(time, pos)`. -/
  | inPrev (d : SignType)
  /-- Work-head predecessor `headPrev R i sign d a` at `(time, pos)`. -/
  | headPrev (i : Fin m) (sign : Bool) (d : SignType)

private def signTypeEquiv : SignType ≃ Fin 3 where
  toFun
    | .zero => 0
    | .neg => 1
    | .pos => 2
  invFun
    | ⟨0, _⟩ => .zero
    | ⟨1, _⟩ => .neg
    | ⟨2, _⟩ => .pos
  left_inv d := by cases d <;> rfl
  right_inv k := by fin_cases k <;> rfl

private instance : Finite SignType := Finite.of_equiv (Fin 3) signTypeEquiv.symm

private def tableauVarEquiv {m : ℕ} {State : Type} :
    TableauVar m State ≃
      Tag m State ⊕ (Fin m × Option Bool) ⊕ Situation m State ⊕
        (Fin m × Bool) ⊕ SignType ⊕ (Fin m × Bool × SignType) where
  toFun
    | .tag q => .inl q
    | .read i s => .inr (.inl (i, s))
    | .sit y => .inr (.inr (.inl y))
    | .elsewhere i sign => .inr (.inr (.inr (.inl (i, sign))))
    | .inPrev d => .inr (.inr (.inr (.inr (.inl d))))
    | .headPrev i sign d => .inr (.inr (.inr (.inr (.inr (i, sign, d)))))
  invFun
    | .inl q => .tag q
    | .inr (.inl (i, s)) => .read i s
    | .inr (.inr (.inl y)) => .sit y
    | .inr (.inr (.inr (.inl (i, sign)))) => .elsewhere i sign
    | .inr (.inr (.inr (.inr (.inl d)))) => .inPrev d
    | .inr (.inr (.inr (.inr (.inr (i, sign, d))))) => .headPrev i sign d
  left_inv v := by cases v <;> rfl
  right_inv x := by
    rcases x with q | ⟨i, s⟩ | y | ⟨i, sign⟩ | d | ⟨i, sign, d⟩ <;> rfl

instance {m : ℕ} {State : Type} [Finite State] : Finite (TableauVar m State) := by
  let _ := Fintype.ofFinite State
  exact Finite.of_equiv _ tableauVarEquiv.symm

private noncomputable def univList (α : Type) [Fintype α] : List α :=
  (Finset.univ : Finset α).toList

private theorem mem_univList {α : Type} [Fintype α] (x : α) : x ∈ univList α :=
  Finset.mem_toList.mpr (Finset.mem_univ x)

private def signs : List SignType := [.zero, .neg, .pos]

private theorem mem_signs (d : SignType) : d ∈ signs := by
  cases d <;> decide

private def rejectViews : List OutView := [.empty, .one false, .many]

private theorem mem_rejectViews_iff (o : OutView) : o ∈ rejectViews ↔ o ≠ .one true := by
  rcases o with _ | (_ | _) | _ <;> decide

/-! ### Guards and atoms -/

section Syntax

variable (L : Language) {m : ℕ} {State : Type}

private noncomputable def zeroGuard {w : ℕ} (a : Fin w) : (Ordered.language L).Formula (Fin w) :=
  Ordered.natEq L 0 (.var a)

private noncomputable def oneGuard {w : ℕ} (a : Fin w) : (Ordered.language L).Formula (Fin w) :=
  Ordered.natEq L 1 (.var a)

private noncomputable def succGuard {w : ℕ} (a b : Fin w) : (Ordered.language L).Formula (Fin w) :=
  Ordered.addEq L (.var a) (Ordered.one L) (.var b)

private def maxGuard {w : ℕ} (a : Fin w) : (Ordered.language L).Formula (Fin w) :=
  Term.equal (.var a) (Ordered.max L)

private def inputGuard {L : Language}
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {w : ℕ} (s : Option Bool) (a : Fin w) : (Ordered.language L).Formula (Fin w) :=
  (inputFormula s).relabel fun _ => a

private abbrev TAtom (m : ℕ) (State : Type) (w : ℕ) :=
  ESO.Horn.Atom (fun _ : TableauVar m State => 2) (Fin w)

private abbrev TClause (L : Language) (m : ℕ) (State : Type) :=
  ESO.Horn.Clause (Ordered.language L) (fun _ : TableauVar m State => 2)

private def tagAtom {w : ℕ} (q : Tag m State) (t a : Fin w) : TAtom m State w :=
  ⟨.tag q, ![t, a]⟩

private def readAtom {w : ℕ} (i : Fin m) (s : Option Bool) (t : Fin w) : TAtom m State w :=
  ⟨.read i s, ![t, t]⟩

private def sitAtom {w : ℕ} (y : Situation m State) (t a : Fin w) : TAtom m State w :=
  ⟨.sit y, ![t, a]⟩

private def elsewhereAtom {w : ℕ} (i : Fin m) (sign : Bool) (t a : Fin w) : TAtom m State w :=
  ⟨.elsewhere i sign, ![t, a]⟩

private def inPrevAtom {w : ℕ} (d : SignType) (t a : Fin w) : TAtom m State w :=
  ⟨.inPrev d, ![t, a]⟩

private def headPrevAtom {w : ℕ} (i : Fin m) (sign : Bool) (d : SignType) (t a : Fin w) :
    TAtom m State w :=
  ⟨.headPrev i sign d, ![t, a]⟩

/-! ### Clauses -/

private def readClausesFor (i : Fin m) (s : Option Bool) : List (TClause L m State) :=
  [⟨2, ⊤, [tagAtom (.head i true) 0 1, tagAtom (.cell i true s) 0 1], some (readAtom i s 0)⟩,
   ⟨2, ⊤, [tagAtom (.head i false) 0 1, tagAtom (.cell i false s) 0 1], some (readAtom i s 0)⟩]

private abbrev sitClauseFor
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) :
    Situation m State → TClause L m State
  | ⟨qy, inSym, workSyms⟩ =>
    ⟨3, inputGuard inputFormula inSym 2,
      tagAtom (.state (some qy)) 0 1 :: tagAtom .inPos 0 2 ::
        (List.finRange m).map (fun i => readAtom i (workSyms i) 0),
      some (sitAtom ⟨qy, inSym, workSyms⟩ 0 1)⟩

private noncomputable def elsewhereClausesFor (i : Fin m) (sign : Bool) :
    List (TClause L m State) :=
  [⟨3, ∼(Term.equal (.var 2) (.var 1)), [tagAtom (.head i sign) 0 2],
      some (elsewhereAtom i sign 0 1)⟩,
   ⟨3, ∼(zeroGuard L 2 ⊓ zeroGuard L 1), [tagAtom (.head i (!sign)) 0 2],
      some (elsewhereAtom i sign 0 1)⟩]

private noncomputable def inPrevClausesFor
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) :
    SignType → List (TClause L m State)
  | .zero =>
    [⟨2, ⊤, [tagAtom .inPos 0 1], some (inPrevAtom .zero 0 1)⟩]
  | .neg =>
    [⟨2, zeroGuard L 1, [tagAtom .inPos 0 1], some (inPrevAtom .neg 0 1)⟩,
     ⟨3, succGuard L 1 2, [tagAtom .inPos 0 2], some (inPrevAtom .neg 0 1)⟩]
  | .pos =>
    [⟨2, ∼(zeroGuard L 1) ⊓ inputGuard inputFormula none 1,
        [tagAtom .inPos 0 1], some (inPrevAtom .pos 0 1)⟩,
     ⟨3, succGuard L 2 1 ⊓ (zeroGuard L 2 ⊔ ∼(inputGuard inputFormula none 2)),
        [tagAtom .inPos 0 2], some (inPrevAtom .pos 0 1)⟩]

private noncomputable def headPrevClausesFor (i : Fin m) (sign : Bool) (d : SignType) :
    List (TClause L m State) :=
  match (if sign then d else -d) with
  | .zero =>
    [⟨2, ⊤, [tagAtom (.head i sign) 0 1], some (headPrevAtom i sign d 0 1)⟩]
  | .neg =>
    [⟨3, succGuard L 1 2, [tagAtom (.head i sign) 0 2], some (headPrevAtom i sign d 0 1)⟩]
  | .pos =>
    [⟨3, zeroGuard L 1 ⊓ oneGuard L 2, [tagAtom (.head i (!sign)) 0 2],
        some (headPrevAtom i sign d 0 1)⟩,
     ⟨3, succGuard L 2 1, [tagAtom (.head i sign) 0 2], some (headPrevAtom i sign d 0 1)⟩]

private noncomputable def initClausesFor [DecidableEq State]
    (tm : MultiTapeTM m Bool State) : Tag m State → List (TClause L m State)
  | .state q =>
    if q = some tm.q₀ then [⟨2, zeroGuard L 0, [], some (tagAtom (.state q) 0 1)⟩] else []
  | .out o =>
    if o = .empty then [⟨2, zeroGuard L 0, [], some (tagAtom (.out o) 0 1)⟩] else []
  | .inPos =>
    [⟨2, zeroGuard L 0 ⊓ oneGuard L 1, [], some (tagAtom .inPos 0 1)⟩]
  | .head i sign =>
    [⟨2, zeroGuard L 0 ⊓ zeroGuard L 1, [], some (tagAtom (.head i sign) 0 1)⟩]
  | .cell i sign s =>
    if s = none then [⟨2, zeroGuard L 0, [], some (tagAtom (.cell i sign s) 0 1)⟩] else []

private noncomputable def stepBodies [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM m Bool State) : Tag m State → List (List (TAtom m State 3))
  | .state q =>
    (if q = none then [ [tagAtom (.state none) 0 2] ] else []) ++
      ((univList (Situation m State)).filter fun y => decide ((tm.actionOf y).state = q)).map
        fun y => [sitAtom y 0 2]
  | .out o =>
    [tagAtom (.state none) 0 2, tagAtom (.out o) 0 2] ::
      ((univList (Situation m State × OutView)).filter fun p =>
          let ⟨y, o'⟩ := p
          decide (o'.push (tm.actionOf y).output = o)).map
        fun p =>
          let ⟨y, o'⟩ := p
          [sitAtom y 0 2, tagAtom (.out o') 0 2]
  | .inPos =>
    [tagAtom (.state none) 0 2, tagAtom .inPos 0 2] ::
      (univList (Situation m State)).map fun y =>
        [sitAtom y 0 2, inPrevAtom (tm.actionOf y).inputTape 0 2]
  | .head i sign =>
    [tagAtom (.state none) 0 2, tagAtom (.head i sign) 0 2] ::
      (univList (Situation m State)).map fun y =>
        let ⟨_, dir⟩ := (tm.actionOf y).workTapes i
        [sitAtom y 0 2, headPrevAtom i sign dir 0 2]
  | .cell i sign s =>
    [tagAtom (.cell i sign s) 0 2, tagAtom (.state none) 0 2] ::
      [tagAtom (.cell i sign s) 0 2, elsewhereAtom i sign 0 2] ::
      ((univList (Situation m State × Option Bool)).filter fun p =>
          let ⟨y, s'⟩ := p
          let ⟨writeSym, _⟩ := (tm.actionOf y).workTapes i
          decide (writeSym.getD s' = s)).map
        fun p =>
          let ⟨y, s'⟩ := p
          [sitAtom y 0 2, tagAtom (.head i sign) 0 2, tagAtom (.cell i sign s') 0 2]

private noncomputable def stepClausesFor [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM m Bool State) (q : Tag m State) : List (TClause L m State) :=
  (stepBodies tm q).map fun body => ⟨3, succGuard L 0 1, body, some (tagAtom q 1 2)⟩

private noncomputable def definiteClauses [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) :
    List (TClause L m State) :=
  ((univList (Fin m × Option Bool)).flatMap fun ⟨i, s⟩ => readClausesFor L i s) ++
  ((univList (Situation m State)).map (sitClauseFor L inputFormula)) ++
  ((univList (Fin m × Bool)).flatMap fun ⟨i, sign⟩ => elsewhereClausesFor L i sign) ++
  (signs.flatMap (inPrevClausesFor L inputFormula)) ++
  ((univList (Fin m × Bool)).flatMap fun ⟨i, sign⟩ =>
    signs.flatMap fun d => headPrevClausesFor L i sign d) ++
  ((univList (Tag m State)).flatMap (initClausesFor L tm)) ++
  ((univList (Tag m State)).flatMap (stepClausesFor L tm))

private noncomputable def goalClauses [Fintype State] : List (TClause L m State) :=
  ((univList State).map fun s =>
      ⟨1, maxGuard L 0, [tagAtom (.state (some s)) 0 0], none⟩) ++
    (rejectViews.map fun o =>
      ⟨1, maxGuard L 0, [tagAtom (.out o) 0 0], none⟩)

private noncomputable abbrev tableauSentence [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) :
    ESO.Horn.Sentence (Ordered.language L) where
  Var := TableauVar m State
  arity := fun _ => 2
  clauses := definiteClauses L tm inputFormula ++ goalClauses L

/-- Uniform SO∃-Horn sentence over `Ordered.language L` expressing that `tm` halts with output
`[true]` by the maximum element of the domain. -/
noncomputable def acceptanceHornSentence [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) :
    ESO.Horn.Sentence (Ordered.language L) :=
  tableauSentence L tm inputFormula

end Syntax

/-! ### Semantics and least-model characterization -/

section Semantics

variable {L : Language} {B : ℕ} {m : ℕ} {State : Type}

private theorem comp_vec2 {α β : Type*} (v : α → β) (a b : α) :
    v ∘ ![a, b] = ![v a, v b] := by
  ext k
  fin_cases k <;> rfl

private abbrev Model (m : ℕ) (State : Type) (B : ℕ) :=
  TableauVar m State → Set (Fin 2 → Fin B)

private theorem holds_tagAtom {w : ℕ} (q : Tag m State) (t a : Fin w)
    (R : Model m State B) (v : Fin w → Fin B) :
    (tagAtom q t a).Holds R v ↔ ![v t, v a] ∈ R (.tag q) := by
  rw [ESO.Horn.Atom.Holds, tagAtom, comp_vec2]

private theorem holds_readAtom {w : ℕ} (i : Fin m) (s : Option Bool) (t : Fin w)
    (R : Model m State B) (v : Fin w → Fin B) :
    (readAtom (State := State) i s t).Holds R v ↔ ![v t, v t] ∈ R (.read i s) := by
  rw [ESO.Horn.Atom.Holds, readAtom, comp_vec2]

private theorem holds_sitAtom {w : ℕ} (y : Situation m State) (t a : Fin w)
    (R : Model m State B) (v : Fin w → Fin B) :
    (sitAtom y t a).Holds R v ↔ ![v t, v a] ∈ R (.sit y) := by
  rw [ESO.Horn.Atom.Holds, sitAtom, comp_vec2]

private theorem holds_elsewhereAtom {w : ℕ} (i : Fin m) (sign : Bool) (t a : Fin w)
    (R : Model m State B) (v : Fin w → Fin B) :
    (elsewhereAtom (State := State) i sign t a).Holds R v ↔
      ![v t, v a] ∈ R (.elsewhere i sign) := by
  rw [ESO.Horn.Atom.Holds, elsewhereAtom, comp_vec2]

private theorem holds_inPrevAtom {w : ℕ} (d : SignType) (t a : Fin w)
    (R : Model m State B) (v : Fin w → Fin B) :
    (inPrevAtom (m := m) (State := State) d t a).Holds R v ↔
      ![v t, v a] ∈ R (.inPrev d) := by
  rw [ESO.Horn.Atom.Holds, inPrevAtom, comp_vec2]

private theorem holds_headPrevAtom {w : ℕ} (i : Fin m) (sign : Bool) (d : SignType)
    (t a : Fin w) (R : Model m State B) (v : Fin w → Fin B) :
    (headPrevAtom (State := State) i sign d t a).Holds R v ↔
      ![v t, v a] ∈ R (.headPrev i sign d) := by
  rw [ESO.Horn.Atom.Holds, headPrevAtom, comp_vec2]

private theorem goalClause_head_none [Fintype State] {C : TClause L m State}
    (hC : C ∈ goalClauses (m := m) (State := State) L) : C.head = none := by
  simp only [goalClauses, List.mem_append, List.mem_map] at hC
  rcases hC with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

private def targetRow (tm : MultiTapeTM m Bool State) (input : List Bool) (t : Fin B) :
    Row m State B :=
  row (tm.runFrom (tm.initCfg input) t.val)

private def targetModel (B : ℕ) (tm : MultiTapeTM m Bool State) (input : List Bool) :
    Model m State B
  | .tag q => {v : Fin 2 → Fin B | targetRow tm input (v 0) q (v 1)}
  | .read i s => {v : Fin 2 → Fin B | ImmermanVardi.Tableau.read (targetRow tm input (v 0)) i s}
  | .sit y => {v : Fin 2 → Fin B | situation input (targetRow tm input (v 0)) y (v 1)}
  | .elsewhere i sign => {v : Fin 2 → Fin B | elsewhere (targetRow tm input (v 0)) i sign (v 1)}
  | .inPrev d => {v : Fin 2 → Fin B | inputPrev input (targetRow tm input (v 0)) d (v 1)}
  | .headPrev i sign d =>
    {v : Fin 2 → Fin B | headPrev (targetRow tm input (v 0)) i sign d (v 1)}

private theorem holds_tagAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (q : Tag m State) (t a : Fin w) (v : Fin w → Fin B) :
    (tagAtom q t a).Holds (targetModel B tm input) v ↔
      targetRow tm input (v t) q (v a) := by
  rw [holds_tagAtom]
  rfl

private theorem holds_readAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (i : Fin m) (s : Option Bool) (t : Fin w) (v : Fin w → Fin B) :
    (readAtom (State := State) i s t).Holds (targetModel B tm input) v ↔
      ImmermanVardi.Tableau.read (targetRow tm input (v t)) i s := by
  rw [holds_readAtom]
  rfl

private theorem holds_sitAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (y : Situation m State) (t a : Fin w) (v : Fin w → Fin B) :
    (sitAtom y t a).Holds (targetModel B tm input) v ↔
      situation input (targetRow tm input (v t)) y (v a) := by
  rw [holds_sitAtom]
  rfl

private theorem holds_elsewhereAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (i : Fin m) (sign : Bool) (t a : Fin w) (v : Fin w → Fin B) :
    (elsewhereAtom (State := State) i sign t a).Holds (targetModel B tm input) v ↔
      elsewhere (targetRow tm input (v t)) i sign (v a) := by
  rw [holds_elsewhereAtom]
  rfl

private theorem holds_inPrevAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (d : SignType) (t a : Fin w) (v : Fin w → Fin B) :
    (inPrevAtom (m := m) (State := State) d t a).Holds (targetModel B tm input) v ↔
      inputPrev input (targetRow tm input (v t)) d (v a) := by
  rw [holds_inPrevAtom]
  rfl

private theorem holds_headPrevAtom_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    {w : ℕ} (i : Fin m) (sign : Bool) (d : SignType) (t a : Fin w) (v : Fin w → Fin B) :
    (headPrevAtom (State := State) i sign d t a).Holds (targetModel B tm input) v ↔
      headPrev (targetRow tm input (v t)) i sign d (v a) := by
  rw [holds_headPrevAtom]
  rfl

variable [L.Structure (Fin B)] [Fact (2 ≤ B)]

private def maxFin (B : ℕ) [Fact (2 ≤ B)] : Fin B :=
  ⟨B - 1, Nat.sub_lt (by have := (Fact.out : 2 ≤ B); omega) (by omega)⟩

private theorem realize_zeroGuard {w : ℕ} (a : Fin w) (v : Fin w → Fin B) :
    (zeroGuard L a).Realize v ↔ (v a).val = 0 :=
  Ordered.realize_natEq 0 (.var a) v

private theorem realize_oneGuard {w : ℕ} (a : Fin w) (v : Fin w → Fin B) :
    (oneGuard L a).Realize v ↔ (v a).val = 1 :=
  Ordered.realize_natEq 1 (.var a) v

private theorem realize_succGuard {w : ℕ} (a b : Fin w) (v : Fin w → Fin B) :
    (succGuard L a b).Realize v ↔ (v a).val + 1 = (v b).val := by
  rw [succGuard, Ordered.realize_addEq, Term.realize_var, Term.realize_var,
    Ordered.realize_one_val]

private theorem realize_maxGuard {w : ℕ} (a : Fin w) (v : Fin w → Fin B) :
    (maxGuard L a).Realize v ↔ v a = maxFin B := by
  rw [maxGuard, Formula.realize_equal, Term.realize_var, Fin.ext_iff, Fin.ext_iff,
    Ordered.realize_max_val]
  rfl

private theorem realize_inputGuard
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)}
    {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    {w : ℕ} (s : Option Bool) (a : Fin w) (v : Fin w → Fin B) :
    (inputGuard inputFormula s a).Realize v ↔ inputAt input (v a).val = s := by
  rw [inputGuard, Formula.realize_relabel]
  have hv : v ∘ (fun _ : Fin 1 => a) = ![v a] := by
    ext k
    fin_cases k
    rfl
  rw [hv]
  exact hinput s (v a)

/-! #### Soundness: `targetModel` is closed under all definite clauses -/

private theorem holds_readClausesFor_target (tm : MultiTapeTM m Bool State) (input : List Bool)
    (i : Fin m) (s : Option Bool) :
    ∀ C ∈ readClausesFor (State := State) L i s, C.Holds (targetModel B tm input) := by
  intro C hC
  simp only [readClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;>
  · intro v _ hb
    have h1 := (holds_tagAtom_target tm input _ 0 1 v).mp (hb _ (List.mem_cons_self ..))
    have h2 := (holds_tagAtom_target tm input _ 0 1 v).mp
      (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    first
    | exact (holds_readAtom_target tm input i s 0 v).mpr ⟨v 1, Or.inl ⟨h1, h2⟩⟩
    | exact (holds_readAtom_target tm input i s 0 v).mpr ⟨v 1, Or.inr ⟨h1, h2⟩⟩

private theorem holds_sitClauseFor_target (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (y : Situation m State) :
    (sitClauseFor L inputFormula y).Holds (targetModel B tm input) := by
  rcases y with ⟨qy, inSym, workSyms⟩
  intro v hg hb
  have hin : inputAt input (v 2).val = inSym := (realize_inputGuard hinput inSym 2 v).mp hg
  have hst := (holds_tagAtom_target tm input _ 0 1 v).mp (hb _ (List.mem_cons_self ..))
  have hpos := (holds_tagAtom_target tm input _ 0 2 v).mp
    (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hread : ∀ i : Fin m,
      ImmermanVardi.Tableau.read (targetRow tm input (v 0)) i (workSyms i) := fun i =>
    (holds_readAtom_target tm input i (workSyms i) 0 v).mp <| hb _ <|
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange i)))
  exact (holds_sitAtom_target tm input ⟨qy, inSym, workSyms⟩ 0 1 v).mpr
    ⟨hst, ⟨v 2, hpos, hin⟩, hread⟩

private theorem holds_elsewhereClausesFor_target (tm : MultiTapeTM m Bool State)
    (input : List Bool) (i : Fin m) (sign : Bool) :
    ∀ C ∈ elsewhereClausesFor (State := State) L i sign, C.Holds (targetModel B tm input) := by
  intro C hC
  simp only [elsewhereClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · intro v hg hb
    rw [Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var] at hg
    have hh := (holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..))
    exact (holds_elsewhereAtom_target tm input i sign 0 1 v).mpr ⟨v 2, Or.inl ⟨hh, hg⟩⟩
  · intro v hg hb
    rw [Formula.realize_not, Formula.realize_inf, realize_zeroGuard, realize_zeroGuard] at hg
    have hh := (holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..))
    exact (holds_elsewhereAtom_target tm input i sign 0 1 v).mpr ⟨v 2, Or.inr ⟨hh, hg⟩⟩

private theorem holds_inPrevClausesFor_target (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (d : SignType) :
    ∀ C ∈ inPrevClausesFor (m := m) (State := State) L inputFormula d,
      C.Holds (targetModel B tm input) := by
  intro C hC
  cases d <;> simp only [inPrevClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC
  case zero =>
    subst hC
    intro v _ hb
    have hh := (holds_tagAtom_target tm input .inPos 0 1 v).mp (hb _ (List.mem_cons_self ..))
    exact (holds_inPrevAtom_target tm input .zero 0 1 v).mpr hh
  case neg =>
    rcases hC with rfl | rfl
    · intro v hg hb
      rw [realize_zeroGuard] at hg
      have hh := (holds_tagAtom_target tm input .inPos 0 1 v).mp (hb _ (List.mem_cons_self ..))
      exact (holds_inPrevAtom_target tm input .neg 0 1 v).mpr (Or.inl ⟨hg, hh⟩)
    · intro v hg hb
      rw [realize_succGuard] at hg
      have hh := (holds_tagAtom_target tm input .inPos 0 2 v).mp (hb _ (List.mem_cons_self ..))
      exact (holds_inPrevAtom_target tm input .neg 0 1 v).mpr (Or.inr ⟨v 2, hg, hh⟩)
  case pos =>
    rcases hC with rfl | rfl
    · intro v hg hb
      rw [Formula.realize_inf, Formula.realize_not, realize_zeroGuard,
        realize_inputGuard hinput] at hg
      obtain ⟨hne, hnone⟩ := hg
      have hh := (holds_tagAtom_target tm input .inPos 0 1 v).mp (hb _ (List.mem_cons_self ..))
      exact (holds_inPrevAtom_target tm input .pos 0 1 v).mpr (Or.inl ⟨hne, hnone, hh⟩)
    · intro v hg hb
      rw [Formula.realize_inf, realize_succGuard, Formula.realize_sup, realize_zeroGuard,
        Formula.realize_not, realize_inputGuard hinput] at hg
      obtain ⟨hs, hor⟩ := hg
      have hh := (holds_tagAtom_target tm input .inPos 0 2 v).mp (hb _ (List.mem_cons_self ..))
      exact (holds_inPrevAtom_target tm input .pos 0 1 v).mpr (Or.inr ⟨v 2, hs, hh, hor⟩)

private theorem holds_headPrevClausesFor_target (tm : MultiTapeTM m Bool State)
    (input : List Bool) (i : Fin m) (sign : Bool) (d : SignType) :
    ∀ C ∈ headPrevClausesFor (State := State) L i sign d, C.Holds (targetModel B tm input) := by
  intro C hC
  unfold headPrevClausesFor at hC
  cases hdir : (if sign then d else -d) <;>
    simp only [hdir, List.mem_cons, List.not_mem_nil, or_false] at hC
  · subst hC
    intro v _ hb
    exact (holds_headPrevAtom_target tm input i sign d 0 1 v).mpr <| by
      rw [headPrev, hdir]
      exact (holds_tagAtom_target tm input _ 0 1 v).mp (hb _ (List.mem_cons_self ..))
  · subst hC
    intro v hg hb
    exact (holds_headPrevAtom_target tm input i sign d 0 1 v).mpr <| by
      rw [headPrev, hdir]
      exact ⟨v 2, (realize_succGuard 1 2 v).mp hg,
        (holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..))⟩
  · rcases hC with rfl | rfl
    · intro v hg hb
      rw [Formula.realize_inf, realize_zeroGuard, realize_oneGuard] at hg
      exact (holds_headPrevAtom_target tm input i sign d 0 1 v).mpr <| by
        rw [headPrev, hdir]
        exact Or.inl ⟨hg.1, v 2, hg.2,
          (holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..))⟩
    · intro v hg hb
      exact (holds_headPrevAtom_target tm input i sign d 0 1 v).mpr <| by
        rw [headPrev, hdir]
        exact Or.inr ⟨v 2, (realize_succGuard 2 1 v).mp hg,
          (holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..))⟩

private theorem holds_initClausesFor_target [DecidableEq State]
    (tm : MultiTapeTM m Bool State) (input : List Bool)
    (q : Tag m State) :
    ∀ C ∈ initClausesFor L tm q, C.Holds (targetModel B tm input) := by
  intro C hC
  have hinit_row (t a : Fin B) (ht : t.val = 0) (hi : initial tm q a) :
      targetRow tm input t q a := by
    simpa only [targetRow, ht, runFrom, Function.iterate_zero_apply] using
      (initial_iff tm input q a).mp hi
  have hpair (g : (Ordered.language L).Formula (Fin 2))
      (hg : ∀ v : Fin 2 → Fin B, g.Realize v → (v 0).val = 0 ∧ initial tm q (v 1))
      (h : C ∈ [⟨2, g, [], some (tagAtom q 0 1)⟩]) :
      C.Holds (targetModel B tm input) := by
    obtain rfl := List.mem_singleton.mp h
    intro v hgv _
    exact (holds_tagAtom_target tm input q 0 1 v).mpr
      (hinit_row (v 0) (v 1) (hg v hgv).1 (hg v hgv).2)
  have hzero (P : Prop) [Decidable P] (hP : ∀ a : Fin B, P → initial tm q a)
      (h : C ∈ if P then [⟨2, zeroGuard L 0, [], some (tagAtom q 0 1)⟩] else []) :
      C.Holds (targetModel B tm input) := by
    split_ifs at h with hp
    · exact hpair (zeroGuard L 0) (fun v hv => ⟨(realize_zeroGuard 0 v).mp hv, hP (v 1) hp⟩) h
    · cases h
  cases q with
  | state q' => exact hzero (q' = some tm.q₀) (fun _ h => h) hC
  | out o => exact hzero (o = .empty) (fun _ h => h) hC
  | inPos => exact hpair (zeroGuard L 0 ⊓ oneGuard L 1) (fun v hv => by
      rw [Formula.realize_inf, realize_zeroGuard, realize_oneGuard] at hv; exact hv) hC
  | head i sign => exact hpair (zeroGuard L 0 ⊓ zeroGuard L 1) (fun v hv => by
      rw [Formula.realize_inf, realize_zeroGuard, realize_zeroGuard] at hv; exact hv) hC
  | cell i sign s => exact hzero (s = none) (fun _ h => h) hC

variable [Fintype State] [DecidableEq State]

omit [L.Structure (Fin B)] [Fact (2 ≤ B)] in
private theorem definiteClause_isSome
    {tm : MultiTapeTM m Bool State}
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)}
    {C : TClause L m State} (hC : C ∈ definiteClauses L tm inputFormula) :
    C.head.isSome := by
  simp only [definiteClauses, List.mem_append, List.mem_flatMap, List.mem_map] at hC
  rcases hC with ((((((h | h) | h) | h) | h) | h) | h)
  · obtain ⟨⟨i, s⟩, _, hC⟩ := h
    simp only [readClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> rfl
  · obtain ⟨y, _, rfl⟩ := h
    cases y; rfl
  · obtain ⟨⟨i, sign⟩, _, hC⟩ := h
    simp only [elsewhereClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> rfl
  · obtain ⟨d, _, hC⟩ := h
    cases d <;> simp only [inPrevClausesFor, List.mem_cons, List.not_mem_nil, or_false] at hC <;>
      (rcases hC with rfl | rfl <;> rfl)
  · obtain ⟨⟨i, sign⟩, _, d, _, hC⟩ := h
    unfold headPrevClausesFor at hC
    cases hdir : (if sign then d else -d) <;>
      simp only [hdir, List.mem_cons, List.not_mem_nil, or_false] at hC <;>
      first | (subst hC; rfl) | (rcases hC with rfl | rfl <;> rfl)
  · obtain ⟨q, _, hC⟩ := h
    cases q <;> simp only [initClausesFor] at hC <;> (try split_ifs at hC) <;>
      first | (obtain rfl := List.mem_singleton.mp hC; rfl) | cases hC
  · obtain ⟨q, _, hC⟩ := h
    obtain ⟨body, _, rfl⟩ := List.mem_map.mp hC
    rfl

omit [Fact (2 ≤ B)] in
private theorem stepBodies_sound (tm : MultiTapeTM m Bool State) (input : List Bool)
    (q : Tag m State) (body : List (TAtom m State 3)) (hbody : body ∈ stepBodies tm q)
    (v : Fin 3 → Fin B) (hb : ∀ a ∈ body, a.Holds (targetModel B tm input) v) :
    rowStep tm input (targetRow tm input (v 0)) q (v 2) := by
  cases q with
  | state q' =>
    simp only [stepBodies, List.mem_append, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hbody
    rcases hbody with hhalt | ⟨y, ⟨_, hy⟩, rfl⟩
    · split_ifs at hhalt with hq
      · obtain rfl := List.mem_singleton.mp hhalt
        exact Or.inl
          ⟨(holds_tagAtom_target tm input _ 0 2 v).mp (hb _ (List.mem_cons_self ..)), hq⟩
      · cases hhalt
    · exact Or.inr
        ⟨y, hy, (holds_sitAtom_target tm input y 0 2 v).mp (hb _ (List.mem_cons_self ..))⟩
  | out o =>
    simp only [stepBodies, List.mem_cons, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hbody
    rcases hbody with rfl | ⟨⟨y, o'⟩, ⟨_, ho'⟩, rfl⟩ <;>
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom_target,
        holds_sitAtom_target] at hb
    exacts [Or.inl hb, Or.inr ⟨y, o', ho', hb⟩]
  | inPos =>
    simp only [stepBodies, List.mem_cons, List.mem_map] at hbody
    rcases hbody with rfl | ⟨y, _, rfl⟩ <;>
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom_target,
        holds_sitAtom_target, holds_inPrevAtom_target] at hb
    exacts [Or.inl hb, Or.inr ⟨y, hb⟩]
  | head i sign =>
    simp only [stepBodies, List.mem_cons, List.mem_map] at hbody
    rcases hbody with rfl | ⟨y, _, rfl⟩
    · simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom_target] at hb
      exact Or.inl hb
    · rcases hw : (tm.actionOf y).workTapes i with ⟨writeSym, dir⟩
      simp only [hw, List.forall_mem_cons, ↓List.forall_mem_singleton, holds_sitAtom_target,
        holds_headPrevAtom_target] at hb
      refine Or.inr ⟨y, hb.1, ?_⟩
      rw [hw]
      exact hb.2
  | cell i sign s =>
    simp only [stepBodies, List.mem_cons, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hbody
    rcases hbody with rfl | rfl | ⟨⟨y, s'⟩, ⟨_, hs'⟩, rfl⟩ <;>
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom_target,
        holds_sitAtom_target, holds_elsewhereAtom_target] at hb
    · exact Or.inl ⟨hb.1, Or.inl hb.2⟩
    · exact Or.inl ⟨hb.1, Or.inr hb.2⟩
    · rcases hw : (tm.actionOf y).workTapes i with ⟨writeSym, dir⟩
      simp only [hw] at hs'
      refine Or.inr ⟨y, s', ?_, hb⟩
      rw [hw]
      exact hs'

private theorem holds_stepClausesFor_target (tm : MultiTapeTM m Bool State)
    {input : List Bool} (hn : input.length + 1 < B) (q : Tag m State) :
    ∀ C ∈ stepClausesFor L tm q, C.Holds (targetModel B tm input) := by
  intro C hC
  obtain ⟨body, hbody, rfl⟩ := List.mem_map.mp hC
  intro v hg hb
  rw [realize_succGuard] at hg
  have hstep := stepBodies_sound tm input q body hbody v hb
  have hb_pos : ∀ i, |(tm.runFrom (tm.initCfg input) (v 0).val).workTapePos i| + 1 < B := by
    intro i
    have := tm.abs_workTapePos_runFrom_le input (v 0).val i
    have := (v 1).isLt
    omega
  have hnext := (rowStep_row tm hn hb_pos q (v 2)).mp hstep
  refine (holds_tagAtom_target tm input q 1 2 v).mpr ?_
  rw [targetRow, ← hg, runFrom_succ]
  exact hnext

private theorem closed_targetModel (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (hn : input.length + 1 < B) :
    (tableauSentence L tm inputFormula).Closed (targetModel B tm input) := by
  intro C hC hsome
  rcases List.mem_append.mp hC with hdef | hgoal
  · simp only [definiteClauses, List.mem_append, List.mem_flatMap, List.mem_map] at hdef
    rcases hdef with ((((((h | h) | h) | h) | h) | h) | h)
    · obtain ⟨⟨i, s⟩, _, hC⟩ := h
      exact holds_readClausesFor_target tm input i s C hC
    · obtain ⟨y, _, rfl⟩ := h
      exact holds_sitClauseFor_target tm hinput y
    · obtain ⟨⟨i, sign⟩, _, hC⟩ := h
      exact holds_elsewhereClausesFor_target tm input i sign C hC
    · obtain ⟨d, _, hC⟩ := h
      exact holds_inPrevClausesFor_target tm hinput d C hC
    · obtain ⟨⟨i, sign⟩, _, d, _, hC⟩ := h
      exact holds_headPrevClausesFor_target tm input i sign d C hC
    · obtain ⟨q, _, hC⟩ := h
      exact holds_initClausesFor_target tm input q C hC
    · obtain ⟨q, _, hC⟩ := h
      exact holds_stepClausesFor_target tm hn q C hC
  · rw [goalClause_head_none hgoal] at hsome
    cases hsome

/-! #### Completeness: `targetRow` holds in `leastModel` -/

private noncomputable abbrev leastRow (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)) (t : Fin B) :
    Row m State B :=
  fun q a => ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.tag q)

private theorem holds_definiteClause_leastModel (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {C : TClause L m State} (hC : C ∈ definiteClauses L tm inputFormula) :
    C.Holds ((tableauSentence L tm inputFormula).leastModel (Fin B)) :=
  (tableauSentence L tm inputFormula).closed_leastModel C
    (List.mem_append_left _ hC) (definiteClause_isSome hC)

private theorem leastModel_read_of_mem (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {i : Fin m} {s : Option Bool} {sign : Bool}
    (hC : (⟨2, ⊤, [tagAtom (.head i sign) 0 1, tagAtom (.cell i sign s) 0 1],
        some (readAtom i s 0)⟩ : TClause L m State) ∈ readClausesFor (State := State) L i s)
    (t a : Fin B)
    (hh : leastRow tm inputFormula t (.head i sign) a)
    (hc : leastRow tm inputFormula t (.cell i sign s) a) :
    ![t, t] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.read i s) := by
  let C : TClause L m State :=
    ⟨2, ⊤, [tagAtom (.head i sign) 0 1, tagAtom (.cell i sign s) 0 1], some (readAtom i s 0)⟩
  have hdef : C ∈ definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; left; left; left; left; left
    exact List.mem_flatMap.mpr ⟨(i, s), mem_univList _, hC⟩
  exact (holds_readAtom i s 0 _ ![t, a]).mp <|
    holds_definiteClause_leastModel tm inputFormula hdef ![t, a]
      (Formula.realize_top.mpr trivial) <|
      List.forall_mem_cons.mpr ⟨(holds_tagAtom (.head i sign) 0 1 _ ![t, a]).mpr hh,
        List.forall_mem_singleton.mpr ((holds_tagAtom (.cell i sign s) 0 1 _ ![t, a]).mpr hc)⟩

private theorem leastModel_read (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (t : Fin B) (i : Fin m) (s : Option Bool)
    (hr : ImmermanVardi.Tableau.read (leastRow tm inputFormula t) i s) :
    ![t, t] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.read i s) := by
  rcases hr with ⟨a, ⟨hh, hc⟩ | ⟨hh, hc⟩⟩
  · exact leastModel_read_of_mem tm inputFormula (List.mem_cons_self ..) t a hh hc
  · exact leastModel_read_of_mem tm inputFormula
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) t a hh hc

private theorem leastModel_sit (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (t a : Fin B) (y : Situation m State)
    (hs : situation input (leastRow tm inputFormula t) y a) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.sit y) := by
  rcases y with ⟨qy, inSym, workSyms⟩
  rcases hs with ⟨hst, ⟨j, hpos, hin⟩, hread⟩
  have hC : sitClauseFor (State := State) L inputFormula ⟨qy, inSym, workSyms⟩ ∈
      definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; left; left; left; left; right
    exact List.mem_map_of_mem (mem_univList _)
  have hg := (realize_inputGuard hinput inSym 2 ![t, a, j]).mpr hin
  have hres := holds_definiteClause_leastModel tm inputFormula hC ![t, a, j] hg fun b hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (holds_tagAtom _ 0 1 _ ![t, a, j]).mpr hst
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact (holds_tagAtom .inPos 0 2 _ ![t, a, j]).mpr hpos
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
        exact (holds_readAtom i (workSyms i) 0 _ ![t, a, j]).mpr
          (leastModel_read tm inputFormula t i (workSyms i) (hread i))
  exact (holds_sitAtom ⟨qy, inSym, workSyms⟩ 0 1 _ ![t, a, j]).mp hres

private theorem leastModel_elsewhere_of_mem (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {i : Fin m} {sign : Bool} {g : (Ordered.language L).Formula (Fin 3)} {q : Tag m State}
    (hC : (⟨3, g, [tagAtom q 0 2], some (elsewhereAtom i sign 0 1)⟩ : TClause L m State) ∈
      elsewhereClausesFor (State := State) L i sign)
    (t a b : Fin B) (hg : g.Realize ![t, a, b])
    (htag : leastRow tm inputFormula t q b) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.elsewhere i sign) := by
  let C : TClause L m State := ⟨3, g, [tagAtom q 0 2], some (elsewhereAtom i sign 0 1)⟩
  have hdef : C ∈ definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; left; left; left; right
    exact List.mem_flatMap.mpr ⟨(i, sign), mem_univList _, hC⟩
  exact (holds_elsewhereAtom i sign 0 1 _ ![t, a, b]).mp <|
    holds_definiteClause_leastModel tm inputFormula hdef ![t, a, b] hg <|
      List.forall_mem_singleton.mpr ((holds_tagAtom q 0 2 _ ![t, a, b]).mpr htag)

private theorem leastModel_elsewhere (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (t a : Fin B) (i : Fin m) (sign : Bool)
    (he : elsewhere (leastRow tm inputFormula t) i sign a) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B)
      (.elsewhere i sign) := by
  rcases he with ⟨b, ⟨hh, hne⟩ | ⟨hh, hnz⟩⟩
  · exact leastModel_elsewhere_of_mem tm inputFormula (List.mem_cons_self ..) t a b (by
      rw [Formula.realize_not, Formula.realize_equal, Term.realize_var, Term.realize_var]
      exact hne) hh
  · exact leastModel_elsewhere_of_mem tm inputFormula
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) t a b (by
      rw [Formula.realize_not, Formula.realize_inf, realize_zeroGuard, realize_zeroGuard]
      exact hnz) hh

private theorem leastModel_inPrev_of_mem (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {d : SignType} {n : ℕ} {g : (Ordered.language L).Formula (Fin (n + 2))} {idx : Fin (n + 2)}
    (hC : (⟨n + 2, g, [tagAtom .inPos 0 idx], some (inPrevAtom d 0 1)⟩ : TClause L m State) ∈
      inPrevClausesFor (m := m) (State := State) L inputFormula d)
    (v : Fin (n + 2) → Fin B) (hg : g.Realize v)
    (htag : leastRow tm inputFormula (v 0) .inPos (v idx)) :
    ![v 0, v 1] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.inPrev d) := by
  let C : TClause L m State := ⟨n + 2, g, [tagAtom .inPos 0 idx], some (inPrevAtom d 0 1)⟩
  have hdef : C ∈ definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; left; left; right
    exact List.mem_flatMap.mpr ⟨d, mem_signs d, hC⟩
  exact (holds_inPrevAtom d 0 1 _ v).mp <|
    holds_definiteClause_leastModel tm inputFormula hdef v hg <|
      List.forall_mem_singleton.mpr ((holds_tagAtom .inPos 0 idx _ v).mpr htag)

private theorem leastModel_inPrev (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (t a : Fin B) (d : SignType)
    (hp : inputPrev input (leastRow tm inputFormula t) d a) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.inPrev d) := by
  cases d with
  | zero =>
    dsimp only [inputPrev] at hp
    exact leastModel_inPrev_of_mem tm inputFormula (n := 0) (idx := 1)
      (List.mem_cons_self ..) ![t, a] (Formula.realize_top.mpr trivial) hp
  | neg =>
    rcases hp with ⟨ha, hh⟩ | ⟨b, hb, hh⟩
    · exact leastModel_inPrev_of_mem tm inputFormula (n := 0) (idx := 1)
        (List.mem_cons_self ..) ![t, a] ((realize_zeroGuard 1 ![t, a]).mpr ha) hh
    · exact leastModel_inPrev_of_mem tm inputFormula (n := 1) (idx := 2)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ![t, a, b]
        ((realize_succGuard 1 2 ![t, a, b]).mpr hb) hh
  | pos =>
    rcases hp with ⟨hne, hnone, hh⟩ | ⟨b, hb, hh, hor⟩
    · refine leastModel_inPrev_of_mem tm inputFormula (n := 0) (idx := 1)
        (List.mem_cons_self ..) ![t, a] ?_ hh
      rw [Formula.realize_inf, Formula.realize_not, realize_zeroGuard, realize_inputGuard hinput]
      exact ⟨hne, hnone⟩
    · refine leastModel_inPrev_of_mem tm inputFormula (n := 1) (idx := 2)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ![t, a, b] ?_ hh
      rw [Formula.realize_inf, realize_succGuard, Formula.realize_sup, realize_zeroGuard,
        Formula.realize_not, realize_inputGuard hinput]
      exact ⟨hb, hor⟩

private theorem leastModel_headPrev_of_mem (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {i : Fin m} {sign : Bool} {d : SignType}
    {n : ℕ} {g : (Ordered.language L).Formula (Fin (n + 2))} {q : Tag m State}
    {idx : Fin (n + 2)}
    (hC : (⟨n + 2, g, [tagAtom q 0 idx], some (headPrevAtom i sign d 0 1)⟩ : TClause L m State) ∈
      headPrevClausesFor (State := State) L i sign d)
    (v : Fin (n + 2) → Fin B) (hg : g.Realize v)
    (htag : leastRow tm inputFormula (v 0) q (v idx)) :
    ![v 0, v 1] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.headPrev i sign d) := by
  let C : TClause L m State := ⟨n + 2, g, [tagAtom q 0 idx], some (headPrevAtom i sign d 0 1)⟩
  have hdef : C ∈ definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; left; right
    exact List.mem_flatMap.mpr ⟨(i, sign), mem_univList _,
      List.mem_flatMap.mpr ⟨d, mem_signs d, hC⟩⟩
  exact (holds_headPrevAtom i sign d 0 1 _ v).mp <|
    holds_definiteClause_leastModel tm inputFormula hdef v hg <|
      List.forall_mem_singleton.mpr ((holds_tagAtom q 0 idx _ v).mpr htag)

private theorem leastModel_headPrev (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (t a : Fin B) (i : Fin m) (sign : Bool) (d : SignType)
    (hp : headPrev (leastRow tm inputFormula t) i sign d a) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B)
      (.headPrev i sign d) := by
  unfold headPrev at hp
  cases hdir : (if sign then d else -d) <;> simp only [hdir] at hp
  · refine leastModel_headPrev_of_mem tm inputFormula (n := 0) (idx := 1) ?_ ![t, a]
      (Formula.realize_top.mpr trivial) hp
    simp only [headPrevClausesFor, hdir, List.mem_cons, List.not_mem_nil, or_false]
  · rcases hp with ⟨b, hb, hh⟩
    refine leastModel_headPrev_of_mem tm inputFormula (n := 1) (idx := 2) ?_ ![t, a, b]
      ((realize_succGuard 1 2 ![t, a, b]).mpr hb) hh
    simp only [headPrevClausesFor, hdir, List.mem_cons, List.not_mem_nil, or_false]
  · rcases hp with ⟨ha, b, hb, hh⟩ | ⟨b, hb, hh⟩
    · refine leastModel_headPrev_of_mem tm inputFormula (n := 1) (idx := 2) ?_ ![t, a, b]
        (Formula.realize_inf.mpr
          ⟨(realize_zeroGuard 1 ![t, a, b]).mpr ha, (realize_oneGuard 2 ![t, a, b]).mpr hb⟩)
        hh
      simp only [headPrevClausesFor, hdir, List.mem_cons, true_or]
    · refine leastModel_headPrev_of_mem tm inputFormula (n := 1) (idx := 2) ?_ ![t, a, b]
        ((realize_succGuard 2 1 ![t, a, b]).mpr hb) hh
      simp only [headPrevClausesFor, hdir, List.mem_cons, List.not_mem_nil, or_false, or_true]

private theorem leastModel_init_of_mem (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    {q : Tag m State} {g : (Ordered.language L).Formula (Fin 2)}
    (hC : (⟨2, g, [], some (tagAtom q 0 1)⟩ : TClause L m State) ∈ initClausesFor L tm q)
    (t a : Fin B) (hg : g.Realize ![t, a]) :
    leastRow tm inputFormula t q a := by
  let C : TClause L m State := ⟨2, g, [], some (tagAtom q 0 1)⟩
  have hdef : C ∈ definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    left; right
    exact List.mem_flatMap.mpr ⟨q, mem_univList q, hC⟩
  exact (holds_tagAtom q 0 1 _ ![t, a]).mp <|
    holds_definiteClause_leastModel tm inputFormula hdef ![t, a] hg fun _ hx => nomatch hx

private theorem leastModel_init (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (t a : Fin B) (ht : t.val = 0) (q : Tag m State) (hi : initial tm q a) :
    leastRow tm inputFormula t q a := by
  cases q with
  | state q' =>
    have hq : q' = some tm.q₀ := hi
    subst hq
    refine leastModel_init_of_mem tm inputFormula ?_ t a ((realize_zeroGuard 0 ![t, a]).mpr ht)
    simp only [initClausesFor, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  | out o =>
    have ho : o = .empty := hi
    subst ho
    refine leastModel_init_of_mem tm inputFormula ?_ t a ((realize_zeroGuard 0 ![t, a]).mpr ht)
    simp only [initClausesFor, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
  | inPos =>
    refine leastModel_init_of_mem tm inputFormula (List.mem_cons_self ..) t a ?_
    rw [Formula.realize_inf, realize_zeroGuard, realize_oneGuard]
    exact ⟨ht, hi⟩
  | head i sign =>
    refine leastModel_init_of_mem tm inputFormula (List.mem_cons_self ..) t a ?_
    rw [Formula.realize_inf, realize_zeroGuard, realize_zeroGuard]
    exact ⟨ht, hi⟩
  | cell i sign s =>
    have hs : s = none := hi
    subst hs
    refine leastModel_init_of_mem tm inputFormula ?_ t a ((realize_zeroGuard 0 ![t, a]).mpr ht)
    simp only [initClausesFor, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]

private theorem stepBodies_complete (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (t t' a : Fin B) (q : Tag m State)
    (hs : rowStep tm input (leastRow tm inputFormula t) q a) :
    ∃ body ∈ stepBodies tm q,
      ∀ x ∈ body, x.Holds ((tableauSentence L tm inputFormula).leastModel (Fin B))
        ![t, t', a] := by
  cases q with
  | state q' =>
    rcases hs with ⟨hhalt, hq⟩ | ⟨y, hy, hsit⟩
    · refine ⟨[tagAtom (.state none) 0 2], ?_,
        List.forall_mem_singleton.mpr ((holds_tagAtom (.state none) 0 2 _ ![t, t', a]).mpr hhalt)⟩
      simp only [stepBodies, hq, ↓reduceIte, List.mem_append, List.mem_cons, true_or]
    · refine ⟨[sitAtom y 0 2], ?_, List.forall_mem_singleton.mpr
        ((holds_sitAtom y 0 2 _ ![t, t', a]).mpr (leastModel_sit tm hinput t a y hsit))⟩
      simp only [stepBodies, List.mem_append]
      right
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨mem_univList y, decide_eq_true hy⟩)
  | out o =>
    rcases hs with ⟨hhalt, hout⟩ | ⟨y, o', ho', hsit, hout⟩
    · refine ⟨_, List.mem_cons_self .., ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom]
      exact ⟨hhalt, hout⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨(y, o'), List.mem_filter.mpr ⟨mem_univList (y, o'), decide_eq_true ho'⟩, rfl⟩), ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom, holds_sitAtom]
      exact ⟨leastModel_sit tm hinput t a y hsit, hout⟩
  | inPos =>
    rcases hs with ⟨hhalt, hpos⟩ | ⟨y, hsit, hprev⟩
    · refine ⟨_, List.mem_cons_self .., ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom]
      exact ⟨hhalt, hpos⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_univList y)), ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_sitAtom,
        holds_inPrevAtom]
      exact ⟨leastModel_sit tm hinput t a y hsit, leastModel_inPrev tm hinput t a _ hprev⟩
  | head i sign =>
    rcases hs with ⟨hhalt, hhead⟩ | ⟨y, hsit, hprev⟩
    · refine ⟨_, List.mem_cons_self .., ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom]
      exact ⟨hhalt, hhead⟩
    · rcases hw : (tm.actionOf y).workTapes i with ⟨writeSym, dir⟩
      simp only [hw] at hprev
      refine ⟨[sitAtom y 0 2, headPrevAtom i sign dir 0 2],
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨y, mem_univList y, by simp only [hw]⟩), ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_sitAtom,
        holds_headPrevAtom]
      exact ⟨leastModel_sit tm hinput t a y hsit,
        leastModel_headPrev tm inputFormula t a i sign dir hprev⟩
  | cell i sign s =>
    rcases hs with ⟨hcell, hhalt | helse⟩ | ⟨y, s', hs', hsit, hhead, hcell⟩
    · refine ⟨_, List.mem_cons_self .., ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom]
      exact ⟨hcell, hhalt⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom,
        holds_elsewhereAtom]
      exact ⟨hcell, leastModel_elsewhere tm inputFormula t a i sign helse⟩
    · rcases hw : (tm.actionOf y).workTapes i with ⟨writeSym, dir⟩
      simp only [hw] at hs'
      refine ⟨[sitAtom y 0 2, tagAtom (.head i sign) 0 2, tagAtom (.cell i sign s') 0 2], ?_, ?_⟩
      · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨(y, s'), List.mem_filter.mpr ⟨mem_univList (y, s'), ?_⟩, rfl⟩))
        simp only [hw, decide_eq_true_eq]
        exact hs'
      simp only [List.forall_mem_cons, ↓List.forall_mem_singleton, holds_tagAtom, holds_sitAtom]
      exact ⟨leastModel_sit tm hinput t a y hsit, hhead, hcell⟩

private theorem leastModel_step (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (t t' a : Fin B) (htt' : t.val + 1 = t'.val) (q : Tag m State)
    (hs : rowStep tm input (leastRow tm inputFormula t) q a) :
    leastRow tm inputFormula t' q a := by
  obtain ⟨body, hbody, hholds⟩ := stepBodies_complete tm hinput t t' a q hs
  have hC : (⟨3, succGuard L 0 1, body, some (tagAtom q 1 2)⟩ : TClause L m State) ∈
      definiteClauses L tm inputFormula := by
    simp only [definiteClauses, List.mem_append]
    right
    exact List.mem_flatMap.mpr ⟨q, mem_univList q, List.mem_map_of_mem hbody⟩
  exact (holds_tagAtom q 1 2 _ ![t, t', a]).mp <|
    holds_definiteClause_leastModel tm inputFormula hC ![t, t', a]
      ((realize_succGuard 0 1 ![t, t', a]).mpr htt') hholds

private theorem targetRow_le_leastRow (tm : MultiTapeTM m Bool State)
    {inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1)} {input : List Bool}
    (hinput : ∀ s (x : Fin B), (inputFormula s).Realize ![x] ↔ inputAt input x.val = s)
    (hn : input.length + 1 < B) :
    ∀ (n : ℕ) (t : Fin B), t.val = n → ∀ q a,
      targetRow tm input t q a → leastRow tm inputFormula t q a := by
  intro n
  induction n with
  | zero =>
    intro t ht q a hr
    have hi : initial tm q a := (initial_iff tm input q a).mpr (by
      simpa only [targetRow, ht, runFrom, Function.iterate_zero_apply] using hr)
    exact leastModel_init tm inputFormula t a ht q hi
  | succ n ih =>
    intro t' ht' q a hr
    let t : Fin B := ⟨n, by have := t'.isLt; omega⟩
    have htt' : t.val + 1 = t'.val := ht'.symm
    have hb_pos : ∀ i, |(tm.runFrom (tm.initCfg input) n).workTapePos i| + 1 < B := by
      intro i
      have := tm.abs_workTapePos_runFrom_le input n i
      have := t'.isLt
      omega
    have hstep_row : rowStep tm input (targetRow tm input t) q a :=
      (rowStep_row tm hn hb_pos q a).mpr (by simpa only [targetRow, ht', runFrom_succ] using hr)
    have hstep_least : rowStep tm input (leastRow tm inputFormula t) q a :=
      rowStep_mono tm input (fun q' a' h => ih t rfl q' a' h) q a hstep_row
    exact leastModel_step tm hinput t t' a htt' q hstep_least

private theorem mem_leastModel_tag_acceptanceHornSentence
    (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (input : List Bool)
    (hinput : ∀ s (a : Fin B), (inputFormula s).Realize ![a] ↔ inputAt input a.val = s)
    (hn : input.length + 1 < B)
    (q : Tag m State) (t a : Fin B) :
    ![t, a] ∈ (tableauSentence L tm inputFormula).leastModel (Fin B) (.tag q) ↔
      row (tm.runFrom (tm.initCfg input) t.val) q a := by
  constructor
  · intro hmem
    exact (tableauSentence L tm inputFormula).leastModel_le
      (closed_targetModel tm hinput hn) (.tag q) hmem
  · intro hrow
    exact targetRow_le_leastRow tm hinput hn t.val t rfl q a hrow

/-- **Horn tableau acceptance.** The uniform SO∃-Horn sentence `acceptanceHornSentence` holds on
`Fin B` (`2 ≤ B`, `input.length + 1 < B`) iff `tm` halts with output `[true]` by step `B - 1`. -/
theorem realize_acceptanceHornSentence
    (tm : MultiTapeTM m Bool State)
    (inputFormula : Option Bool → (Ordered.language L).Formula (Fin 1))
    (input : List Bool)
    (hinput : ∀ s (a : Fin B), (inputFormula s).Realize ![a] ↔ inputAt input a.val = s)
    (hn : input.length + 1 < B) :
    (acceptanceHornSentence L tm inputFormula).Realize (Fin B) ↔
      (tm.runFrom (tm.initCfg input) (B - 1)).Halted ∧
        (tm.runFrom (tm.initCfg input) (B - 1)).output = [true] := by
  unfold acceptanceHornSentence
  let Φ := tableauSentence L tm inputFormula
  let LM := Φ.leastModel (Fin B)
  let cfgMax := tm.runFrom (tm.initCfg input) (B - 1)
  rw [ESO.Horn.Sentence.realize_iff_leastModel]
  have hcons : Φ.Consistent LM ↔ ∀ C ∈ goalClauses (m := m) (State := State) L, C.Holds LM :=
    ⟨fun h C hC => h C (List.mem_append_right _ hC) (goalClause_head_none hC),
      fun h C hC hnone => (List.mem_append.mp hC).elim
        (fun hdef => absurd (definiteClause_isSome hdef) (by simp [hnone])) (h C)⟩
  -- a goal clause holds iff its tag fails at the last step
  have hgoal (q : Tag m State) :
      (⟨1, maxGuard L 0, [tagAtom q 0 0], none⟩ : TClause L m State).Holds LM ↔
        ¬ row cfgMax q (maxFin B) := by
    have hmem := mem_leastModel_tag_acceptanceHornSentence tm inputFormula input hinput hn q
      (maxFin B) (maxFin B)
    refine ⟨fun h hrow => h ![maxFin B] ((realize_maxGuard 0 _).mpr rfl)
      (List.forall_mem_singleton.mpr ((holds_tagAtom q 0 0 _ _).mpr (hmem.mpr hrow))),
      fun h v hg hb => h ?_⟩
    have hm := (holds_tagAtom _ _ _ _ _).mp (hb _ (List.mem_cons_self ..))
    rw [(realize_maxGuard 0 v).mp hg] at hm
    exact hmem.mp hm
  rw [hcons]
  simp only [goalClauses, List.forall_mem_append, List.forall_mem_map, hgoal]
  refine and_congr ⟨fun h => ?_, fun h s _ hrow => ?_⟩ ?_
  · rw [Cfg.Halted]
    cases hst : cfgMax.state with
    | none => rfl
    | some s => exact absurd hst (h s (mem_univList s))
  · rw [Cfg.Halted] at h
    exact Option.some_ne_none s ((hrow : cfgMax.state = some s).symm.trans h)
  · rw [← OutView.ofList_eq_one_iff]
    exact ⟨fun h => Classical.byContradiction fun hne =>
        h _ ((mem_rejectViews_iff _).mpr hne) rfl,
      fun heq o ho hrow => (mem_rejectViews_iff o).mp ho
        ((hrow : OutView.ofList cfgMax.output = o).symm.trans heq)⟩

end Semantics

end Cslib.Complexity.Gradel.Tableau
