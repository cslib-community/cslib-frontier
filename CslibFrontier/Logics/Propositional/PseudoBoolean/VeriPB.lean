/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean

/-!
# A VeriPB kernel-proof checker: cutting planes, RUP and proof by contradiction

This file checks the fragment of the kernel proof format of VeriPB version 3.0
[Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023] made of the rules

* `pol`: a cutting-planes derivation in reverse Polish notation, over constraint numbers, literal
  axioms, addition, multiplication, division, saturation and weakening
  (`Cslib.Logic.PL.VeriPB.PolOp`);
* `rup`: a constraint implied by reverse unit propagation, with or without hints
  (`Cslib.Logic.PL.VeriPB.Hint`);
* `pbc`: proof by contradiction, a subproof from the negated constraint that ends at a
  contradiction;
* `del`: deletion;

with the conclusion `UNSAT` naming a contradiction (`Cslib.Logic.PL.VeriPB.Proof`). The steps are
abstract syntax, not text: a step `pol 3 5 + 2 d;` is `.pol [.id 3, .id 5, .add, .div 2]`, the
number operand of `*` and `d` written into the operation. The constraints of the formula are
numbered `1, 2, …`, and every step, including the negated constraint of a `pbc` and the steps of
its subproof, takes the next number. After a `pbc` the constraints of its subproof are dropped
and the proved constraint takes the number after them.

**Unit propagation** on pseudo-Boolean constraints [Gocht and Nordström][GochtNordstrom2021]
works on a trail of literals taken to be true. The *slack* of `∑ aᵢ ℓᵢ ≥ d` is the sum of the
coefficients of the terms whose literals the trail does not falsify, minus `d`. A negative slack
is a conflict; otherwise every term not yet decided whose coefficient exceeds the slack must be
true (`Cslib.Logic.PL.VeriPB.propagate`). A `rup` step for `C` with hints propagates the hinted
constraints in order, `~` naming the negation of `C`, and succeeds at the first conflict; without
hints it propagates all constraints and the negation of `C` until a conflict or until nothing
changes.

**Soundness** (`Cslib.Logic.PL.VeriPB.not_satisfiable_of_check`): every constraint the checker
derives holds under every assignment satisfying the formula, so a checked proof of `UNSAT` shows
that the formula has no solution. For a CNF formula given as the constraints
`Cslib.Logic.PL.Clause.toPB` of its clauses, this is
`Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_check`.

The checker is written with structural recursion on lists, so `decide` can run it on small
proofs.

## Main definitions

* `Cslib.Logic.PL.VeriPB.propagate`: unit propagation of one constraint.
* `Cslib.Logic.PL.VeriPB.Step`, `Cslib.Logic.PL.VeriPB.Proof`: kernel proofs.
* `Cslib.Logic.PL.VeriPB.check`: the checker.

## Main results

* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_check`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_check`: soundness for `UNSAT`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
* [S. Gocht, J. Nordström, *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean
  Proofs*][GochtNordstrom2021]
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace VeriPB

open PBConstr

/-! ### Unit propagation -/

/-- The trail falsifies a term when the negation of its literal is on the trail. -/
def falsified (ρ : List (Literal ℕ)) (t : ℕ × Literal ℕ) : Bool :=
  ρ.contains (Std.Sat.Literal.negate t.2)

/-- The coefficients of the terms the trail does not falsify, minus the degree. -/
def slack (ρ : List (Literal ℕ)) (c : PBConstr) : ℤ :=
  (coeffSum (c.terms.filter fun t => !falsified ρ t) : ℤ) - c.degree

/-- **Unit propagation** of `c` on the trail `ρ`: `none` on a conflict, and otherwise the trail
extended by the literals `c` forces. -/
def propagate (ρ : List (Literal ℕ)) (c : PBConstr) : Option (List (Literal ℕ)) :=
  if slack ρ c < 0 then none
  else some ((c.terms.filter fun t =>
    !falsified ρ t && !ρ.contains t.2 && decide (slack ρ c < t.1)).map (·.2) ++ ρ)

/-- `σ` makes every literal of the trail true. -/
def Consistent (σ : ℕ → Bool) (ρ : List (Literal ℕ)) : Prop := ∀ l ∈ ρ, Literal.eval σ l = true

theorem coeffSum_filter_add (ts : List (ℕ × Literal ℕ)) (p q : ℕ × Literal ℕ → Bool) :
    coeffSum (ts.filter p) =
      coeffSum (ts.filter fun t => p t && q t) + coeffSum (ts.filter fun t => p t && !q t) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.filter_cons]
    cases p t <;> cases q t <;> simp [ih] <;> omega

theorem le_coeffSum_of_mem {ts : List (ℕ × Literal ℕ)} {t : ℕ × Literal ℕ} (h : t ∈ ts) :
    t.1 ≤ coeffSum ts := by
  induction ts with
  | nil => simp at h
  | cons u ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp only [coeffSum_cons]; have := ih h; omega

theorem lhs_eq_coeffSum_filter (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    lhs σ ts = coeffSum (ts.filter fun t => Literal.eval σ t.2) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons, List.filter_cons, termVal]
    cases Literal.eval σ t.2 <;> simp [ih]

theorem filter_congr' {ts : List (ℕ × Literal ℕ)} {p q : ℕ × Literal ℕ → Bool}
    (h : ∀ t ∈ ts, p t = q t) : ts.filter p = ts.filter q := List.filter_congr h

/-- **Unit propagation is sound**: under an assignment consistent with the trail and satisfying
`c`, propagation finds no conflict and the extended trail stays consistent. -/
theorem propagate_sound {σ : ℕ → Bool} {ρ : List (Literal ℕ)} {c : PBConstr}
    (hρ : Consistent σ ρ) (hc : c.Holds σ) :
    ∃ ρ', propagate ρ c = some ρ' ∧ Consistent σ ρ' := by
  -- A term whose literal is true is not falsified.
  have hnf : ∀ t ∈ c.terms, Literal.eval σ t.2 = true → falsified ρ t = false := by
    intro t _ ht
    unfold falsified
    by_contra hf
    simp only [Bool.not_eq_false, List.contains_iff_mem] at hf
    have := hρ _ hf
    rw [Literal.eval_negate] at this
    simp [ht] at this
  have hsplit := coeffSum_filter_add c.terms (fun t => !falsified ρ t)
    (fun t => Literal.eval σ t.2)
  have htrue : (c.terms.filter fun t => !falsified ρ t && Literal.eval σ t.2) =
      c.terms.filter fun t => Literal.eval σ t.2 := by
    apply List.filter_congr
    intro t ht
    cases h : Literal.eval σ t.2
    · simp
    · simp [hnf t ht h]
  rw [htrue, ← lhs_eq_coeffSum_filter] at hsplit
  unfold Holds at hc
  have hs : 0 ≤ slack ρ c := by unfold slack; omega
  refine ⟨_, by
    unfold propagate
    split
    · exact absurd ‹_› (not_lt.mpr hs)
    · rfl, fun l hl => ?_⟩
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
    have htm := (List.mem_filter.mp ht).1
    have hp := (List.mem_filter.mp ht).2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
    obtain ⟨⟨hf, -⟩, hlt⟩ := hp
    by_contra hev
    have hmem : t ∈ c.terms.filter fun t => !falsified ρ t && !Literal.eval σ t.2 := by
      simp only [Bool.not_eq_true] at hev
      simp [List.mem_filter, htm, hf, hev]
    have := le_coeffSum_of_mem hmem
    unfold slack at hlt
    omega
  · exact hρ l hl

/-- A conflict: no assignment consistent with the trail satisfies `c`. -/
theorem not_holds_of_propagate_eq_none {σ : ℕ → Bool} {ρ : List (Literal ℕ)} {c : PBConstr}
    (hρ : Consistent σ ρ) (h : propagate ρ c = none) : ¬ c.Holds σ := fun hc => by
  obtain ⟨ρ', h', -⟩ := propagate_sound hρ hc
  simp [h] at h'

/-! ### The database -/

/-- The constraint numbered `n`. -/
def lookup (db : List (ℕ × PBConstr)) (n : ℕ) : Option PBConstr :=
  (db.find? (·.1 == n)).map (·.2)

/-- `σ` satisfies every constraint of the database. -/
def AllHold (σ : ℕ → Bool) (db : List (ℕ × PBConstr)) : Prop := ∀ e ∈ db, e.2.Holds σ

theorem AllHold.lookup {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} (h : AllHold σ db) {n : ℕ}
    {c : PBConstr} (hc : VeriPB.lookup db n = some c) : c.Holds σ := by
  unfold VeriPB.lookup at hc
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact h e (List.mem_of_find?_eq_some he)

/-! ### Reverse unit propagation -/

/-- A RUP hint: the negated constraint `~`, or a constraint number. -/
inductive Hint where
  /-- The negation of the constraint being proved. -/
  | neg
  /-- The constraint with this number. -/
  | id (n : ℕ)
  deriving DecidableEq, Repr

/-- The constraint a hint names. -/
def resolve (db : List (ℕ × PBConstr)) (neg : PBConstr) : Hint → Option PBConstr
  | .neg => some neg
  | .id n => lookup db n

/-- Propagate the hinted constraints in order; `true` at the first conflict. -/
def rupHints (db : List (ℕ × PBConstr)) (neg : PBConstr) :
    List Hint → List (Literal ℕ) → Bool
  | [], _ => false
  | h :: hs, ρ =>
    match resolve db neg h with
    | none => false
    | some c =>
      match propagate ρ c with
      | none => true
      | some ρ' => rupHints db neg hs ρ'

/-- One round of propagation over a list of constraints: `none` on a conflict. -/
def propRound : List PBConstr → List (Literal ℕ) → Option (List (Literal ℕ))
  | [], ρ => some ρ
  | c :: cs, ρ => (propagate ρ c).bind (propRound cs)

/-- Propagate all constraints, round after round, until a conflict (`true`) or a round that adds
nothing (`false`); `fuel` bounds the number of rounds. -/
def rupFix (cs : List PBConstr) : ℕ → List (Literal ℕ) → Bool
  | 0, _ => false
  | fuel + 1, ρ =>
    match propRound cs ρ with
    | none => true
    | some ρ' => if ρ'.length = ρ.length then false else rupFix cs fuel ρ'

/-- **RUP**: `c` follows from the database by unit propagation from its negation, along the
hints when given. -/
def rup (db : List (ℕ × PBConstr)) (c : PBConstr) : Option (List Hint) → Bool
  | some hs => rupHints db c.negate hs []
  | none =>
    let cs := c.negate :: db.map (·.2)
    rupFix cs ((cs.map (·.terms.length)).sum + 1) []

theorem rupHints_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} {neg : PBConstr}
    (hdb : AllHold σ db) (hneg : neg.Holds σ) :
    ∀ (hs : List Hint) (ρ : List (Literal ℕ)), Consistent σ ρ → rupHints db neg hs ρ = false
  | [], _, _ => rfl
  | h :: hs, ρ, hρ => by
    have hc : ∀ c, resolve db neg h = some c → c.Holds σ := by
      intro c hc
      cases h with
      | neg => cases hc; exact hneg
      | id n => exact hdb.lookup (by simpa [resolve] using hc)
    unfold rupHints
    split
    · rfl
    · rename_i c hcm
      obtain ⟨ρ', hp, hρ'⟩ := propagate_sound hρ (hc c hcm)
      simp only [hp]
      exact rupHints_sound hdb hneg hs ρ' hρ'

theorem propRound_sound {σ : ℕ → Bool} :
    ∀ (cs : List PBConstr) (ρ : List (Literal ℕ)), (∀ c ∈ cs, c.Holds σ) → Consistent σ ρ →
      ∃ ρ', propRound cs ρ = some ρ' ∧ Consistent σ ρ'
  | [], ρ, _, hρ => ⟨ρ, rfl, hρ⟩
  | c :: cs, ρ, hcs, hρ => by
    obtain ⟨ρ', hp, hρ'⟩ := propagate_sound hρ (hcs c (by simp))
    obtain ⟨ρ'', hr, hρ''⟩ := propRound_sound cs ρ' (fun c hc => hcs c (by simp [hc])) hρ'
    exact ⟨ρ'', by simp [propRound, hp, hr], hρ''⟩

theorem rupFix_sound {σ : ℕ → Bool} {cs : List PBConstr} (hcs : ∀ c ∈ cs, c.Holds σ) :
    ∀ (fuel : ℕ) (ρ : List (Literal ℕ)), Consistent σ ρ → rupFix cs fuel ρ = false
  | 0, _, _ => rfl
  | fuel + 1, ρ, hρ => by
    obtain ⟨ρ', hp, hρ'⟩ := propRound_sound cs ρ hcs hρ
    simp only [rupFix, hp]
    split
    · rfl
    · exact rupFix_sound hcs fuel ρ' hρ'

/-- **RUP is sound**: a constraint accepted by RUP holds wherever the database does. -/
theorem rup_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} {c : PBConstr}
    {hs : Option (List Hint)} (hdb : AllHold σ db) (h : rup db c hs = true) : c.Holds σ := by
  by_contra hc
  have hneg : c.negate.Holds σ := (holds_negate σ c).mpr hc
  have hρ : Consistent σ [] := fun _ h => by simp at h
  cases hs with
  | some hs => simp [rup, rupHints_sound hdb hneg hs [] hρ] at h
  | none =>
    have hcs : ∀ c' ∈ c.negate :: db.map (·.2), c'.Holds σ := by
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hneg
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc'
        exact hdb e he
    simp [rup, rupFix_sound hcs _ [] hρ] at h

/-! ### Cutting planes in reverse Polish notation -/

/-- An operation of a `pol` step. The number operand of `*` and `d` is written into the
operation. -/
inductive PolOp where
  /-- Push the constraint with this number. -/
  | id (n : ℕ)
  /-- Push the literal axiom `ℓ ≥ 0`. -/
  | lit (l : Literal ℕ)
  /-- `+`: add the top two constraints. -/
  | add
  /-- `k *`: multiply the top constraint by `k`. -/
  | mul (k : ℕ)
  /-- `k d`: divide the top constraint by `k`, rounding up. -/
  | div (k : ℕ)
  /-- `s`: saturate the top constraint. -/
  | sat
  /-- `x w`: weaken the top constraint on the variable `x`. -/
  | weaken (v : ℕ)
  deriving DecidableEq, Repr

/-- Run the operations of a `pol` step on a stack of constraints, top first. -/
def polEval (db : List (ℕ × PBConstr)) : List PolOp → List PBConstr → Option (List PBConstr)
  | [], st => some st
  | .id n :: ops, st => (lookup db n).bind fun c => polEval db ops (c :: st)
  | .lit l :: ops, st => polEval db ops (litAxiom l :: st)
  | .add :: ops, c₂ :: c₁ :: st => polEval db ops (c₁.add c₂ :: st)
  | .mul k :: ops, c :: st => polEval db ops (c.mul k :: st)
  | .div k :: ops, c :: st => polEval db ops (c.div k :: st)
  | .sat :: ops, c :: st => polEval db ops (c.saturate :: st)
  | .weaken v :: ops, c :: st => polEval db ops (c.weaken v :: st)
  | _, _ => none

theorem polEval_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} (hdb : AllHold σ db) :
    ∀ (ops : List PolOp) (st st' : List PBConstr), (∀ c ∈ st, c.Holds σ) →
      polEval db ops st = some st' → ∀ c ∈ st', c.Holds σ
  | [], st, st', hst, h => by cases h; exact hst
  | .id n :: ops, st, st', hst, h => by
    simp only [polEval, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    exact polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨hdb.lookup hc, hst⟩) h
  | .lit l :: ops, st, st', hst, h =>
    polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨holds_litAxiom σ l, hst⟩) h
  | .add :: ops, c₂ :: c₁ :: st, st', hst, h => by
    simp only [List.forall_mem_cons] at hst
    exact polEval_sound hdb ops _ st'
      (List.forall_mem_cons.2 ⟨hst.2.1.add hst.1, hst.2.2⟩) h
  | .mul k :: ops, c :: st, st', hst, h => by
    simp only [List.forall_mem_cons] at hst
    exact polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨hst.1.mul k, hst.2⟩) h
  | .div k :: ops, c :: st, st', hst, h => by
    simp only [List.forall_mem_cons] at hst
    exact polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨hst.1.div k, hst.2⟩) h
  | .sat :: ops, c :: st, st', hst, h => by
    simp only [List.forall_mem_cons] at hst
    exact polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨hst.1.saturate, hst.2⟩) h
  | .weaken v :: ops, c :: st, st', hst, h => by
    simp only [List.forall_mem_cons] at hst
    exact polEval_sound hdb ops _ st' (List.forall_mem_cons.2 ⟨hst.1.weaken v, hst.2⟩) h
  | .add :: _, [], _, _, h => by simp [polEval] at h
  | .add :: _, [_], _, _, h => by simp [polEval] at h
  | .mul _ :: _, [], _, _, h => by simp [polEval] at h
  | .div _ :: _, [], _, _, h => by simp [polEval] at h
  | .sat :: _, [], _, _, h => by simp [polEval] at h
  | .weaken _ :: _, [], _, _, h => by simp [polEval] at h

/-! ### Steps and proofs -/

/-- A step of a kernel proof. -/
inductive Step where
  /-- `pol ops;`: a cutting-planes derivation, which must leave exactly one constraint. -/
  | pol (ops : List PolOp)
  /-- `rup C : hints;`, or `rup C;` without hints. -/
  | rup (c : PBConstr) (hints : Option (List Hint))
  /-- `pbc C : subproof … qed : n;`: the subproof starts from the negation of `C` and must
  derive the contradiction numbered `n`. -/
  | pbc (c : PBConstr) (sub : List Step) (qed : ℕ)
  /-- `del id ids;`: delete the constraints with these numbers. -/
  | del (ids : List ℕ)
  deriving Repr

mutual

/-- Run one step on the database `db`, whose next number is `n`. -/
def runStep (db : List (ℕ × PBConstr)) (n : ℕ) : Step → Option (List (ℕ × PBConstr) × ℕ)
  | .pol ops =>
    match polEval db ops [] with
    | some [c] => some ((n, c) :: db, n + 1)
    | _ => none
  | .rup c hs => if rup db c hs then some ((n, c.normalize) :: db, n + 1) else none
  | .pbc c sub q =>
    match runSteps ((n, c.negate) :: db) (n + 1) sub with
    | some (db', n') =>
      if (lookup db' q).any (fun c => decide c.IsContradiction) then
        some ((n', c.normalize) :: db, n' + 1)
      else none
    | none => none
  | .del ids => some (db.filter fun e => !ids.contains e.1, n)

/-- Run the steps in order. -/
def runSteps (db : List (ℕ × PBConstr)) (n : ℕ) :
    List Step → Option (List (ℕ × PBConstr) × ℕ)
  | [] => some (db, n)
  | s :: ss =>
    match runStep db n s with
    | some (db', n') => runSteps db' n' ss
    | none => none

end

/-- A kernel proof of `UNSAT`: its steps, and the number of the contradiction named by
`conclusion UNSAT : n;`. -/
structure Proof where
  /-- The steps. -/
  steps : List Step
  /-- The number of the contradiction. -/
  conclusion : ℕ
  deriving Repr

/-- The database of a formula: its constraints numbered from `1`, normalized. -/
def initDb (F : List PBConstr) : List (ℕ × PBConstr) :=
  F.zipIdx.map fun e => (e.2 + 1, e.1.normalize)

/-- **The checker**: run the steps from the formula and check that the conclusion names a
contradiction. -/
def check (F : List PBConstr) (P : Proof) : Bool :=
  match runSteps (initDb F) (F.length + 1) P.steps with
  | some (db, _) => (lookup db P.conclusion).any fun c => decide c.IsContradiction
  | none => false

/-! ### Soundness -/

mutual

theorem runStep_sound {σ : ℕ → Bool} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (s : Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      AllHold σ db → runStep db n s = some (db', n') → AllHold σ db'
  | db, n, .pol ops, db', n', hdb, h => by
    simp only [runStep] at h
    split at h
    · rename_i c hc
      cases h
      have := polEval_sound hdb ops [] [c] (by simp) hc
      exact List.forall_mem_cons.2 ⟨this c (by simp), hdb⟩
    · cases h
  | db, n, .rup c hs, db', n', hdb, h => by
    simp only [runStep] at h
    split at h
    · rename_i hr
      cases h
      exact List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 (rup_sound hdb hr), hdb⟩
    · cases h
  | db, n, .pbc c sub q, db', n', hdb, h => by
    simp only [runStep] at h
    split at h
    · rename_i db'' n'' hsub
      split at h
      · rename_i hq
        cases h
        refine List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 ?_, hdb⟩
        by_contra hc
        have hext : AllHold σ ((n, c.negate) :: db) :=
          List.forall_mem_cons.2 ⟨(holds_negate σ c).2 hc, hdb⟩
        have hall := runSteps_sound _ _ sub db'' n'' hext hsub
        obtain ⟨c', hc', hcon⟩ := (Option.any_eq_true _ _).mp hq
        exact (of_decide_eq_true hcon).not_holds σ (hall.lookup hc')
      · cases h
    · cases h
  | db, n, .del ids, db', n', hdb, h => by
    simp only [runStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun e he => hdb e (List.mem_of_mem_filter he)

theorem runSteps_sound {σ : ℕ → Bool} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      AllHold σ db → runSteps db n ss = some (db', n') → AllHold σ db'
  | db, n, [], db', n', hdb, h => by
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hdb
  | db, n, s :: ss, db', n', hdb, h => by
    simp only [runSteps] at h
    split at h
    · rename_i db₁ n₁ h₁
      exact runSteps_sound db₁ n₁ ss db' n' (runStep_sound db n s db₁ n₁ hdb h₁) h
    · cases h

end

theorem allHold_initDb {σ : ℕ → Bool} {F : List PBConstr} (hF : ∀ c ∈ F, c.Holds σ) :
    AllHold σ (initDb F) := by
  intro e he
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp he
  exact (holds_normalize σ c).2 (hF c (List.mem_iff_getElem.2 (by
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 hci
    rw [List.getElem_zipIdx] at hji
    simp only [Prod.mk.injEq] at hji
    exact ⟨j, by simpa using hj, hji.1⟩)))

/-- **Soundness of the checker**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_check {F : List PBConstr} {P : Proof} (h : check F P = true)
    (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  unfold check at h
  split at h
  · rename_i db n hrun
    have hall := runSteps_sound _ _ _ db n (allHold_initDb hF) hrun
    obtain ⟨c, hc, hcon⟩ := (Option.any_eq_true _ _).mp h
    exact (of_decide_eq_true hcon).not_holds σ (hall.lookup hc)
  · cases h

/-- **Soundness for CNF**: a CNF whose clauses, as pseudo-Boolean constraints, have a checked
proof of `UNSAT` is unsatisfiable. -/
theorem not_satisfiable_cnf_of_check {φ : CNF ℕ} {P : Proof}
    (h : check (φ.map Clause.toPB) P = true) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine not_satisfiable_of_check h σ fun c hc => ?_
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
  exact (Clause.holds_toPB_iff σ cl).2 ((CNF.eval_eq_true_iff σ φ).1 hσ cl hcl)

end VeriPB

end Cslib.Logic.PL

end
