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
* `rup`: a constraint implied by reverse unit propagation along ordered hints
  (`Cslib.Logic.PL.VeriPB.Hint`);
* `pbc`: proof by contradiction, a subproof from the negated constraint that ends at a
  contradiction;
* `del`: deletion;

with the conclusion `UNSAT` naming a contradiction (`Cslib.Logic.PL.VeriPB.Proof`). The steps are
abstract syntax, not text: a step `pol 3 5 + 2 d;` is `.pol [.id 3, .id 5, .add, .div 2]`, the
number operand of `*` and `d` written into the operation. As in the kernel format, that operand
must be positive: a `pol` step multiplying or dividing by `0` is rejected. The constraints of the
formula are numbered `1, 2, …`, and every step that derives a constraint, including the negated
constraint of a `pbc` and the steps of its subproof, takes the next number. A deletion takes no
number. After a `pbc` the constraints of its subproof are dropped and the proved constraint takes
the number after them.

**Scope.** Two points differ from the kernel format.
* *RUP without hints.* The kernel format requires hints on `rup`. The step `rupSearch C`
  (`Cslib.Logic.PL.VeriPB.Step.rupSearch`) is an extension outside the kernel format: it
  propagates every constraint of the database until a conflict or a fixpoint, as the VeriPB tool
  does for `rup C;` without hints.
* *Deletion.* The kernel format distinguishes deleting derived constraints (`deld`) from deleting
  constraints of the formula (`delc`) and checks each number against the matching set. Here `del`
  is a single untyped deletion: its numbers must be distinct and each must name a constraint of
  the database, core or derived, and those constraints are removed. Deleting
  constraints only enlarges the set of solutions of the database, so this is sound for `UNSAT`,
  the only conclusion checked here. The checker `Cslib.Logic.PL.VeriPB.checkRed` keeps the core
  set and has the typed and checked deletions of the kernel format; there, `del` is the deletion
  by reference of the augmented format (§5.7.2), unchecked when it deletes a core constraint.

**Unit propagation** on pseudo-Boolean constraints [Gocht and Nordström][GochtNordstrom2021]
works on a trail of literals taken to be true. The *slack* of `∑ aᵢ ℓᵢ ≥ d` is the sum of the
coefficients of the terms whose literals the trail does not falsify, minus `d`. A negative slack
is a conflict; otherwise every term not yet decided whose coefficient exceeds the slack must be
true (`Cslib.Logic.PL.VeriPB.propagate`). A `rup` step for `C` with hints propagates the hinted
constraints in order, `~` naming the negation of `C`, and succeeds at the first conflict. A
`rupSearch` step for `C` propagates all constraints of the database and the negation of `C` until
a conflict or until nothing changes.

**Soundness** (`Cslib.Logic.PL.VeriPB.not_satisfiable_of_check`): every constraint the checker
derives holds under every assignment satisfying the formula, so a checked proof of `UNSAT` shows
that the formula has no solution. For a CNF formula given as the constraints
`Cslib.Logic.PL.Clause.toPB` of its clauses, this is
`Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_check`.

The checker is written with structural recursion on lists, so `decide` can run it on small
proofs.

## Main definitions

* `Cslib.Logic.PL.VeriPB.propagate`: unit propagation of one constraint.
* `Cslib.Logic.PL.VeriPB.rup`, `Cslib.Logic.PL.VeriPB.rupSearch`: RUP along hints, and the
  hintless extension.
* `Cslib.Logic.PL.VeriPB.namesContra`: a constraint number names a contradiction.
* `Cslib.Logic.PL.VeriPB.Step`, `Cslib.Logic.PL.VeriPB.Proof`: kernel proofs.
* `Cslib.Logic.PL.VeriPB.check`: the checker.
* `Cslib.Logic.PL.VeriPB.IdOk`: the numbers of a database are distinct and below a bound
  (CakePB's `id_ok`).
* `Cslib.Logic.PL.VeriPB.StepEffect`: the shape of a successful step: the constraint it adds and
  its number, or the constraints it deletes.

## Main results

* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_check`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_check`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.runStep_effect`: a successful step adds one constraint at a fresh
  number, after any `pbc` subproof, or deletes some.
* `Cslib.Logic.PL.VeriPB.IdOk.runStep`: a step numbers its new constraint from the next number
  on.

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
  induction ts <;> grind [coeffSum_cons]

theorem lhs_eq_coeffSum_filter (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    lhs σ ts = coeffSum (ts.filter fun t => Literal.eval σ t.2) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons, List.filter_cons, termVal]
    cases Literal.eval σ t.2 <;> simp [ih]

/-- **Unit propagation is sound**: under an assignment consistent with the trail and satisfying
`c`, propagation finds no conflict and the extended trail stays consistent. -/
theorem propagate_sound {σ : ℕ → Bool} {ρ : List (Literal ℕ)} {c : PBConstr}
    (hρ : Consistent σ ρ) (hc : c.Holds σ) :
    ∃ ρ', propagate ρ c = some ρ' ∧ Consistent σ ρ' := by
  -- A term whose literal is true is not falsified.
  have hnf : ∀ t ∈ c.terms, Literal.eval σ t.2 = true → falsified ρ t = false := by
    intro t _ ht
    by_contra hf
    have := hρ _ (List.contains_iff_mem.mp (Bool.eq_true_of_ne_false hf))
    simp [Literal.eval_negate, ht] at this
  have hsplit := coeffSum_filter_add c.terms (fun t => !falsified ρ t)
    (fun t => Literal.eval σ t.2)
  have htrue : (c.terms.filter fun t => !falsified ρ t && Literal.eval σ t.2) =
      c.terms.filter fun t => Literal.eval σ t.2 :=
    List.filter_congr fun t ht => by grind
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
    obtain ⟨htm, hp⟩ := List.mem_filter.mp ht
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
    obtain ⟨⟨hf, -⟩, hlt⟩ := hp
    by_contra hev
    have hmem : t ∈ c.terms.filter fun t => !falsified ρ t && !Literal.eval σ t.2 := by
      simp [List.mem_filter, htm, hf, Bool.eq_false_of_ne_true hev]
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

/-- The constraint numbered `n` is a contradiction, as `conclusion UNSAT : n` and the end of a
`pbc` subproof require. -/
def namesContra (db : List (ℕ × PBConstr)) (n : ℕ) : Bool :=
  (lookup db n).any fun c => decide c.IsContradiction

/-- A database naming a contradiction has no solution. -/
theorem AllHold.not_namesContra {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} (h : AllHold σ db)
    {n : ℕ} : namesContra db n = false := by
  rw [Bool.eq_false_iff]
  intro hq
  obtain ⟨c, hc, hcon⟩ := (Option.any_eq_true _ _).mp hq
  exact (of_decide_eq_true hcon).not_holds σ (h.lookup hc)

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
hints. -/
def rup (db : List (ℕ × PBConstr)) (c : PBConstr) (hs : List Hint) : Bool :=
  rupHints db c.negate hs []

/-- **RUP without hints**, an extension of the kernel format: propagate the negation of `c` and
every constraint of the database until a conflict or a fixpoint. -/
def rupSearch (db : List (ℕ × PBConstr)) (c : PBConstr) : Bool :=
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
    {hs : List Hint} (hdb : AllHold σ db) (h : rup db c hs = true) : c.Holds σ := by
  by_contra hc
  simp [rup, rupHints_sound hdb ((holds_negate σ c).mpr hc) hs [] (List.forall_mem_nil _)] at h

theorem rupSearch_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} {c : PBConstr}
    (hdb : AllHold σ db) (h : rupSearch db c = true) : c.Holds σ := by
  by_contra hc
  have hcs : ∀ c' ∈ c.negate :: db.map (·.2), c'.Holds σ :=
    List.forall_mem_cons.2 ⟨(holds_negate σ c).mpr hc, List.forall_mem_map.2 hdb⟩
  simp [rupSearch, rupFix_sound hcs _ [] (List.forall_mem_nil _)] at h

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
  /-- `k *`: multiply the top constraint by `k`, which must be positive. -/
  | mul (k : ℕ)
  /-- `k d`: divide the top constraint by `k`, rounding up; `k` must be positive. -/
  | div (k : ℕ)
  /-- `s`: saturate the top constraint. -/
  | sat
  /-- `x w`: weaken the top constraint on the variable `x`. -/
  | weaken (v : ℕ)
  deriving DecidableEq, Repr

/-- Run the operations of a `pol` step on a stack of constraints, top first. A missing operand,
an unknown constraint number, or a multiplication or division by `0` fails. -/
def polEval (db : List (ℕ × PBConstr)) : List PolOp → List PBConstr → Option (List PBConstr)
  | [], st => some st
  | .id n :: ops, st => (lookup db n).bind fun c => polEval db ops (c :: st)
  | .lit l :: ops, st => polEval db ops (litAxiom l :: st)
  | .add :: ops, c₂ :: c₁ :: st => polEval db ops (c₁.add c₂ :: st)
  | .mul (k + 1) :: ops, c :: st => polEval db ops (c.mul (k + 1) :: st)
  | .div (k + 1) :: ops, c :: st => polEval db ops (c.div (k + 1) :: st)
  | .sat :: ops, c :: st => polEval db ops (c.saturate :: st)
  | .weaken v :: ops, c :: st => polEval db ops (c.weaken v :: st)
  | _, _ => none

theorem polEval_sound {σ : ℕ → Bool} {db : List (ℕ × PBConstr)} (hdb : AllHold σ db) :
    ∀ (ops : List PolOp) (st st' : List PBConstr), (∀ c ∈ st, c.Holds σ) →
      polEval db ops st = some st' → ∀ c ∈ st', c.Holds σ := by
  intro ops st st'
  fun_induction polEval db ops st with
  | case1 => rintro hst ⟨⟩; exact hst
  | case2 n ops st ih =>
    intro hst h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
    exact ih c (List.forall_mem_cons.2 ⟨hdb.lookup hc, hst⟩) h
  | case3 l _ _ ih => exact fun hst => ih (List.forall_mem_cons.2 ⟨holds_litAxiom σ l, hst⟩)
  | case4 _ _ _ _ ih =>
    simp only [List.forall_mem_cons] at ih ⊢
    exact fun ⟨h₂, h₁, hst⟩ => ih ⟨h₁.add h₂, hst⟩
  | case5 k _ _ _ ih =>
    simp only [List.forall_mem_cons] at ih ⊢
    exact fun ⟨h, hst⟩ => ih ⟨h.mul (k + 1), hst⟩
  | case6 k _ _ _ ih =>
    simp only [List.forall_mem_cons] at ih ⊢
    exact fun ⟨h, hst⟩ => ih ⟨h.div (k + 1), hst⟩
  | case7 _ _ _ ih =>
    simp only [List.forall_mem_cons] at ih ⊢
    exact fun ⟨h, hst⟩ => ih ⟨h.saturate, hst⟩
  | case8 v _ _ _ ih =>
    simp only [List.forall_mem_cons] at ih ⊢
    exact fun ⟨h, hst⟩ => ih ⟨h.weaken v, hst⟩
  | case9 => rintro _ ⟨⟩

/-! ### Subproofs by contradiction -/

/-- **A scoped subproof by contradiction** of `G`, the subproof given by its runner `run`: the
negation of `G` takes the number `n`, the subproof runs from the database extended by it, and its
result must name a contradiction `q`. Returns the next number after the subproof; the subproof's
constraints are dropped. Used by `pbc` and by the `proofgoal` blocks of `red`. -/
def subproofRefutes (run : List (ℕ × PBConstr) → ℕ → Option (List (ℕ × PBConstr) × ℕ))
    (db : List (ℕ × PBConstr)) (n : ℕ) (G : PBConstr) (q : ℕ) : Option ℕ :=
  match run ((n, G.negate) :: db) (n + 1) with
  | some (db', n') => if namesContra db' q then some n' else none
  | none => none

/-- **A scoped subproof by contradiction is sound**: if the runner keeps every solution of the
extended database, `G` holds under every solution of the database. -/
theorem holds_of_subproofRefutes {σ : ℕ → Bool}
    {run : List (ℕ × PBConstr) → ℕ → Option (List (ℕ × PBConstr) × ℕ)}
    {db : List (ℕ × PBConstr)} {n n' : ℕ} {G : PBConstr} {q : ℕ}
    (hrun : ∀ db' n'', AllHold σ ((n, G.negate) :: db) →
      run ((n, G.negate) :: db) (n + 1) = some (db', n'') → AllHold σ db')
    (hdb : AllHold σ db) (h : subproofRefutes run db n G q = some n') : G.Holds σ := by
  by_contra hG
  unfold subproofRefutes at h
  split at h
  · have hall := hrun _ _ (List.forall_mem_cons.2 ⟨(holds_negate σ G).2 hG, hdb⟩) ‹_›
    simp [hall.not_namesContra] at h
  · cases h

/-! ### Steps and proofs -/

/-- A step of a kernel proof. -/
inductive Step where
  /-- `pol ops;`: a cutting-planes derivation, which must leave exactly one constraint. -/
  | pol (ops : List PolOp)
  /-- `rup C : hints;`. -/
  | rup (c : PBConstr) (hints : List Hint)
  /-- `rup C;` without hints: an extension outside the kernel format, checked by propagating the
  whole database (`Cslib.Logic.PL.VeriPB.rupSearch`). -/
  | rupSearch (c : PBConstr)
  /-- `pbc C : subproof … qed : n;`: the subproof starts from the negation of `C` and must
  derive the contradiction numbered `n`. -/
  | pbc (c : PBConstr) (sub : List Step) (qed : ℕ)
  /-- `del id ids;`: delete the constraints with these distinct numbers, each of which must be in
  the database. This untyped deletion is `del id` of the augmented format and takes no number; it
  only enlarges the set of solutions of the database. -/
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
  | .rupSearch c => if rupSearch db c then some ((n, c.normalize) :: db, n + 1) else none
  | .pbc c sub q =>
    (subproofRefutes (fun db n => runSteps db n sub) db n c q).map
      fun n' => ((n', c.normalize) :: db, n' + 1)
  | .del ids =>
    if decide ids.Nodup && ids.all (fun i => (lookup db i).isSome) then
      some (db.filter fun e => !ids.contains e.1, n)
    else none

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
  | some (db, _) => namesContra db P.conclusion
  | none => false

/-! ### Soundness -/

mutual

theorem runStep_sound {σ : ℕ → Bool} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (s : Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      AllHold σ db → runStep db n s = some (db', n') → AllHold σ db'
  | db, n, .pol ops, db', n', hdb, h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact List.forall_mem_cons.2 ⟨polEval_sound hdb ops [] _ (by simp) ‹_› _ (by simp), hdb⟩
  | db, n, .rup c hs, db', n', hdb, h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 (rup_sound hdb ‹_›), hdb⟩
  | db, n, .rupSearch c, db', n', hdb, h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 (rupSearch_sound hdb ‹_›), hdb⟩
  | db, n, .pbc c sub q, db', n', hdb, h => by
    obtain ⟨n'', hq, rfl, rfl⟩ := by
      simpa only [runStep, Option.map_eq_some_iff, Prod.mk.injEq] using h
    exact List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 (holds_of_subproofRefutes
      (fun _ _ hext hsub => runSteps_sound _ _ sub _ _ hext hsub) hdb hq), hdb⟩
  | db, n, .del ids, db', n', hdb, h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact fun e he => hdb e (List.mem_of_mem_filter he)

theorem runSteps_sound {σ : ℕ → Bool} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      AllHold σ db → runSteps db n ss = some (db', n') → AllHold σ db'
  | db, n, [], db', n', hdb, h => by
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ hdb
  | db, n, s :: ss, db', n', hdb, h => by
    simp only [runSteps] at h
    split at h
    · exact runSteps_sound _ _ ss db' n' (runStep_sound db n s _ _ hdb ‹_›) h
    · cases h

end

theorem allHold_initDb {σ : ℕ → Bool} {F : List PBConstr} (hF : ∀ c ∈ F, c.Holds σ) :
    AllHold σ (initDb F) := by
  intro e he
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp he
  exact (holds_normalize σ c).2 (hF c (List.fst_mem_of_mem_zipIdx hci))

/-! ### Fresh numbers -/

/-- **The numbers of the database `db` are fresh from `n` on**: every number is below `n`, and no
two constraints share one. This is CakePB's `id_ok fml n`, with the distinctness that CakePB's
finite maps have built in. -/
structure IdOk (db : List (ℕ × PBConstr)) (n : ℕ) : Prop where
  /-- Every number is below `n`. -/
  lt : ∀ e ∈ db, e.1 < n
  /-- No two constraints share a number. -/
  nodup : (db.map (·.1)).Nodup

namespace IdOk

variable {db : List (ℕ × PBConstr)} {n : ℕ}

/-- Two constraints with the same number are the same. -/
theorem eq_of_mem (h : IdOk db n) {i : ℕ} {c c' : PBConstr} (hc : (i, c) ∈ db)
    (hc' : (i, c') ∈ db) : c = c' :=
  (Prod.ext_iff.1 (List.inj_on_of_nodup_map h.nodup hc hc' rfl)).2

/-- The numbers stay fresh from a later number on. -/
theorem mono (h : IdOk db n) {m : ℕ} (hm : n ≤ m) : IdOk db m :=
  ⟨fun e he => (h.lt e he).trans_le hm, h.nodup⟩

/-- A constraint numbered `m ≥ n` may join the database, and the numbers are fresh from `m + 1`
on. -/
theorem cons (h : IdOk db n) {m : ℕ} (hm : n ≤ m) (c : PBConstr) :
    IdOk ((m, c) :: db) (m + 1) where
  lt e he := by
    rcases List.mem_cons.1 he with rfl | he
    exacts [m.lt_succ_self, (h.lt e he).trans_le (hm.trans m.le_succ)]
  nodup := List.nodup_cons.2 ⟨fun hm' => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm'
    exact (h.lt e he).not_ge hm, h.nodup⟩

/-- Deleting constraints keeps the numbers fresh. -/
theorem filter (h : IdOk db n) (p : ℕ × PBConstr → Bool) : IdOk (db.filter p) n :=
  ⟨fun e he => h.lt e (List.mem_of_mem_filter he), h.nodup.sublist (List.filter_sublist.map _)⟩

end IdOk

/-- The input database is numbered from `1` to the number of its constraints. -/
theorem idOk_initDb (F : List PBConstr) : IdOk (initDb F) (F.length + 1) := by
  have hmap : (initDb F).map (·.1) = List.range' 1 F.length := by
    simp only [initDb, List.map_map]
    rw [show ((·.1) ∘ fun e : PBConstr × ℕ => (e.2 + 1, e.1.normalize)) =
      (1 + ·) ∘ Prod.snd from funext fun _ => Nat.add_comm _ _, ← List.map_map,
      List.zipIdx_map_snd, List.map_add_range']
  refine ⟨fun e he => ?_, hmap ▸ List.nodup_range'⟩
  have := List.mem_map_of_mem (f := (·.1)) he
  rw [hmap, List.mem_range'_1] at this
  omega

/-- **The shape of a successful step on the database `db`, whose next number is `n`**: which
constraint it adds, at which number, and what it deletes. Each addition puts its constraint in
front and continues from the number after it: `pol`, `rup` and `rupSearch` at `n`, and `pbc` at
some number `m > n`. `rup`, `rupSearch` and `pbc` add their stated constraint, normalized; for
`pol` the relation records only that one constraint is added, not which. A deletion `del ids`
drops the constraints numbered in `ids` and keeps the next number. The relation does not record
that a step's check passed, nor, for `pbc`, which number its subproof stops at: any `m > n` is
allowed. `Cslib.Logic.PL.VeriPB.runStep_effect` shows that a successful `runStep` has this
shape, taking `m` from the counter at which the subproof of a `pbc` step stops, above `n` since
the negated constraint takes `n`. -/
inductive StepEffect (db : List (ℕ × PBConstr)) (n : ℕ) :
    Step → List (ℕ × PBConstr) → ℕ → Prop where
  /-- `pol ops` adds the constraint `c` that its derivation leaves, at `n`. -/
  | pol {ops : List PolOp} (c : PBConstr) : StepEffect db n (.pol ops) ((n, c) :: db) (n + 1)
  /-- `rup c hs` adds `c` at `n`. -/
  | rup {c : PBConstr} {hs : List Hint} :
      StepEffect db n (.rup c hs) ((n, c.normalize) :: db) (n + 1)
  /-- `rupSearch c` adds `c` at `n`. -/
  | rupSearch {c : PBConstr} :
      StepEffect db n (.rupSearch c) ((n, c.normalize) :: db) (n + 1)
  /-- `pbc c sub q` adds `c`, normalized, at some number `m > n`; `m` does not depend on
  `sub`. -/
  | pbc {c : PBConstr} {sub : List Step} {q m : ℕ} (hm : n < m) :
      StepEffect db n (.pbc c sub q) ((m, c.normalize) :: db) (m + 1)
  /-- `del ids` drops the constraints numbered in `ids`. -/
  | del (ids : List ℕ) : StepEffect db n (.del ids) (db.filter fun e => !ids.contains e.1) n

namespace StepEffect

variable {db db' : List (ℕ × PBConstr)} {n n' : ℕ} {s : Step}

/-- A step only advances the numbering. -/
theorem le (h : StepEffect db n s db' n') : n ≤ n' := by
  cases h with
  | pol | rup | rupSearch => exact Nat.le_succ n
  | pbc hm => exact hm.le.trans (Nat.le_succ _)
  | del ids => exact le_rfl

/-- A step keeps the numbers fresh. -/
theorem idOk (h : StepEffect db n s db' n') (hid : IdOk db n) : IdOk db' n' := by
  cases h with
  | pol c => exact hid.cons le_rfl c
  | rup | rupSearch => exact hid.cons le_rfl _
  | pbc hm => exact hid.cons hm.le _
  | del ids => exact hid.filter _

/-- A step keeps every constraint whose number it does not delete. -/
theorem mem (h : StepEffect db n s db' n') {e : ℕ × PBConstr} (he : e ∈ db)
    (hd : ∀ ids, s = .del ids → ids.contains e.1 = false) : e ∈ db' := by
  cases h with
  | pol | rup | rupSearch | pbc => exact List.mem_cons_of_mem _ he
  | del ids => exact List.mem_filter.2 ⟨he, by simpa using hd ids rfl⟩

end StepEffect

mutual

/-- **The effect of a successful step** (`Cslib.Logic.PL.VeriPB.StepEffect`). For `pbc`, the
number of the added constraint is the counter at which the successful subproof stops. -/
theorem runStep_effect :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (s : Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      runStep db n s = some (db', n') → StepEffect db n s db' n'
  | db, n, .pol ops, db', n', h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact .pol _
  | db, n, .rup c hs, db', n', h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact .rup
  | db, n, .rupSearch c, db', n', h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact .rupSearch
  | db, n, .pbc c sub q, db', n', h => by
    simp only [runStep, Option.map_eq_some_iff] at h
    obtain ⟨n'', hq, h⟩ := h
    cases h
    unfold subproofRefutes at hq
    split at hq
    · rename_i db₁ n₁ hsub
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hq
      exact .pbc (hq.2 ▸ Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (runSteps_le _ _ sub _ _ hsub))
    · cases hq
  | db, n, .del ids, db', n', h => by
    simp only [runStep] at h
    split at h <;> cases h
    exact .del ids

/-- Steps only advance the numbering. -/
theorem runSteps_le :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step) (db' : List (ℕ × PBConstr)) (n' : ℕ),
      runSteps db n ss = some (db', n') → n ≤ n'
  | db, n, [], db', n', h => by
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ le_rfl
  | db, n, s :: ss, db', n', h => by
    simp only [runSteps] at h
    split at h
    · exact (runStep_effect db n s _ _ ‹_›).le.trans (runSteps_le _ _ ss db' n' h)
    · cases h

end

/-- A step only advances the numbering. -/
theorem runStep_le (db : List (ℕ × PBConstr)) (n : ℕ) (s : Step) (db' : List (ℕ × PBConstr))
    (n' : ℕ) (h : runStep db n s = some (db', n')) : n ≤ n' :=
  (runStep_effect db n s db' n' h).le

/-- **A step keeps the numbers fresh**: a new constraint takes a number from `n` on. -/
theorem IdOk.runStep {db db' : List (ℕ × PBConstr)} {n n' : ℕ} {s : Step} (h : IdOk db n)
    (hs : runStep db n s = some (db', n')) : IdOk db' n' :=
  (runStep_effect _ _ _ _ _ hs).idOk h

/-- **Soundness of the checker**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_check {F : List PBConstr} {P : Proof} (h : check F P = true)
    (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  unfold check at h
  split at h
  · simp [(runSteps_sound _ _ _ _ _ (allHold_initDb hF) ‹_›).not_namesContra] at h
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
