/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A VeriPB kernel-proof checker: redundance-based strengthening

The rule `red C : ω` of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] adds a constraint `C` that need not follow from
the database, justified by a *witness* `ω`: a substitution of variables by `0`, `1` or literals
(`Cslib.Logic.PL.VeriPB.Witness`). It is sound when every assignment `σ` satisfying the database
and violating `C` is repaired by `ω`: the assignment `σ ∘ ω` (`Cslib.Logic.PL.VeriPB.Witness.apply`)
satisfies the database and `C`. Then adding `C` keeps a satisfiable database satisfiable, which is
all a proof of `UNSAT` needs.

Applying `ω` to a constraint `D` gives `D|ω` (`Cslib.Logic.PL.VeriPB.Witness.substC`), and
`σ` satisfies `D|ω` exactly when `σ ∘ ω` satisfies `D`
(`Cslib.Logic.PL.VeriPB.Witness.holds_substC`). The *proof goals* are `C|ω` and `D|ω` for every
constraint `D` of the database, each to be shown from the database and `¬C`.

**The step** (`Cslib.Logic.PL.VeriPB.redCheck`), as in VeriPB and CakePB: `¬C` takes the next
number and the subproof runs. Its items are derivation steps (`Cslib.Logic.PL.VeriPB.Step`,
including deletion), which may use `¬C`, and `proofgoal` blocks
(`Cslib.Logic.PL.VeriPB.RedItem.goal`), each starting from the negation of its goal and ending at
a contradiction, after which its constraints are dropped; a block is checked by
`Cslib.Logic.PL.VeriPB.subproofRefutes`, as a `pbc` subproof is. The step is
accepted when the subproof closes with a contradiction (then `C` follows outright), or when every
goal is covered (`Cslib.Logic.PL.VeriPB.goalCovered`), following the autoproven goals of the
kernel format (§5.5.1 of the VeriPB/CakePB documentation, 22 June 2026 edition): trivially
true after normalization, in the database up to the order of terms, proved by a `proofgoal`
block, or weakly syntactically implied by `¬C` (`Cslib.Logic.PL.VeriPB.weakImplies`). A database
goal `D|ω` is also covered when `ω` sets every literal of `D` it touches true, or when `D` weakly
syntactically implies it. `C` takes the number after the subproof, whose constraints are
dropped.

**Weak syntactic implication.** The test is that, in the linear forms `∑ dᵥ xᵥ ≥ A` of `D` and
`∑ cᵥ xᵥ ≥ B` of `C`, `B + ∑ᵥ max(0, dᵥ - cᵥ) ≤ A`. It bounds the slack of `C` below by that of
`D` on every assignment (`Cslib.Logic.PL.VeriPB.Holds.of_weakImplies`), and it covers a `C`
obtained from `D` by adding literal axioms.

`red` is a top-level step (`Cslib.Logic.PL.VeriPB.TopStep`): subproofs contain only derivation
steps, as in VeriPB. Every derived constraint holds under every solution of the database it was
derived from. Deletion and `red` change the set of solutions, deletion by enlarging it, but both
keep a satisfiable database satisfiable, so a checked proof of `UNSAT` still shows the formula
unsatisfiable (`Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`). Matching VeriPB, `red`
steps are not cutting-planes steps, and the translation of
`Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check` covers only proofs without them.

**Scope.** This is the decision fragment of the format, for the conclusion `UNSAT`: there is no
objective, so no goal `#2`, and no order, so no dominance. Deletion is the untyped deletion of
`Cslib.Logic.PL.VeriPB.Step.del`; the checked deletions `deld` and `delc` of the format matter
only for conclusions other than `UNSAT`.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Witness`, `Cslib.Logic.PL.VeriPB.Witness.substC`: witnesses and
  substitution.
* `Cslib.Logic.PL.VeriPB.TopStep`, `Cslib.Logic.PL.VeriPB.RedProof`,
  `Cslib.Logic.PL.VeriPB.checkRed`: proofs with `red` steps and their checker.

## Main results

* `Cslib.Logic.PL.VeriPB.Witness.holds_substC`: `σ ⊨ D|ω` iff `σ ∘ ω ⊨ D`.
* `Cslib.Logic.PL.VeriPB.redCheck_sound`: a checked `red` step keeps the database satisfiable.
* `Cslib.Logic.PL.VeriPB.not_satisfiable_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.not_satisfiable_cnf_of_checkRed`: soundness for `UNSAT`.
* `Cslib.Logic.PL.VeriPB.checkRed_map_step`: without `red`, the checker of
  `Cslib.Logic.PL.VeriPB.check`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace VeriPB

open PBConstr

/-! ### Witnesses -/

/-- The value a witness gives a variable. -/
inductive WVal where
  /-- The constant `0`. -/
  | zero
  /-- The constant `1`. -/
  | one
  /-- A literal. -/
  | lit (l : Literal ℕ)
  deriving DecidableEq, Repr

/-- A witness: a substitution of variables by `0`, `1` or literals, as a list of pairs; a
variable not listed is left alone. -/
abbrev Witness := List (ℕ × WVal)

namespace Witness

/-- The value the witness gives `v`, if any. -/
def find (ω : Witness) (v : ℕ) : Option WVal := (ω.find? (·.1 == v)).map (·.2)

/-- The assignment `σ ∘ ω`: the value of `v` under `ω`, evaluated in `σ`. -/
def apply (σ : ℕ → Bool) (ω : Witness) (v : ℕ) : Bool :=
  match ω.find v with
  | none => σ v
  | some .zero => false
  | some .one => true
  | some (.lit l) => Literal.eval σ l

/-- A term under the witness: the terms it becomes and the constant it contributes. -/
def substTerm (ω : Witness) (t : ℕ × Literal ℕ) : List (ℕ × Literal ℕ) × ℕ :=
  match ω.find (termVar t) with
  | none => ([t], 0)
  | some .zero => ([], if termPos t then 0 else t.1)
  | some .one => ([], if termPos t then t.1 else 0)
  | some (.lit l) => ([(t.1, if termPos t then l else Std.Sat.Literal.negate l)], 0)

/-- **The constraint `D|ω`**: every term under the witness, constants moved into the degree. -/
def substC (ω : Witness) (c : PBConstr) : PBConstr :=
  ⟨c.terms.flatMap fun t => (substTerm ω t).1,
    c.degree - (c.terms.map fun t => (substTerm ω t).2).sum⟩

theorem not_beq_eq_beq_not (x y : Bool) : (!x == y) = (x == !y) := by
  cases x <;> cases y <;> rfl

theorem termVal_apply (σ : ℕ → Bool) (ω : Witness) (t : ℕ × Literal ℕ) :
    termVal (apply σ ω) t = lhs σ (substTerm ω t).1 + (substTerm ω t).2 := by
  obtain ⟨a, v, b⟩ := t
  simp only [substTerm, termVar_mk, termPos_mk]
  unfold termVal apply
  simp only [Literal.eval]
  cases hf : ω.find v with
  | none => simp [termVal, Literal.eval]
  | some w =>
    cases w <;> cases b <;>
      simp [termVal, Literal.eval, Std.Sat.Literal.negate, not_beq_eq_beq_not]

theorem lhs_apply (σ : ℕ → Bool) (ω : Witness) (ts : List (ℕ × Literal ℕ)) :
    lhs (apply σ ω) ts = lhs σ (ts.flatMap fun t => (substTerm ω t).1) +
      (ts.map fun t => (substTerm ω t).2).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons, termVal_apply, ih, List.flatMap_cons, lhs_append, List.map_cons,
      List.sum_cons]
    omega

/-- **Substitution and composition**: `σ` satisfies `D|ω` exactly when `σ ∘ ω` satisfies `D`. -/
theorem holds_substC (σ : ℕ → Bool) (ω : Witness) (c : PBConstr) :
    (substC ω c).Holds σ ↔ c.Holds (apply σ ω) := by
  unfold Holds substC
  rw [lhs_apply]
  simp only
  omega

/-- Every literal of `c` that the witness touches is set true by it. -/
def touchedTrue (ω : Witness) (c : PBConstr) : Bool :=
  c.terms.all fun t =>
    match ω.find (termVar t) with
    | none => true
    | some .zero => !termPos t
    | some .one => termPos t
    | some (.lit _) => false

/-- If the witness sets every literal it touches true, it can only raise the left-hand side. -/
theorem Holds.apply_of_touchedTrue {σ : ℕ → Bool} {ω : Witness} {c : PBConstr}
    (h : touchedTrue ω c = true) (hc : c.Holds σ) : c.Holds (apply σ ω) := by
  unfold Holds at hc ⊢
  refine hc.trans ?_
  unfold touchedTrue at h
  rw [List.all_eq_true] at h
  generalize c.terms = ts at h ⊢
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [lhs_cons]
    have ht := h t (by simp)
    have := ih fun t' h' => h t' (by simp [h'])
    suffices termVal σ t ≤ termVal (apply σ ω) t by omega
    obtain ⟨a, v, b⟩ := t
    simp only [termVar_mk, termPos_mk] at ht
    unfold termVal apply
    simp only [Literal.eval]
    cases hf : ω.find v with
    | none => simp
    | some w =>
      simp only [hf] at ht
      cases w <;> cases b <;> simp_all <;> cases σ v <;> simp

end Witness

/-! ### The `red` step -/

/-- A proof goal of a `red` step: `#1`, the constraint itself, or a constraint of the database by
number. -/
inductive GoalId where
  /-- `#1`: the goal `C|ω`. -/
  | self
  /-- The goal `D|ω` of the database constraint with this number. -/
  | db (n : ℕ)
  deriving DecidableEq, Repr

/-- An item of the subproof of a `red` step: a derivation step, which may use `¬C`, or a
`proofgoal` block, which starts from the negation of its goal and must derive the contradiction
it names. -/
inductive RedItem where
  /-- A derivation step. -/
  | step (s : Step)
  /-- `proofgoal g … qed : n`. -/
  | goal (g : GoalId) (sub : List Step) (qed : ℕ)
  deriving Repr

/-- A top-level step of a kernel proof: an implicational step, or `red C : ω` with its subproof
and an optional closing contradiction `qed : n`. -/
inductive TopStep where
  /-- An implicational step. -/
  | step (s : Step)
  /-- `red C : ω : subproof … qed [: n]`. -/
  | red (c : PBConstr) (ω : Witness) (items : List RedItem) (qed : Option ℕ)
  deriving Repr

/-- The constraint of a goal: `C|ω` or `D|ω`, with `D` looked up in the database `db₀` of the
step. -/
def goalOf (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr) : GoalId → Option PBConstr
  | .self => some (Witness.substC ω c)
  | .db n => (lookup db₀ n).map (Witness.substC ω)

/-- Run the items of a `red` subproof, collecting the goal constraints proved by `proofgoal`
blocks. A block's constraints are dropped after it; only the numbering advances. -/
def runItems (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr) :
    List (ℕ × PBConstr) → ℕ → List RedItem → List PBConstr →
      Option (List (ℕ × PBConstr) × ℕ × List PBConstr)
  | db, n, [], proved => some (db, n, proved)
  | db, n, .step s :: items, proved =>
    match runStep db n s with
    | some (db', n') => runItems db₀ ω c db' n' items proved
    | none => none
  | db, n, .goal g sub q :: items, proved =>
    match goalOf db₀ ω c g with
    | none => none
    | some G =>
      match subproofRefutes (fun db n => runSteps db n sub) db n G q with
      | some n' => runItems db₀ ω c db n' items (G :: proved)
      | none => none

/-- The linear form `L - L'`: `L` with the coefficients of `L'` subtracted. -/
def subLinear (L L' : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  L'.foldr (fun e L => insertCoeff e.1 (-e.2) L) L

/-- The sum of the positive coefficients of a linear form. -/
def posMass (L : List (ℕ × ℤ)) : ℕ := (L.map fun e => e.2.toNat).sum

/-- **Weak syntactic implication**: `D` implies `C` because the slack of `C` exceeds that of `D`
on every assignment. In the linear forms `∑ dᵥ xᵥ ≥ A` and `∑ cᵥ xᵥ ≥ B`, it suffices that
`B + ∑ᵥ max(0, dᵥ - cᵥ) ≤ A`. This holds when `C` follows from `D` by adding literal axioms. -/
def weakImplies (D C : PBConstr) : Bool :=
  decide (((C.degree : ℤ) - negSum C.terms) +
      posMass (subLinear (toLinear D.terms) (toLinear C.terms)) ≤
    (D.degree : ℤ) - negSum D.terms)

/-- `C` and `D` are the same constraint up to the order of their terms. -/
def sameUpToOrder (C D : PBConstr) : Bool := C.degree == D.degree && C.terms.isPerm D.terms

/-- A goal constraint `G` needs no subproof, given the negation `negC` of the constraint being
added: it is trivially true after normalization, it is a constraint of the database up to the
order of terms, a `proofgoal` block proved it, or `negC` weakly syntactically implies it. -/
def goalCovered (db₀ : List (ℕ × PBConstr)) (proved : List PBConstr) (negC G : PBConstr) :
    Bool :=
  G.normalize.degree == 0 || db₀.any (fun e => sameUpToOrder e.2 G.normalize) ||
    proved.contains G || weakImplies negC G

/-- The end of a `red` subproof: the closing constraint is a contradiction, or every goal is
covered. -/
def redOk (db₀ : List (ℕ × PBConstr)) (ω : Witness) (c : PBConstr) (db' : List (ℕ × PBConstr))
    (proved : List PBConstr) : Option ℕ → Bool
  | some q => namesContra db' q
  | none =>
    goalCovered db₀ proved c.negate (Witness.substC ω c) &&
      db₀.all fun e => Witness.touchedTrue ω e.2 || weakImplies e.2 (Witness.substC ω e.2) ||
        goalCovered db₀ proved c.negate (Witness.substC ω e.2)

/-- **The redundance check** of `red C : ω`: `¬C` takes the number `n`, the subproof runs, and
then either the closing contradiction is derived, or `C|ω` is covered and so is `D|ω` for every
constraint `D` of the database, `D|ω` also when `ω` sets every literal of `D` it touches true.
Returns the next number after the subproof. -/
def redCheck (db₀ : List (ℕ × PBConstr)) (n : ℕ) (c : PBConstr) (ω : Witness)
    (items : List RedItem) (qed : Option ℕ) : Option ℕ :=
  match runItems db₀ ω c ((n, c.negate) :: db₀) (n + 1) items [] with
  | none => none
  | some (db', n', proved) => if redOk db₀ ω c db' proved qed then some n' else none

/-- Run the top-level steps. -/
def runTop : List (ℕ × PBConstr) → ℕ → List TopStep → Option (List (ℕ × PBConstr) × ℕ)
  | db, n, [] => some (db, n)
  | db, n, .step s :: ss =>
    match runStep db n s with
    | some (db', n') => runTop db' n' ss
    | none => none
  | db, n, .red c ω items q :: ss =>
    match redCheck db n c ω items q with
    | some n' => runTop ((n', c.normalize) :: db) (n' + 1) ss
    | none => none

/-- A kernel proof of `UNSAT` with redundance steps. -/
structure RedProof where
  /-- The steps. -/
  steps : List TopStep
  /-- The number of the contradiction named by `conclusion UNSAT : n;`. -/
  conclusion : ℕ
  deriving Repr

/-- **The checker** for proofs with redundance steps. -/
def checkRed (F : List PBConstr) (P : RedProof) : Bool :=
  match runTop (initDb F) (F.length + 1) P.steps with
  | some (db, _) => namesContra db P.conclusion
  | none => false

/-! ### Soundness -/

theorem linVal_subLinear (σ : ℕ → Bool) (L L' : List (ℕ × ℤ)) :
    linVal σ (subLinear L L') = linVal σ L - linVal σ L' := by
  induction L' with
  | nil => simp [subLinear]
  | cons e L' ih =>
    simp only [subLinear, List.foldr_cons] at ih ⊢
    rw [linVal_insertCoeff, ih, linVal_cons]
    ring

theorem linVal_le_posMass (σ : ℕ → Bool) (L : List (ℕ × ℤ)) : linVal σ L ≤ posMass L := by
  induction L with
  | nil => simp [posMass]
  | cons e L ih =>
    simp only [posMass, List.map_cons, List.sum_cons, Nat.cast_add, linVal_cons] at ih ⊢
    have : e.2 * ((σ e.1).toNat : ℤ) ≤ (e.2.toNat : ℤ) := by
      cases σ e.1 <;> simp
    linarith

/-- **Weak syntactic implication is sound.** -/
theorem Holds.of_weakImplies {σ : ℕ → Bool} {D C : PBConstr} (hD : D.Holds σ)
    (h : weakImplies D C = true) : C.Holds σ := by
  rw [holds_iff_linVal] at hD ⊢
  have h1 := linVal_subLinear σ (toLinear D.terms) (toLinear C.terms)
  have h2 := linVal_le_posMass σ (subLinear (toLinear D.terms) (toLinear C.terms))
  have h3 := of_decide_eq_true h
  linarith

theorem Holds.of_sameUpToOrder {σ : ℕ → Bool} {C D : PBConstr} (hC : C.Holds σ)
    (h : sameUpToOrder C D = true) : D.Holds σ := by
  simp only [sameUpToOrder, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at h
  unfold Holds lhs at hC ⊢
  rw [← h.1, ← (h.2.map _).sum_nat]
  exact hC

theorem goalCovered_holds {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)} {proved : List PBConstr}
    {negC G : PBConstr} (hdb : AllHold σ db₀) (hp : ∀ G ∈ proved, G.Holds σ)
    (hneg : negC.Holds σ) (h : goalCovered db₀ proved negC G = true) : G.Holds σ := by
  unfold goalCovered at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at h
  rcases h with ((h | ⟨e, he, heq⟩) | h) | h
  · rw [← holds_normalize]; unfold Holds; rw [h]; exact Nat.zero_le _
  · rw [← holds_normalize]; exact Holds.of_sameUpToOrder (hdb e he) heq
  · exact hp G h
  · exact Holds.of_weakImplies hneg h

theorem runItems_sound {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)} {ω : Witness} {c : PBConstr} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (items : List RedItem) (proved : List PBConstr)
      (db' : List (ℕ × PBConstr)) (n' : ℕ) (proved' : List PBConstr),
      AllHold σ db → (∀ G ∈ proved, G.Holds σ) →
      runItems db₀ ω c db n items proved = some (db', n', proved') →
      AllHold σ db' ∧ ∀ G ∈ proved', G.Holds σ
  | db, n, [], proved, db', n', proved', hdb, hp, h => by
    simp only [runItems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨hdb, hp⟩
  | db, n, .step s :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runItems] at h
    split at h
    · rename_i db₁ n₁ h₁
      exact runItems_sound db₁ n₁ items proved db' n' proved' (runStep_sound _ _ _ _ _ hdb h₁) hp h
    · cases h
  | db, n, .goal g sub q :: items, proved, db', n', proved', hdb, hp, h => by
    simp only [runItems] at h
    split at h
    · cases h
    · rename_i G hG
      split at h
      · rename_i n₁ h₁
        refine runItems_sound db n₁ items (G :: proved) db' n' proved' hdb
          (List.forall_mem_cons.2 ⟨holds_of_subproofRefutes
            (fun _ _ hext hsub => runSteps_sound _ _ sub _ _ hext hsub) hdb h₁, hp⟩) h
      · cases h

/-- **The redundance check is sound**: an assignment satisfying the database is either one
satisfying `C` too, or `σ ∘ ω` satisfies the database and `C`. -/
theorem redCheck_sound {σ : ℕ → Bool} {db₀ : List (ℕ × PBConstr)} {n n' : ℕ} {c : PBConstr}
    {ω : Witness} {items : List RedItem} {qed : Option ℕ} (hdb : AllHold σ db₀)
    (h : redCheck db₀ n c ω items qed = some n') :
    ∃ τ, AllHold τ ((n', c.normalize) :: db₀) := by
  by_cases hc : c.Holds σ
  · exact ⟨σ, List.forall_mem_cons.2 ⟨(holds_normalize σ c).2 hc, hdb⟩⟩
  unfold redCheck at h
  split at h
  · cases h
  rename_i db' n'' proved hrun
  have hnegC : c.negate.Holds σ := (holds_negate σ c).2 hc
  have hneg : AllHold σ ((n, c.negate) :: db₀) := List.forall_mem_cons.2 ⟨hnegC, hdb⟩
  obtain ⟨hall, hp⟩ := runItems_sound _ _ _ [] db' n'' proved hneg (by simp) hrun
  split at h
  · rename_i hok
    cases h
    refine ⟨Witness.apply σ ω, ?_⟩
    cases qed with
    | some q =>
      simp [redOk, hall.not_namesContra] at hok
    | none =>
      simp only [redOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hok
      obtain ⟨hself, hdbg⟩ := hok
      refine List.forall_mem_cons.2 ⟨?_, fun e he => ?_⟩
      · rw [holds_normalize, ← Witness.holds_substC]
        exact goalCovered_holds hdb hp hnegC hself
      · rcases hdbg e he with (ht | hw) | hg
        · exact Witness.Holds.apply_of_touchedTrue ht (hdb e he)
        · rw [← Witness.holds_substC]; exact Holds.of_weakImplies (hdb e he) hw
        · rw [← Witness.holds_substC]; exact goalCovered_holds hdb hp hnegC hg
  · cases h

theorem runTop_sound :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List TopStep) (db' : List (ℕ × PBConstr))
      (n' : ℕ), (∃ σ, AllHold σ db) → runTop db n ss = some (db', n') → ∃ σ, AllHold σ db'
  | db, n, [], db', n', hdb, h => by
    simp only [runTop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hdb
  | db, n, .step s :: ss, db', n', ⟨σ, hσ⟩, h => by
    simp only [runTop] at h
    split at h
    · rename_i db₁ n₁ h₁
      exact runTop_sound db₁ n₁ ss db' n' ⟨σ, runStep_sound _ _ _ _ _ hσ h₁⟩ h
    · cases h
  | db, n, .red c ω items q :: ss, db', n', ⟨σ, hσ⟩, h => by
    simp only [runTop] at h
    split at h
    · rename_i n₁ h₁
      exact runTop_sound _ _ ss db' n' (redCheck_sound hσ h₁) h
    · cases h

/-- **Soundness with redundance**: a formula with a checked proof of `UNSAT` has no solution. -/
theorem not_satisfiable_of_checkRed {F : List PBConstr} {P : RedProof} (h : checkRed F P = true)
    (σ : ℕ → Bool) : ¬ ∀ c ∈ F, c.Holds σ := fun hF => by
  unfold checkRed at h
  split at h
  · rename_i db n hrun
    obtain ⟨τ, hτ⟩ := runTop_sound _ _ _ db n ⟨σ, allHold_initDb hF⟩ hrun
    simp [hτ.not_namesContra] at h
  · cases h

/-- **Soundness for CNF with redundance.** -/
theorem not_satisfiable_cnf_of_checkRed {φ : CNF ℕ} {P : RedProof}
    (h : checkRed (φ.map Clause.toPB) P = true) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine not_satisfiable_of_checkRed h σ fun c hc => ?_
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
  exact (Clause.holds_toPB_iff σ cl).2 ((CNF.eval_eq_true_iff σ φ).1 hσ cl hcl)

/-! ### Proofs without redundance -/

theorem runTop_map_step (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step) :
    runTop db n (ss.map .step) = runSteps db n ss := by
  induction ss generalizing db n with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, runTop, runSteps]
    rcases h : runStep db n s with _ | ⟨db', n'⟩ <;> simp [ih]

/-- On proofs without `red`, the checker is the checker of implicational steps. -/
theorem checkRed_map_step (F : List PBConstr) (P : Proof) :
    checkRed F ⟨P.steps.map .step, P.conclusion⟩ = check F P := by
  unfold checkRed check
  rw [runTop_map_step]
  rcases runSteps (initDb F) (F.length + 1) P.steps with _ | ⟨db, n⟩ <;> rfl

end VeriPB

end Cslib.Logic.PL

end
