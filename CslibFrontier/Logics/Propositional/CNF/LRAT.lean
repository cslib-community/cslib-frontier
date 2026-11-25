/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Std.Tactic.BVDecide.LRAT.Actions
import CslibFrontier.Foundations.Data.List.Lookup

/-! # A kernel-reducible LRAT checker

An LRAT certificate [Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017] refutes a
formula in conjunctive normal form by a sequence of steps, each adding a clause, adding the empty
clause, or deleting clauses. Every clause has a number: the clauses of the formula are numbered
`1, 2, …` in order, and every added clause carries its own number. An added clause comes with
*hints*, a list of numbers of clauses. Starting from the negation of the added clause, the hinted
clauses are visited in order. Each must have all but one of its literals false, and then the
remaining literal becomes true, except the last, which must have all its literals false. So the
added clause follows from the hinted clauses by unit propagation: it is a *RUP* clause.

`Cslib.Logic.PL.CNF.checkLRAT φ cert` checks a certificate in the format of Lean core's
`Std.Tactic.BVDecide.LRAT.IntAction`: literals are nonzero integers in DIMACS style, so the
variable `v` of `φ : CNF ℕ` is written `v + 1`, and is negated by negating the integer. It accepts
RUP steps, empty-clause steps and deletions, and rejects RAT steps. It is written with structural
recursion on lists, so the kernel can evaluate it and `decide` proves that it accepts a given
certificate. Lean core's `Std.Tactic.BVDecide.LRAT.check` checks the same format, but the kernel
cannot evaluate it, and it is only proved sound, not complete.

A clause added by a RUP step holds under every assignment satisfying the clauses so far, so an
accepted certificate shows that the formula has no model
(`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`).

## Main definitions

* `Cslib.Logic.PL.Clause.ofDIMACS`: a clause from DIMACS integers.
* `Cslib.Logic.PL.Literal.toDIMACS`, `Cslib.Logic.PL.Clause.toDIMACS`: a literal and a clause as
  DIMACS integers, inverted by `Cslib.Logic.PL.Literal.ofDIMACS_toDIMACS` and
  `Cslib.Logic.PL.Clause.ofDIMACS_toDIMACS`.
* `Cslib.Logic.PL.Clause.residual`: what is left of a clause once its false literals are removed:
  nothing, one literal possibly repeated, or more.
* `Cslib.Logic.PL.CNF.propagateHints`: unit propagation along hints.
* `Cslib.Logic.PL.CNF.lratHintCount`: the number of hints of a certificate.
* `Cslib.Logic.PL.CNF.checkLRAT`: the checker.

## Main results

* `Cslib.Logic.PL.CNF.propagateHints_cons_of_forall_ne`: a hinted clause whose literals other than
  `l` are false ends propagation successfully or propagates `l`.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`: a formula with an accepted certificate is
  unsatisfiable.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- The literal named by a DIMACS integer: `v + 1` is the variable `v` and `-(v + 1)` its
negation; `0` names nothing. -/
def Literal.ofDIMACS (i : Int) : Option (Literal ℕ) :=
  if 0 < i then some (i.natAbs - 1, true)
  else if i < 0 then some (i.natAbs - 1, false)
  else none

/-- The clause named by a list of DIMACS integers. -/
def Clause.ofDIMACS (c : List Int) : Clause ℕ :=
  c.filterMap Literal.ofDIMACS

/-- The DIMACS integer of a literal: `v + 1` for the variable `v`, `-(v + 1)` for its negation. -/
def Literal.toDIMACS (l : Literal ℕ) : Int :=
  if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

/-- A clause as DIMACS integers. -/
def Clause.toDIMACS (c : Clause ℕ) : Array Int :=
  (c.map Literal.toDIMACS).toArray

/-- The DIMACS integer of the variable `v` has absolute value `v + 1`. -/
@[simp] theorem Literal.natAbs_toDIMACS (l : Literal ℕ) : l.toDIMACS.natAbs = l.1 + 1 := by
  unfold Literal.toDIMACS
  split <;> omega

/-- **Reading the DIMACS integer of a literal gives it back.** -/
@[simp] theorem Literal.ofDIMACS_toDIMACS (l : Literal ℕ) :
    Literal.ofDIMACS l.toDIMACS = some l := by
  unfold Literal.ofDIMACS
  rw [Literal.natAbs_toDIMACS, Nat.add_sub_cancel]
  rcases l with ⟨v, _ | _⟩
  · rw [ite_eq_right (by simp [Literal.toDIMACS]; omega),
      ite_eq_left (by simp [Literal.toDIMACS]; omega)]
  · rw [ite_eq_left (by simp [Literal.toDIMACS])]

/-- Reading the DIMACS integers of a clause gives it back. -/
@[simp] theorem Clause.ofDIMACS_toDIMACS (c : Clause ℕ) :
    Clause.ofDIMACS c.toDIMACS.toList = c := by
  simp [Clause.ofDIMACS, Clause.toDIMACS, List.filterMap_map]

/-- What is left of a clause under the literals assumed true, once its false literals are
removed (`Cslib.Logic.PL.Clause.residual`). -/
inductive Clause.Residual where
  /-- Every literal of the clause is false. -/
  | empty
  /-- The literal `l`, possibly repeated: every literal of the clause but `l` is false, and `l` is
  not. -/
  | unit (l : Literal ℕ)
  /-- Two different literals of the clause are not false. -/
  | other

/-- **The residual of a clause** under the literals `t` assumed true: the literals of `c` whose
negation is not in `t`, classified as none (`empty`), one literal possibly repeated (`unit`), or
more (`other`). A literal repeated in the clause counts once. Unit propagation along hints
(`Cslib.Logic.PL.CNF.propagateWith`) reads every hinted clause through this classification. -/
def Clause.residual (c : Clause ℕ) (t : List (Literal ℕ)) : Clause.Residual :=
  match c.filter (fun l => !t.contains (Std.Sat.Literal.negate l)) with
  | [] => .empty
  | l :: ls => if ls.all (· == l) then .unit l else .other

/-- The residual of a clause is empty exactly when every literal of the clause is false. -/
theorem Clause.residual_eq_empty_iff {c : Clause ℕ} {t : List (Literal ℕ)} :
    c.residual t = .empty ↔ ∀ m ∈ c, Std.Sat.Literal.negate m ∈ t := by
  unfold residual
  split
  · rename_i h
    simpa [List.filter_eq_nil_iff] using h
  · rename_i l ls h
    have hl := List.mem_filter.1 (h ▸ List.mem_cons_self : l ∈ _)
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hl
    split <;> simp only [reduceCtorEq, false_iff, not_forall]
    all_goals exact ⟨l, hl.1, hl.2⟩

/-- The residual of a clause is the unit `l` exactly when `l` is a literal of the clause that is
not false, and every other literal of the clause is false. -/
theorem Clause.residual_eq_unit_iff {c : Clause ℕ} {t : List (Literal ℕ)} {l : Literal ℕ} :
    c.residual t = .unit l ↔
      l ∈ c ∧ Std.Sat.Literal.negate l ∉ t ∧ ∀ m ∈ c, m ≠ l → Std.Sat.Literal.negate m ∈ t := by
  have hmem (m : Literal ℕ) :
      m ∈ c.filter (fun l => !t.contains (Std.Sat.Literal.negate l)) ↔
        m ∈ c ∧ Std.Sat.Literal.negate m ∉ t := by simp
  -- under the right side, every literal of the filtered clause is `l`
  have honly (hc : ∀ m ∈ c, m ≠ l → Std.Sat.Literal.negate m ∈ t) (m)
      (hm : m ∈ c.filter (fun l => !t.contains (Std.Sat.Literal.negate l))) : m = l :=
    by_contra fun hne => ((hmem m).1 hm).2 (hc m ((hmem m).1 hm).1 hne)
  unfold residual
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun hl hlt _ => List.not_mem_nil (h ▸ (hmem l).2 ⟨hl, hlt⟩)
  · rename_i a as h
    split <;> rename_i hall
    · simp only [Clause.Residual.unit.injEq]
      refine ⟨?_, fun ⟨_, _, hc⟩ => honly hc a (h ▸ List.mem_cons_self)⟩
      rintro rfl
      refine ⟨((hmem a).1 (h ▸ List.mem_cons_self)).1, ((hmem a).1 (h ▸ List.mem_cons_self)).2,
        fun m hm hne => by_contra fun hmt => hne ?_⟩
      rcases List.mem_cons.1 (h ▸ (hmem m).2 ⟨hm, hmt⟩) with rfl | hm'
      · rfl
      · simpa using List.all_eq_true.1 hall m hm'
    · simp only [reduceCtorEq, false_iff, not_and]
      refine fun _ _ hc => hall (List.all_eq_true.2 fun m hm => ?_)
      simp [honly hc m (h ▸ List.mem_cons_of_mem _ hm), honly hc a (h ▸ List.mem_cons_self)]

/-- **A clause whose literals other than `l` are false** has an empty residual or the residual
`l`. -/
theorem Clause.residual_of_forall_ne {c : Clause ℕ} {t : List (Literal ℕ)} {l : Literal ℕ}
    (h : ∀ m ∈ c, m ≠ l → Std.Sat.Literal.negate m ∈ t) :
    c.residual t = .empty ∨ c.residual t = .unit l := by
  by_cases hl : l ∈ c ∧ Std.Sat.Literal.negate l ∉ t
  · exact .inr (residual_eq_unit_iff.2 ⟨hl.1, hl.2, h⟩)
  · exact .inl (residual_eq_empty_iff.2 fun m hm =>
      if hml : m = l then not_not.1 fun hmt => hl ⟨hml ▸ hm, hml ▸ hmt⟩ else h m hm hml)

/-- The residual of a clause reads the assumed literals only through membership. -/
theorem Clause.residual_congr (c : Clause ℕ) {t t' : List (Literal ℕ)} (h : ∀ l, l ∈ t ↔ l ∈ t') :
    c.residual t = c.residual t' := by
  have hf : (fun l => !t.contains (Std.Sat.Literal.negate l)) =
      fun l => !t'.contains (Std.Sat.Literal.negate l) :=
    funext fun _ => by simp only [List.contains_eq_mem, h]
  simp only [residual, hf]

/-- Unit propagation along hints, from the literals `trail` assumed true, reading the hinted
clauses with `lookup`. Each hinted clause must have every literal but one false under `trail`, and
that literal is added to `trail`; the run succeeds when a hinted clause has every literal false
(`Cslib.Logic.PL.Clause.residual`). The checker reads clauses from a list of numbered clauses
(`Cslib.Logic.PL.CNF.propagateHints`); a solver can read them from an index. -/
def CNF.propagateWith (lookup : ℕ → Option (Clause ℕ)) : List (Literal ℕ) → List ℕ → Bool
  | _, [] => false
  | trail, h :: hs =>
    match lookup h with
    | none => false
    | some c =>
      match c.residual trail with
      | .empty => true
      | .unit l => propagateWith lookup (l :: trail) hs
      | .other => false

/-- **One step of unit propagation along hints**: if every literal of the hinted clause other
than `l` is false, propagation succeeds, at once when `l` is also false or absent, and otherwise
when it succeeds from the trail extended by `l`. -/
theorem CNF.propagateWith_cons_of_forall_ne {lookup : ℕ → Option (Clause ℕ)}
    {t : List (Literal ℕ)} {h : ℕ} {hs : List ℕ} {c : Clause ℕ} {l : Literal ℕ}
    (hc : lookup h = some c) (hfalse : ∀ m ∈ c, m ≠ l → Std.Sat.Literal.negate m ∈ t)
    (hnext : l ∈ c → Std.Sat.Literal.negate l ∉ t → propagateWith lookup (l :: t) hs = true) :
    propagateWith lookup t (h :: hs) = true := by
  simp only [propagateWith, hc]
  rcases Clause.residual_of_forall_ne hfalse with hr | hr <;> rw [hr]
  obtain ⟨hl, hlt, -⟩ := Clause.residual_eq_unit_iff.1 hr
  exact hnext hl hlt

/-- **Unit propagation along hints** in a database of numbered clauses
(`Cslib.Logic.PL.CNF.propagateWith`), looking up the first clause of each number (`List.lookup`). -/
def CNF.propagateHints (db : List (ℕ × Clause ℕ)) : List (Literal ℕ) → List ℕ → Bool :=
  propagateWith (fun h => db.lookup h)

theorem CNF.propagateHints_nil (db : List (ℕ × Clause ℕ)) (t : List (Literal ℕ)) :
    propagateHints db t [] = false := rfl

/-- One step of unit propagation along hints in a database, by the residual of the hinted
clause. -/
theorem CNF.propagateHints_cons (db : List (ℕ × Clause ℕ)) (t : List (Literal ℕ)) (h : ℕ)
    (hs : List ℕ) :
    propagateHints db t (h :: hs) =
      match db.find? (·.1 == h) with
      | none => false
      | some e =>
        match e.2.residual t with
        | .empty => true
        | .unit l => propagateHints db (l :: t) hs
        | .other => false := by
  have hk : (fun e : ℕ × Clause ℕ => h == e.1) = (·.1 == h) := funext fun _ => BEq.comm
  simp only [propagateHints, propagateWith, List.lookup_eq_map_find?, hk]
  cases db.find? (·.1 == h) <;> rfl

/-- **One step of unit propagation along hints in a database**: if every literal of the hinted
clause other than `l` is false, propagation succeeds, at once when `l` is also false or absent,
and otherwise when it succeeds from the trail extended by `l`. -/
theorem CNF.propagateHints_cons_of_forall_ne {db : List (ℕ × Clause ℕ)} {t : List (Literal ℕ)}
    {h : ℕ} {hs : List ℕ} {e : ℕ × Clause ℕ} {l : Literal ℕ} (he : db.find? (·.1 == h) = some e)
    (hfalse : ∀ m ∈ e.2, m ≠ l → Std.Sat.Literal.negate m ∈ t)
    (hnext : l ∈ e.2 → Std.Sat.Literal.negate l ∉ t → propagateHints db (l :: t) hs = true) :
    propagateHints db t (h :: hs) = true := by
  have hk : (fun e : ℕ × Clause ℕ => h == e.1) = (·.1 == h) := funext fun _ => BEq.comm
  refine propagateWith_cons_of_forall_ne (c := e.2) ?_ hfalse hnext
  simp only [List.lookup_eq_map_find?, hk, he, Option.map_some]

/-- The **number of hints** of a certificate: the total length of the hint lists of its RUP and
empty-clause steps. The checker reads no other hints: it rejects RAT steps. -/
def CNF.lratHintCount : List LRAT.IntAction → ℕ
  | [] => 0
  | .addRup _ _ hints :: rest => hints.size + lratHintCount rest
  | .addEmpty _ hints :: rest => hints.size + lratHintCount rest
  | _ :: rest => lratHintCount rest

/-- The checker on a database of numbered clauses. -/
def CNF.checkLRATAux : List (ℕ × Clause ℕ) → List LRAT.IntAction → Bool
  | _, [] => false
  | db, .addEmpty _ hints :: _ => propagateHints db [] hints.toList
  | db, .addRup id c hints :: rest =>
    propagateHints db ((Clause.ofDIMACS c.toList).map Std.Sat.Literal.negate) hints.toList &&
      checkLRATAux ((id, Clause.ofDIMACS c.toList) :: db) rest
  | _, .addRat .. :: _ => false
  | db, .del ids :: rest => checkLRATAux (db.filter fun e => !ids.toList.contains e.1) rest

/-- The numbered clauses the checker starts from: clause `i` of `φ` has the number `i + 1`. -/
def CNF.lratDB (φ : CNF ℕ) : List (ℕ × Clause ℕ) :=
  φ.zipIdx.map fun e => (e.2 + 1, e.1)

/-- **The LRAT checker**: the clauses of `φ` are numbered from `1`, and the certificate must reach
an empty-clause step through RUP steps and deletions. -/
def CNF.checkLRAT (φ : CNF ℕ) (cert : Array LRAT.IntAction) : Bool :=
  checkLRATAux φ.lratDB cert.toList

/-- Unit propagation along hints reads the starting literals only through membership. -/
theorem CNF.propagateWith_congr (lookup : ℕ → Option (Clause ℕ)) :
    ∀ {t t' : List (Literal ℕ)}, (∀ l, l ∈ t ↔ l ∈ t') → ∀ hs : List ℕ,
      propagateWith lookup t hs = propagateWith lookup t' hs
  | _, _, _, [] => rfl
  | t, t', h, x :: hs => by
    simp only [propagateWith]
    cases lookup x with
    | none => rfl
    | some c =>
      dsimp only
      rw [Clause.residual_congr _ h]
      cases c.residual t' <;>
        first | rfl | exact CNF.propagateWith_congr lookup (fun _ => by simp [h]) hs

/-- Unit propagation along hints reads the starting literals only through membership. -/
theorem CNF.propagateHints_congr (db : List (ℕ × Clause ℕ)) {t t' : List (Literal ℕ)}
    (h : ∀ l, l ∈ t ↔ l ∈ t') (hs : List ℕ) : propagateHints db t hs = propagateHints db t' hs :=
  CNF.propagateWith_congr _ h hs

/-! ### Soundness -/

/-- If unit propagation along hints succeeds, no assignment satisfying every clause the lookup
returns makes the starting literals true. -/
theorem CNF.false_of_propagateWith {lookup : ℕ → Option (Clause ℕ)} {σ : ℕ → Bool}
    (hlookup : ∀ h c, lookup h = some c → c.eval σ = true) {trail : List (Literal ℕ)}
    (htrail : ∀ l ∈ trail, Literal.eval σ l = true) {hs : List ℕ}
    (h : propagateWith lookup trail hs = true) : False := by
  -- a literal of a looked-up clause holds, so it is not false under the trail
  have key {trail : List (Literal ℕ)} (htrail : ∀ l ∈ trail, Literal.eval σ l = true) {x c}
      (hc : lookup x = some c) :
      ∃ l' ∈ c, Literal.eval σ l' = true ∧ Std.Sat.Literal.negate l' ∉ trail := by
    obtain ⟨l', hl', hl'σ⟩ := (Clause.eval_eq_true_iff σ c).1 (hlookup x c hc)
    have hl'e : Literal.eval σ l' = true := by simp [Literal.eval, hl'σ]
    exact ⟨l', hl', hl'e, fun hm => by simpa [hl'e] using htrail _ hm⟩
  fun_induction propagateWith lookup trail hs with
  | case1 | case2 | case5 => simp at h -- no hints, unknown clause, non-unit residual
  | case3 trail x hs c hc hr => -- residual empty: conflict
    obtain ⟨l', hl', -, hl't⟩ := key htrail hc
    exact hl't (Clause.residual_eq_empty_iff.1 hr l' hl')
  | case4 trail x hs c hc l hr ih => -- residual unit l: propagate
    obtain ⟨l', hl', hl'e, hl't⟩ := key htrail hc
    -- the literal that holds is the propagated one
    obtain rfl : l' = l :=
      by_contra fun hne => hl't ((Clause.residual_eq_unit_iff.1 hr).2.2 l' hl' hne)
    exact ih (by simpa only [List.mem_cons, forall_eq_or_imp] using ⟨hl'e, htrail⟩) h

/-- If unit propagation along hints succeeds, no assignment satisfies the database and makes the
starting literals true. -/
theorem CNF.false_of_propagateHints {db : List (ℕ × Clause ℕ)} {σ : ℕ → Bool}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {trail : List (Literal ℕ)}
    (htrail : ∀ l ∈ trail, Literal.eval σ l = true) {hs : List ℕ}
    (h : propagateHints db trail hs = true) : False :=
  CNF.false_of_propagateWith (fun k c hc => by
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hc
    exact hdb (k, c) (by simp [hl])) htrail h

/-- **A RUP clause holds**: if unit propagation along hints from its negation succeeds, every
assignment satisfying the database satisfies it. -/
theorem CNF.eval_of_propagateHints {db : List (ℕ × Clause ℕ)} {σ : ℕ → Bool}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {c : Clause ℕ} {hs : List ℕ}
    (h : propagateHints db (c.map Std.Sat.Literal.negate) hs = true) : c.eval σ = true := by
  by_contra hne
  refine false_of_propagateHints hdb (fun l hl => ?_) h
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  rw [Literal.eval_negate]
  simpa [Literal.eval] using fun hσ => hne ((Clause.eval_eq_true_iff σ c).2 ⟨l₀, hl₀, hσ⟩)

/-- If the checker accepts on a database, no assignment satisfies the database. -/
theorem CNF.false_of_checkLRATAux {σ : ℕ → Bool} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, e.2.eval σ = true) {cert : List LRAT.IntAction}
    (h : checkLRATAux db cert = true) : False := by
  fun_induction checkLRATAux db cert with
  | case1 | case4 => simp at h -- no actions, addRat
  | case2 => exact false_of_propagateHints hdb (trail := []) (by simp) h -- addEmpty
  | case3 db id c hints rest ih => -- addRup
    rw [Bool.and_eq_true] at h
    exact ih (by simpa only [List.mem_cons, forall_eq_or_imp] using
      ⟨eval_of_propagateHints hdb h.1, hdb⟩) h.2
  | case5 db ids rest ih => exact ih (fun e he => hdb e (List.mem_filter.1 he).1) h -- del

/-- **A formula with an accepted LRAT certificate is unsatisfiable.** -/
theorem CNF.not_satisfiable_of_checkLRAT {φ : CNF ℕ} {cert : Array LRAT.IntAction}
    (h : φ.checkLRAT cert = true) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  refine false_of_checkLRATAux (σ := σ) ?_ h
  intro e he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (show e ∈ φ.zipIdx.map fun e => (e.2 + 1, e.1) from he)
  exact (CNF.eval_eq_true_iff σ φ).1 hσ _
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp))

end Cslib.Logic.PL
