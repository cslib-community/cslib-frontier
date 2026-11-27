/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DPLL

/-! # The DPLL search with an explicit trail

The solver `Cslib.Algorithms.Lean.DPLL.solve` searches recursively and builds a resolution
derivation as it returns. A machine without recursion runs the same search with an explicit
*trail*: the literals assumed so far, each marked as a first or a second branch
(`Cslib.Algorithms.Lean.DPLL.Trail`). One step (`Cslib.Algorithms.Lean.DPLL.Trail.step`) looks
at the partial assignment of the trail (`Cslib.Algorithms.Lean.DPLL.status`):

* if it satisfies every clause, the search ends with it;
* if it falsifies a clause, the search backtracks: it drops the second branches on top of the
  trail and turns the first branch below them into its second branch, or ends with `UNSAT` when
  there is none (`Cslib.Algorithms.Lean.DPLL.Trail.backtrack`);
* otherwise it pushes the literal the solver branches on
  (`Cslib.Algorithms.Lean.DPLL.nextLiteral`) as a first branch.

The run of the steps (`Cslib.Algorithms.Lean.DPLL.Trail.run`) explores the same tree as the
recursive search, except that it always tries the second branch of a variable, where the solver
skips it when the derivation of the first branch does not mention the variable. In that case the
second branch has no model either, since the derived clause is falsified by the partial assignment
(`Cslib.Algorithms.Lean.DPLL.dfs_eq_none_of_derivation`); so both find the same first model
(`Cslib.Algorithms.Lean.DPLL.solve_eq_sat_iff_dfs`). The run takes at most `2 ^ (N + 1)` steps,
where `N` is the number of distinct variables (`Cslib.Algorithms.Lean.DPLL.Trail.run_answer`):
one per node of the search tree.

## Main definitions

* `Cslib.Algorithms.Lean.DPLL.status`, `Cslib.Algorithms.Lean.DPLL.nextLiteral`: what the search
  does at a partial assignment.
* `Cslib.Algorithms.Lean.DPLL.dfs`: the search without skipping second branches.
* `Cslib.Algorithms.Lean.DPLL.Trail.step`, `Cslib.Algorithms.Lean.DPLL.Trail.run`: the search with
  an explicit trail.

## Main results

* `Cslib.Algorithms.Lean.DPLL.solve_eq_sat_iff_dfs`,
  `Cslib.Algorithms.Lean.DPLL.isSat_solve_eq_isSome_dfs`:
  the search without skipping finds the solver's answer and model.
* `Cslib.Algorithms.Lean.DPLL.Trail.run_answer`: the trail run reaches that answer within
  `2 ^ (N + 1)` steps.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

/-! ### The status of a partial assignment -/

/-- Whether a partial assignment assigns the variable `x`. -/
def Assigned (π : List (Literal ℕ)) (x : ℕ) : Bool :=
  π.contains (x, true) || π.contains (x, false)

/-- The literal the solver branches on at `π`: the literal of a unit clause, or else the variable
of the first literal occurrence that `π` leaves open, `true` first. -/
def nextLiteral (φ : CNF ℕ) (π : List (Literal ℕ)) : Literal ℕ :=
  match unitLiteral? φ π with
  | some l => l
  | none => ((φ.vars.find? fun x => !Assigned π x).getD 0, true)

/-- What the search does at a partial assignment. -/
inductive Status : Type
  /-- A clause is falsified. -/
  | conflict
  /-- Every clause has a literal that holds. -/
  | sat
  /-- Branch on this literal, first assuming it true. -/
  | branch (l : Literal ℕ)
  deriving DecidableEq, Repr

/-- The status of the partial assignment `π`, tested in the order of the solver: a falsified
clause, then satisfaction, then branching. -/
def status (φ : CNF ℕ) (π : List (Literal ℕ)) : Status :=
  if (φ.find? (Falsifies π)).isSome then .conflict
  else if φ.all (fun c => c.any (Holds π)) then .sat
  else .branch (nextLiteral φ π)

/-- No variable is assumed both true and false. -/
def Consistent (π : List (Literal ℕ)) : Prop := ∀ x, ¬ ((x, true) ∈ π ∧ (x, false) ∈ π)

theorem assigned_eq_false_iff {π : List (Literal ℕ)} {x : ℕ} :
    Assigned π x = false ↔ (x, true) ∉ π ∧ (x, false) ∉ π := by
  simp [Assigned]

theorem assigned_cons (l : Literal ℕ) (π : List (Literal ℕ)) (x : ℕ) :
    Assigned (l :: π) x = (Assigned π x || x == l.1) := by
  obtain ⟨v, b⟩ := l
  by_cases hx : x = v
  · subst hx; cases b <;> simp [Assigned]
  · simp [Assigned, hx]

theorem assigned_negate_cons (l : Literal ℕ) (π : List (Literal ℕ)) (x : ℕ) :
    Assigned (l.negate :: π) x = Assigned (l :: π) x := by
  rw [assigned_cons, assigned_cons]; rfl

/-- Assuming a literal on an unassigned variable keeps a partial assignment consistent. -/
theorem Consistent.cons {π : List (Literal ℕ)} (hπ : Consistent π) {l : Literal ℕ}
    (hl : Assigned π l.1 = false) : Consistent (l :: π) := by
  obtain ⟨v, b⟩ := l
  rw [assigned_eq_false_iff] at hl
  intro x
  have := hπ x
  simp only [List.mem_cons]
  grind

theorem unitLiteral?_spec {φ : CNF ℕ} {π : List (Literal ℕ)} {l : Literal ℕ}
    (h : unitLiteral? φ π = some l) :
    l.1 ∈ φ.vars ∧ Std.Sat.Literal.negate l ∉ π ∧ l ∉ π := by
  obtain ⟨c, hc, hcl⟩ := List.exists_of_findSome?_eq_some h
  split at hcl
  next l' hu =>
    split at hcl
    · cases hcl
    · cases hcl
      obtain ⟨hmc, hmn⟩ := List.mem_filter.1
        (Clause.unit?_eq_some_iff.1 hu ▸ List.mem_singleton_self l)
      exact ⟨CNF.mem_vars.2 ⟨c, hc, l.2, hmc⟩, by simpa using hmn,
        by simpa using ‹¬π.contains l = true›⟩
  next => cases hcl

/-- Every variable of the formula is assigned when no variable of `φ.vars` is open. -/
theorem forall_assigned_of_find?_eq_none {φ : CNF ℕ} {π : List (Literal ℕ)}
    (h : φ.vars.find? (fun x => !Assigned π x) = none) :
    ∀ x ∈ φ.vars, (x, true) ∈ π ∨ (x, false) ∈ π := by
  intro x hx
  exact Decidable.or_iff_not_imp_left.2 (by simpa [Assigned] using List.find?_eq_none.1 h x hx)

/-- **The branch variable is open.** -/
theorem assigned_of_status_eq_branch {φ : CNF ℕ} {π : List (Literal ℕ)} {l : Literal ℕ}
    (h : status φ π = .branch l) : l.1 ∈ φ.vars ∧ Assigned π l.1 = false := by
  unfold status at h
  split_ifs at h with hf hs
  cases h
  unfold nextLiteral
  split
  · rename_i l hl
    obtain ⟨hv, hn, hp⟩ := unitLiteral?_spec hl
    refine ⟨hv, assigned_eq_false_iff.2 ?_⟩
    obtain ⟨v, b⟩ := l
    cases b <;> simp_all [Std.Sat.Literal.negate]
  · cases hfind : φ.vars.find? (fun x => !Assigned π x) with
    | none =>
      exact absurd (all_any_holds (by simpa using hf)
        (forall_assigned_of_find?_eq_none hfind)) hs
    | some x =>
      exact ⟨List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩

/-! ### The search without skipping -/

/-- **The search without skipping** from `π` with `fuel` levels left: the first partial assignment
satisfying every clause, trying both branches of every variable in order. -/
def dfs (φ : CNF ℕ) : ℕ → List (Literal ℕ) → Option (List (Literal ℕ))
  | 0, π =>
    match status φ π with
    | .sat => some π
    | _ => none
  | fuel + 1, π =>
    match status φ π with
    | .conflict => none
    | .sat => some π
    | .branch l => (dfs φ fuel (l :: π)).or (dfs φ fuel (l.negate :: π))

theorem status_eq_sat_iff {φ : CNF ℕ} {π : List (Literal ℕ)} :
    status φ π = .sat ↔ φ.find? (Falsifies π) = none ∧ φ.all (fun c => c.any (Holds π)) = true := by
  unfold status
  split_ifs <;> simp_all

/-- A partial assignment falsifying a clause has the status `conflict`. -/
theorem status_eq_conflict {φ : CNF ℕ} {π : List (Literal ℕ)} (h : φ.any (Falsifies π) = true) :
    status φ π = .conflict := by
  unfold status; rw [List.isSome_find?, h]; rfl

/-- A partial assignment of status `conflict` falsifies a clause. -/
theorem any_falsifies_of_status_eq_conflict {φ : CNF ℕ} {π : List (Literal ℕ)}
    (h : status φ π = .conflict) : φ.any (Falsifies π) = true := by
  unfold status at h
  split_ifs at h with hs
  simp_all [List.isSome_find?]

/-- A partial assignment falsifying no clause, with a true literal in every clause, has the status
`sat`. -/
theorem status_eq_sat {φ : CNF ℕ} {π : List (Literal ℕ)} (hc : φ.any (Falsifies π) = false)
    (ha : φ.all (fun c => c.any (Holds π)) = true) : status φ π = .sat := by
  unfold status; rw [List.isSome_find?, hc]; simp only [Bool.false_eq_true, ↓reduceIte, ha]

/-- Otherwise the status branches on `nextLiteral`. -/
theorem status_eq_branch {φ : CNF ℕ} {π : List (Literal ℕ)} (hc : φ.any (Falsifies π) = false)
    (ha : φ.all (fun c => c.any (Holds π)) = false) :
    status φ π = .branch (nextLiteral φ π) := by
  unfold status; rw [List.isSome_find?, hc]; simp only [Bool.false_eq_true, ↓reduceIte, ha]

/-- A model found by the search extends the partial assignment, stays consistent, and satisfies
every clause. -/
theorem dfs_eq_some {φ : CNF ℕ} : (fuel : ℕ) → {π π' : List (Literal ℕ)} → Consistent π →
    dfs φ fuel π = some π' →
      (∀ l ∈ π, l ∈ π') ∧ Consistent π' ∧ φ.all (fun c => c.any (Holds π')) = true
  | 0, π, π', hπ, h => by
    unfold dfs at h
    split at h
    · rename_i hs; cases h; exact ⟨fun _ h => h, hπ, (status_eq_sat_iff.1 hs).2⟩
    · cases h
  | fuel + 1, π, π', hπ, h => by
    unfold dfs at h
    split at h
    · cases h
    · rename_i hs; cases h; exact ⟨fun _ h => h, hπ, (status_eq_sat_iff.1 hs).2⟩
    · rename_i l hs
      have hl := (assigned_of_status_eq_branch hs).2
      rcases Option.or_eq_some_iff.1 h with h₁ | ⟨-, h₂⟩
      · obtain ⟨hsub, hc, hall⟩ := dfs_eq_some fuel (hπ.cons hl) h₁
        exact ⟨fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl'), hc, hall⟩
      · obtain ⟨hsub, hc, hall⟩ := dfs_eq_some fuel (hπ.cons (l := l.negate) hl) h₂
        exact ⟨fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl'), hc, hall⟩

/-- **No model below a falsified derived clause**: if `π` falsifies a clause derived from `φ`, the
search from `π` finds no model. -/
theorem dfs_eq_none_of_derivation {φ : CNF ℕ} {π : List (Literal ℕ)} (hπ : Consistent π)
    {c : Clause ℕ} (d : φ.Derivation c) (hc : ∀ l ∈ c, l.negate ∈ π) (fuel : ℕ) :
    dfs φ fuel π = none := by
  cases h : dfs φ fuel π with
  | none => rfl
  | some π' =>
    obtain ⟨hsub, hcons, hall⟩ := dfs_eq_some fuel hπ h
    have hev := d.derives.eval_eq_true (eval_assignment hall)
    obtain ⟨⟨x, b⟩, hl, hev⟩ := List.any_eq_true.1 hev
    have hneg := hsub _ (hc _ hl)
    cases b <;> simp only [Std.Sat.Literal.negate, Bool.not_false, Bool.not_true, Literal.eval,
      assignment] at hneg hev
    · exact absurd hneg (by simpa using hev)
    · exact (hcons x ⟨by simpa using hev, hneg⟩).elim

/-! ### The search without skipping finds the solver's answer -/

/-- The open variables of `π` in the order of their first occurrences in `φ.vars`. -/
def openVars (φ : CNF ℕ) (π : List (Literal ℕ)) : List ℕ :=
  φ.vars.eraseDups.filter fun x => !Assigned π x

theorem openVars_cons (φ : CNF ℕ) (π : List (Literal ℕ)) (l : Literal ℕ) :
    openVars φ (l :: π) = (openVars φ π).erase l.1 := by
  simp only [openVars]
  rw [List.Nodup.erase_eq_filter ((List.nodup_eraseDups _).filter _), List.filter_filter]
  congr 1
  funext x
  rw [assigned_cons]
  by_cases hx : x = l.1 <;> simp [hx, bne, Bool.and_comm]

theorem mem_openVars {φ : CNF ℕ} {π : List (Literal ℕ)} {x : ℕ} :
    x ∈ openVars φ π ↔ x ∈ φ.vars ∧ Assigned π x = false := by
  simp [openVars, List.mem_eraseDups]

/-- At a branching on `l`, a bound `fuel` on the open variables is positive, and the partial
assignments with a literal on the variable of `l` added have fewer. -/
theorem length_openVars_cons_le {φ : CNF ℕ} {π : List (Literal ℕ)} {l : Literal ℕ} {fuel : ℕ}
    (hs : status φ π = .branch l) (hf : (openVars φ π).length ≤ fuel) :
    ∃ f, fuel = f + 1 ∧ ∀ l' : Literal ℕ, l'.1 = l.1 → (openVars φ (l' :: π)).length ≤ f := by
  obtain ⟨hv, ha⟩ := assigned_of_status_eq_branch hs
  have hmem : l.1 ∈ openVars φ π := mem_openVars.2 ⟨hv, ha⟩
  have := List.length_pos_of_mem hmem
  refine ⟨fuel - 1, by omega, fun l' hl' => ?_⟩
  rw [openVars_cons, hl', List.length_erase_of_mem hmem]
  omega

/-- The literal of the solver's branch is `nextLiteral` when the open variables are listed in the
order of their first occurrences. -/
theorem branchLiteral_eq {φ : CNF ℕ} {π : List (Literal ℕ)} {x : ℕ} {xs : List ℕ}
    (hvs : x :: xs = openVars φ π) : (branchLiteral φ π x xs).val = nextLiteral φ π := by
  unfold branchLiteral nextLiteral
  split
  next l hl =>
    obtain ⟨hv, hn, hp⟩ := unitLiteral?_spec hl
    have hmem : l.1 ∈ x :: xs := hvs ▸ mem_openVars.2 ⟨hv, assigned_eq_false_iff.2 <| by
      rcases l with ⟨v, _ | _⟩ <;> simp_all [Std.Sat.Literal.negate]⟩
    simp [hmem, hl]
  next hl =>
    have hhead : (openVars φ π).head? = some x := hvs ▸ rfl
    rw [openVars, List.head?_filter, List.find?_eraseDups] at hhead
    simp [hhead, hl]

/-- The model of an outcome, if it is one. -/
def Outcome.model? {φ : CNF ℕ} {π : List (Literal ℕ)} : Outcome φ π → Option (ℕ → Bool)
  | .sat σ _ => some σ
  | .unsat .. => none

theorem model?_resolveBranches {φ : CNF ℕ} {π : List (Literal ℕ)} (v : ℕ) (b : Bool)
    {c₁ c₂ : Clause ℕ} (d₁ : φ.Derivation c₁) (hc₁ : (v, !b) ∈ c₁)
    (h₁ : ∀ l ∈ c₁, l.negate ∈ (v, b) :: π) (d₂ : φ.Derivation c₂) (hc₂ : (v, b) ∈ c₂)
    (h₂ : ∀ l ∈ c₂, l.negate ∈ (v, !b) :: π) :
    (resolveBranches v b d₁ hc₁ h₁ d₂ hc₂ h₂).model? = none := by
  cases b <;> rfl

/-- **The solver's search and the search without skipping agree**: from the same partial
assignment, the solver's search returns a model exactly when the search without skipping finds
one, and then it is the model of the partial assignment found. -/
theorem model?_search (φ : CNF ℕ) : (fuel : ℕ) → (π : List (Literal ℕ)) → (vs : List ℕ) →
    (hvs : OpenVars φ π vs) → (hfuel : vs.length ≤ fuel) → vs = openVars φ π → Consistent π →
    (search φ fuel π vs hvs hfuel).model? = (dfs φ fuel π).map assignment := by
  intro fuel
  induction fuel with
  | zero =>
    intro π vs hvs hfuel hvo hπ
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [search]
    split
    · rename_i c hfind
      simp [Outcome.model?, dfs, status, hfind]
    · rename_i hfind
      split
      · rename_i hsat
        simp [Outcome.model?, dfs, status_eq_sat_iff.2 ⟨hfind, hsat⟩]
      · exact absurd (all_any_holds hfind fun x hx => (hvs.covers x hx).resolve_left
          List.not_mem_nil) ‹_›
  | succ fuel ih =>
    intro π vs hvs hfuel hvo hπ
    rw [search]
    split
    · rename_i c hfind
      simp [Outcome.model?, dfs, status, hfind]
    · rename_i hfind
      split
      · rename_i hsat
        simp [Outcome.model?, dfs, status_eq_sat_iff.2 ⟨hfind, hsat⟩]
      · rename_i hsat
        split
        · exact absurd (all_any_holds hfind fun x hx =>
            (‹OpenVars φ π []›.covers x hx).resolve_left List.not_mem_nil) hsat
        · omega
        · rename_i x xs fuel' hvs' hlen' hfe _
          obtain rfl : fuel = fuel' := by omega
          have hst : status φ π = .branch (nextLiteral φ π) := by simp [status, hfind, hsat]
          split
          rename_i v b hv hbr
          have hbl : (v, b) = nextLiteral φ π := by simpa [hbr] using branchLiteral_eq hvo
          have hdfs : dfs φ (fuel + 1) π =
              (dfs φ fuel ((v, b) :: π)).or (dfs φ fuel ((v, !b) :: π)) := by
            rw [dfs, hst, ← hbl]; rfl
          have hun : Assigned π v = false := by
            simpa [← hbl] using (assigned_of_status_eq_branch hst).2
          have hl : ((x :: xs).erase v).length ≤ fuel := by
            rw [List.length_erase_of_mem hv]; simp only [List.length_cons] at hlen' ⊢; omega
          have ih₁ := ih _ _ (hvs'.erase v b) hl (by rw [hvo, openVars_cons]) (hπ.cons hun)
          have hc₂ : Consistent ((v, !b) :: π) := hπ.cons (l := (v, !b)) hun
          have ih₂ := ih _ _ (hvs'.erase v !b) hl (by rw [hvo, openVars_cons]) hc₂
          rw [hdfs]
          dsimp only
          split
          · rename_i σ h hs₁
            rw [hs₁] at ih₁
            cases hd : dfs φ fuel ((v, b) :: π) <;>
              simp only [hd, Outcome.model?, Option.map_some, Option.map_none, Option.some_or,
                reduceCtorEq] at ih₁ ⊢
            exact ih₁
          · rename_i c₁ d₁ h₁ hs₁
            rw [hs₁] at ih₁
            have hd₁ : dfs φ fuel ((v, b) :: π) = none :=
              Option.eq_none_iff_forall_ne_some.2 fun π' hd => by simp [hd, Outcome.model?] at ih₁
            rw [hd₁, Option.none_or]
            split
            · split <;> rename_i hs₂ <;> rw [hs₂] at ih₂
              · exact ih₂
              · rw [Outcome.model?] at ih₂
                split
                · rwa [model?_resolveBranches]
                · exact ih₂
            · rename_i hn
              rw [dfs_eq_none_of_derivation hc₂ d₁ (fun l hl => List.mem_cons_of_mem _
                (Literal.negate_mem_of_mem_cons (h₁ l hl) (by rintro rfl; exact hn (by
                  simpa [Std.Sat.Literal.negate] using hl)))) fuel]
              rfl

/-- The number of distinct variables of `φ`: the depth of the search tree. -/
def depth (φ : CNF ℕ) : ℕ := φ.vars.eraseDups.length

theorem openVars_nil (φ : CNF ℕ) : openVars φ [] = φ.vars.eraseDups := by
  simp [openVars, Assigned]

theorem model?_dpll (φ : CNF ℕ) : (dpll φ).model? = (dfs φ (depth φ) []).map assignment :=
  model?_search φ _ _ _ _ _ (openVars_nil φ).symm fun _ h => by simp at h

/-- **The search without skipping finds the solver's model.** -/
theorem solve_eq_sat_iff_dfs {φ : CNF ℕ} {σ : ℕ → Bool} :
    solve φ = .sat σ ↔ ∃ π, dfs φ (depth φ) [] = some π ∧ σ = assignment π := by
  have h := model?_dpll φ
  unfold solve
  split <;> rename_i hd <;> rw [hd] at h
  · cases hdfs : dfs φ (depth φ) [] <;> grind [Outcome.model?]
  · simp_all [Outcome.model?, Option.none_eq_map_iff]

/-- **The search without skipping decides satisfiability as the solver does.** -/
theorem isSat_solve_eq_isSome_dfs (φ : CNF ℕ) :
    (solve φ).isSat = (dfs φ (depth φ) []).isSome := by
  cases hs : solve φ with
  | sat σ =>
    obtain ⟨π, hπ, -⟩ := solve_eq_sat_iff_dfs.1 hs
    simp [Result.isSat, hπ]
  | unsat cert =>
    cases hd : dfs φ (depth φ) [] with
    | none => rfl
    | some π => exact absurd (solve_eq_sat_iff_dfs.2 ⟨π, hd, rfl⟩) (by simp [hs])

/-! ### The search with an explicit trail -/

/-- An entry of a trail: a literal assumed, and whether it is the second branch of its
variable. -/
structure TrailEntry where
  /-- The literal assumed. -/
  lit : Literal ℕ
  /-- Whether this is the second branch of its variable, after the first was refuted. -/
  isSecond : Bool
  deriving DecidableEq, Repr

/-- A trail: its entries, last first. -/
abbrev Trail := List TrailEntry

namespace Trail

/-- The partial assignment of a trail. -/
def lits (t : Trail) : List (Literal ℕ) := t.map TrailEntry.lit

@[simp] theorem lits_nil : lits [] = [] := rfl

@[simp] theorem lits_cons (l : Literal ℕ) (b : Bool) (t : Trail) :
    lits (⟨l, b⟩ :: t) = l :: lits t := rfl

/-- **Backtracking**: drop the second branches on top, and turn the first branch below them into
its second branch; `none` when every branch is a second branch. -/
def backtrack : Trail → Option Trail
  | [] => none
  | ⟨_, true⟩ :: t => backtrack t
  | ⟨l, false⟩ :: t => some (⟨l.negate, true⟩ :: t)

/-- The end of a run: a partial assignment satisfying every clause, or none. -/
inductive Answer : Type
  /-- The partial assignment of the trail satisfies every clause. -/
  | sat (π : List (Literal ℕ))
  /-- No partial assignment satisfies every clause. -/
  | unsat
  deriving DecidableEq, Repr

/-- **One step** of the search: end at a satisfying partial assignment, backtrack at a falsified
clause, and otherwise push the branch literal. -/
def step (φ : CNF ℕ) (t : Trail) : Answer ⊕ Trail :=
  match status φ (lits t) with
  | .sat => .inl (.sat (lits t))
  | .branch l => .inr (⟨l, false⟩ :: t)
  | .conflict =>
    match backtrack t with
    | none => .inl .unsat
    | some t' => .inr t'

theorem step_of_status_eq_conflict {φ : CNF ℕ} {t : Trail} (h : status φ (lits t) = .conflict) :
    step φ t = match backtrack t with
      | none => .inl .unsat
      | some t' => .inr t' := by
  unfold step; rw [h]

theorem step_of_status_eq_sat {φ : CNF ℕ} {t : Trail} (h : status φ (lits t) = .sat) :
    step φ t = .inl (.sat (lits t)) := by
  unfold step; rw [h]

theorem step_of_status_eq_branch {φ : CNF ℕ} {t : Trail} {l : Literal ℕ}
    (h : status φ (lits t) = .branch l) : step φ t = .inr (⟨l, false⟩ :: t) := by
  unfold step; rw [h]

/-- **The run** of at most `k` steps from the trail `t`: its answer, or `none` if the steps run
out. -/
def run (φ : CNF ℕ) : ℕ → Trail → Option Answer
  | 0, _ => none
  | k + 1, t =>
    match step φ t with
    | .inl a => some a
    | .inr t' => run φ k t'

/-- The number of nodes of the search tree from `π` with `fuel` levels. -/
def nodes (φ : CNF ℕ) : ℕ → List (Literal ℕ) → ℕ
  | 0, _ => 1
  | fuel + 1, π =>
    match status φ π with
    | .branch l => nodes φ fuel (l :: π) + nodes φ fuel (l.negate :: π) + 1
    | _ => 1

theorem nodes_lt (φ : CNF ℕ) : (fuel : ℕ) → (π : List (Literal ℕ)) →
    nodes φ fuel π < 2 ^ (fuel + 1)
  | 0, _ => by simp [nodes]
  | fuel + 1, π => by
    have h₁ := nodes_lt φ fuel
    unfold nodes
    split
    · rename_i l _
      have := h₁ (l :: π); have := h₁ (l.negate :: π)
      rw [Nat.pow_succ]; omega
    · exact Nat.one_lt_two_pow (by omega)

/-- What a run does after the subtree at the top of the trail: the model found in it, or else
the backtracked trail continuing with `k` steps. -/
def after (φ : CNF ℕ) (k : ℕ) (t : Trail) : Option (List (Literal ℕ)) → Option Answer
  | some π => some (.sat π)
  | none =>
    match backtrack t with
    | none => some .unsat
    | some t' => run φ k t'

theorem backtrack_cons_false (l : Literal ℕ) (t : Trail) :
    backtrack (⟨l, false⟩ :: t) = some (⟨l.negate, true⟩ :: t) := rfl

theorem backtrack_cons_true (l : Literal ℕ) (t : Trail) :
    backtrack (⟨l, true⟩ :: t) = backtrack t := rfl

/-- **The run explores the subtree at the top of the trail** in `nodes` steps: it ends with the
model of the subtree if there is one, and otherwise continues by backtracking. -/
theorem run_add_nodes (φ : CNF ℕ) : (fuel : ℕ) → (t : Trail) → (k : ℕ) →
    (openVars φ (lits t)).length ≤ fuel →
    run φ (k + nodes φ fuel (lits t)) t = after φ k t (dfs φ fuel (lits t))
  | fuel, t, k, hf => by
    cases hs : status φ (lits t) with
    | sat =>
      cases fuel <;> simp [nodes, dfs, hs, run, step, after]
    | conflict =>
      cases fuel <;> cases hb : backtrack t <;> simp [nodes, dfs, hs, run, step, after, hb]
    | branch l =>
      obtain ⟨fuel, rfl, hlen⟩ := length_openVars_cons_le hs hf
      have ih₁ := run_add_nodes φ fuel (⟨l, false⟩ :: t)
        (k + nodes φ fuel (l.negate :: lits t)) (hlen l rfl)
      have ih₂ := run_add_nodes φ fuel (⟨l.negate, true⟩ :: t) k (hlen l.negate rfl)
      simp only [lits_cons] at ih₁ ih₂
      have hn : k + nodes φ (fuel + 1) (lits t) =
          (k + nodes φ fuel (l.negate :: lits t) + nodes φ fuel (l :: lits t)) + 1 := by
        simp only [nodes, hs]; omega
      simp only [hn, run, step, dfs, hs, ih₁]
      cases dfs φ fuel (l :: lits t) with
      | some π => rfl
      | none =>
        simp only [after, backtrack_cons_false, Option.none_or]
        rw [ih₂]
        cases dfs φ fuel (l.negate :: lits t) with
        | some π => rfl
        | none => simp only [after, backtrack_cons_true]
  termination_by fuel => fuel

/-- The answer of the search without skipping. -/
def answer (φ : CNF ℕ) : Answer :=
  match dfs φ (depth φ) [] with
  | some π => .sat π
  | none => .unsat

/-- **The trail run finds the answer** within `2 ^ (N + 1)` steps, where `N` is the number of
distinct variables of `φ`. -/
theorem run_answer (φ : CNF ℕ) :
    ∃ k ≤ 2 ^ (depth φ + 1), run φ k [] = some (answer φ) := by
  have h := run_add_nodes φ (depth φ) [] 0 (by simp [lits, openVars_nil, depth])
  rw [Nat.zero_add, lits_nil] at h
  refine ⟨nodes φ (depth φ) [], (nodes_lt φ (depth φ) []).le, ?_⟩
  rw [h, answer]
  cases dfs φ (depth φ) [] <;> rfl

end Trail

end Cslib.Algorithms.Lean.DPLL
