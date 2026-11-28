/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Exec

/-! # Minimizing learned clauses

MiniSat's minimization of learned clauses. In its recursive mode (`ccmin_mode = 2`, Sörensson and
Biere), a literal `y` of a learned clause, false below the backjump point, is *redundant* when the
literal `¬y` of the trail is implied and every other literal of its reason is either in the learned
clause or, recursively, redundant (`Cslib.Algorithms.Lean.CDCL.derived`). In its basic mode
(`ccmin_mode = 1`, MiniSat 1.13), the recursion goes only into the literals implied without any
decision, which MiniSat's test of level `0` admits. Removing every redundant literal
gives a clause that follows from the rest by unit propagation: assuming its negation, the reasons
of the derived literals, oldest first, propagate the negations of the removed literals, and then
the learned clause is false.

So the minimized clause is learned with the hints of the learned clause after those reasons
(`Cslib.Algorithms.Lean.CDCL.Learned.minimize`), still one RUP step, and the hints are proved to
refute it (`Cslib.Algorithms.Lean.CDCL.Learned.propagateHints_minimized`), with no check at run
time. The proof rests on the soundness of the memo of the search: a variable recorded as derived
has a reason on the trail whose other literals are on variables of the learned clause or recorded
as derived. The search records a variable as not derived while it searches its reason, so a
recorded result is never changed. Reasons point down the trail, so propagating the derived
literals oldest first reaches each reason with its other literals false. The minimized clause is a
subset of the learned one containing its asserting literal once, at its head, so it is again a
learned clause.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.derived`: whether a literal of the trail follows from the learned
  clause's other literals.
* `Cslib.Algorithms.Lean.CDCL.Learned.minimize`: the minimized learned clause.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Learned.propagateHints_minimized`: the minimized clause, with the
  reasons of the derived literals, oldest first, before the hints of the learned clause, is a RUP
  clause.

## References

* [N. Sörensson, A. Biere, *Minimizing Learned Clauses*][SorenssonBiere2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

variable {φ : CNF ℕ}

/-- The number of the reason of each implied variable of the trail `T`, indexed by variable, for
the variables below `n`. -/
def XTrail.reasons (T : XTrail) (n : ℕ) : Array (Option ℕ) :=
  T.foldl (fun a x => match x with
    | .implied l r => a.setIfInBounds l.1 (some r)
    | .decision _ => a) (Array.replicate n none)

/-- **Whether the literal of the trail on `v` is derived** from the literals of the learned clause,
whose variables are marked by `inC`: its reason, looked up in `log` through `reason`, has every
other literal either on a variable of the learned clause or, on a variable where `deep` allows the
recursion, derived. Decisions and literals without a reason are not derived. The results are
memoized in `memo`, where `v` counts as not derived while its reason is searched; `fuel` bounds the
depth of the search, and running out of it counts as not derived. -/
def derived (log : LRATLog φ) (reason : Array (Option ℕ)) (inC : Array Bool) (deep : ℕ → Bool) :
    (fuel : ℕ) → (memo : Assign) → (v : ℕ) → Bool × Assign
  | 0, memo, _ => (false, memo)
  | fuel + 1, memo, v =>
    match memo.value v with
    | some b => (b, memo)
    | none =>
      match (reason.getD v none).bind log.clause? with
      | none => (false, memo.set v (some false))
      | some R =>
        let r := R.foldl (fun (acc : Bool × Assign) z =>
          if !acc.1 then acc
          else if z.1 == v || inC.getD z.1 false then acc
          else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
          else (false, acc.2)) (true, memo.set v (some false))
        (r.1, r.2.set v (some r.1))

/-- The literals of the clause `C`, other than `lit`, whose negations are derived, and the
memoized search. -/
def redundant (log : LRATLog φ) (reason : Array (Option ℕ)) (inC : Array Bool) (deep : ℕ → Bool)
    (fuel : ℕ) (lit : Literal ℕ) (C : Clause ℕ) (memo : Assign) : List (Literal ℕ) × Assign :=
  C.foldl (fun (acc : List (Literal ℕ) × Assign) y =>
    if y == lit then acc
    else
      let r := derived log reason inC deep fuel acc.2 y.1
      (if r.1 then y :: acc.1 else acc.1, r.2)) ([], memo)

/-- The reasons of the derived literals of the trail `T`, oldest first: the hints that propagate
them. -/
def derivedHints (T : XTrail) (memo : Assign) : List ℕ :=
  T.reverse.filterMap fun x => match x with
    | .implied l r => if memo.value l.1 == some true then some r else none
    | .decision _ => none

/-- `derivedHints` in one pass over the trail, newest first, without reversing it. -/
private theorem foldl_derivedHints (memo : Assign) : ∀ (T : XTrail) (acc : List ℕ),
    T.foldl (fun acc x => match x with
      | .implied l r => if memo.value l.1 == some true then r :: acc else acc
      | .decision _ => acc) acc = derivedHints T memo ++ acc
  | [], _ => by simp [derivedHints]
  | x :: T, acc => by
    rw [List.foldl_cons, foldl_derivedHints memo T]
    cases x with
    | decision d => simp [derivedHints]
    | implied l r =>
      by_cases h : memo.value l.1 = some true <;> simp [derivedHints, h]

/-- The array marking the variables of the clause `C`, below `n`. -/
def clauseVars (C : Clause ℕ) (n : ℕ) : Array Bool :=
  C.foldl (fun a y => a.setIfInBounds y.1 true) (Array.replicate n false)

/-- **The redundant literals** of the learned clause `C` with the asserting literal `lit`, whose
false literals are on the trail `T`, and the memoized search: recursively if `recursive`, and
otherwise following only the reasons of the literals implied at the root. The arrays have `n`
slots, and the search `n + 1` levels of fuel: with `n` beyond every variable of `T`, whose
variables are distinct, no reason is missed and the fuel never runs out, and in any case the
result is sound. -/
def minimizeRedundant (log : LRATLog φ) (T : XTrail) (C : Clause ℕ) (lit : Literal ℕ)
    (recursive : Bool) (n : ℕ) : List (Literal ℕ) × Assign :=
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let root := Assign.ofTrail (XTrail.trail (XTrail.root T))
      fun v => root.assigned v
  redundant log (T.reasons n) (clauseVars C n) deep (n + 1) lit C ⟨Array.replicate n 0⟩

/-! ### The minimized clause is a RUP clause -/

/-- The entries of the reason array are reasons of the trail. -/
private theorem XTrail.mem_of_reasons {T : XTrail} {n v r : ℕ}
    (h : (T.reasons n).getD v none = some r) :
    ∃ b, XEntry.implied (v, b) r ∈ T := by
  suffices ∀ (T : XTrail) (a : Array (Option ℕ)),
      (T.foldl (fun a x => match x with
        | .implied l r => a.setIfInBounds l.1 (some r)
        | .decision _ => a) a).getD v none = some r →
        a.getD v none = some r ∨ ∃ b, XEntry.implied (v, b) r ∈ T by
    rcases this T _ h with h | h
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
      split at h <;> simp at h
    · exact h
  intro T
  induction T with
  | nil => exact fun a h => .inl h
  | cons x T ih =>
    intro a h
    rcases ih _ h with h' | ⟨b, hb⟩
    · cases x with
      | decision d => exact .inl h'
      | implied l r' =>
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h'
        split at h'
        · rename_i hv
          split at h'
          · obtain rfl := hv
            obtain rfl : r' = r := by simpa using h'
            exact .inr ⟨l.2, List.mem_cons_self⟩
          · simp at h'
        · exact .inl (by rw [Array.getD_eq_getD_getElem?]; exact h')
    · exact .inr ⟨b, List.mem_cons_of_mem _ hb⟩

/-- The marked variables are those of the clause. -/
private theorem mem_of_clauseVars {C : Clause ℕ} {n w : ℕ}
    (h : (clauseVars C n).getD w false = true) :
    ∃ y ∈ C, y.1 = w := by
  suffices ∀ (C : Clause ℕ) (a : Array Bool),
      (C.foldl (fun a y => a.setIfInBounds y.1 true) a).getD w false = true →
        a.getD w false = true ∨ ∃ y ∈ C, y.1 = w by
    rcases this C _ h with h | h
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
      split at h <;> simp at h
    · exact h
  intro C
  induction C with
  | nil => exact fun a h => .inl h
  | cons y C ih =>
    intro a h
    rcases ih _ h with h' | ⟨z, hz, hzw⟩
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h'
      split at h'
      · rename_i hv
        exact .inr ⟨y, List.mem_cons_self, hv⟩
      · exact .inl (by rw [Array.getD_eq_getD_getElem?]; exact h')
    · exact .inr ⟨z, List.mem_cons_of_mem _ hz, hzw⟩

/-- The memo is sound: every variable recorded as derived has a reason whose other literals are on
variables of the learned clause or recorded as derived. -/
private def MemoSound (log : LRATLog φ) (reason : Array (Option ℕ)) (inC : Array Bool)
    (memo : Assign) : Prop :=
  ∀ w, memo.value w = some true → ∃ r R, reason.getD w none = some r ∧ log.clause? r = some R ∧
    ∀ z ∈ R, z.1 ≠ w → inC.getD z.1 false = true ∨ memo.value z.1 = some true

/-- The search only fills entries of the memo. -/
private def Keeps (memo memo' : Assign) : Prop :=
  ∀ w, memo.value w ≠ none → memo'.value w = memo.value w

private theorem Keeps.trans {a b c : Assign} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  fun w hw => (h₂ w (by rw [h₁ w hw]; exact hw)).trans (h₁ w hw)

private theorem Keeps.true {a b : Assign} (h : Keeps a b) {w : ℕ} (hw : a.value w = some true) :
    b.value w = some true := (h w (by simp [hw])).trans hw

/-- Recording a variable without a value as not derived keeps the memo sound. -/
private theorem MemoSound.set_false {log : LRATLog φ} {reason : Array (Option ℕ)} {inC : Array Bool}
    {memo : Assign} (h : MemoSound log reason inC memo) {v : ℕ} (hv : memo.value v = none) :
    MemoSound log reason inC (memo.set v (some false)) ∧ Keeps memo (memo.set v (some false)) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [Assign.value_set] at hw
    split at hw
    · simp at hw
    · obtain ⟨r, R, hr, hR, hz⟩ := h w hw
      refine ⟨r, R, hr, hR, fun z hz' hne => (hz z hz' hne).imp id fun hzt => ?_⟩
      rw [Assign.value_set, ite_eq_right]
      · exact hzt
      · rintro rfl; simp [hv] at hzt
  · rw [Assign.value_set, ite_eq_right]
    rintro rfl; exact hw hv

/-- **The search for derived literals is sound**: it keeps the memo sound, only fills entries, and
records a literal found derived. -/
private theorem derived_spec {log : LRATLog φ} {reason : Array (Option ℕ)} {inC : Array Bool}
    {deep : ℕ → Bool} : ∀ (fuel : ℕ) (memo : Assign) (v : ℕ),
      MemoSound log reason inC memo →
      MemoSound log reason inC (derived log reason inC deep fuel memo v).2 ∧
        Keeps memo (derived log reason inC deep fuel memo v).2 ∧
        ((derived log reason inC deep fuel memo v).1 = true →
          (derived log reason inC deep fuel memo v).2.value v = some true)
  | 0, memo, v, h => ⟨h, fun _ _ => rfl, by simp [derived]⟩
  | fuel + 1, memo, v, h => by
    simp only [derived]
    split
    · rename_i b hb
      exact ⟨h, fun _ _ => rfl, fun hb' => by simp only at hb'; rw [hb, hb']⟩
    · rename_i hv
      split
      · exact ⟨(h.set_false hv).1, (h.set_false hv).2, by simp⟩
      · rename_i R hR
        obtain ⟨r, hr, hRr⟩ := Option.bind_eq_some_iff.1 hR
        obtain ⟨h₁, hk₁⟩ := h.set_false hv
        -- the fold over the reason
        have hfold : ∀ (Rs : Clause ℕ) (acc : Bool × Assign),
            MemoSound log reason inC acc.2 → Keeps (memo.set v (some false)) acc.2 →
            let res := Rs.foldl (fun (acc : Bool × Assign) z =>
              if !acc.1 then acc
              else if z.1 == v || inC.getD z.1 false then acc
              else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
              else (false, acc.2)) acc
            MemoSound log reason inC res.2 ∧ Keeps (memo.set v (some false)) res.2 ∧
              Keeps acc.2 res.2 ∧
              (res.1 = true → acc.1 = true ∧
                ∀ z ∈ Rs, z.1 ≠ v → inC.getD z.1 false = true ∨ res.2.value z.1 = some true) := by
          intro Rs
          induction Rs with
          | nil => exact fun acc ha hk => ⟨ha, hk, fun _ _ => rfl, fun h => ⟨h, by simp⟩⟩
          | cons z Rs ih =>
            intro acc ha hk
            simp only [List.foldl_cons]
            by_cases hacc : acc.1 = true
            · by_cases hz : (z.1 == v || inC.getD z.1 false) = true
              · have hstep : (if !acc.1 then acc
                    else if z.1 == v || inC.getD z.1 false then acc
                    else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
                    else (false, acc.2)) = acc := by
                  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz]
                rw [hstep]
                obtain ⟨i₁, i₂, i₃, i₄⟩ := ih acc ha hk
                refine ⟨i₁, i₂, i₃, fun hres => ⟨hacc, fun z' hz' hne => ?_⟩⟩
                rcases List.mem_cons.1 hz' with rfl | hz'
                · simp only [Bool.or_eq_true, beq_iff_eq] at hz
                  exact .inl (hz.resolve_left hne)
                · exact (i₄ hres).2 z' hz' hne
              · by_cases hd : deep z.1 = true
                · have hstep : (if !acc.1 then acc
                      else if z.1 == v || inC.getD z.1 false then acc
                      else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
                      else (false, acc.2)) = derived log reason inC deep fuel acc.2 z.1 := by
                    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                      Bool.eq_false_iff.2 hz, hd]
                  rw [hstep]
                  obtain ⟨d₁, d₂, d₃⟩ := derived_spec fuel acc.2 z.1 ha
                  obtain ⟨i₁, i₂, i₃, i₄⟩ := ih _ d₁ (hk.trans d₂)
                  refine ⟨i₁, i₂, d₂.trans i₃, fun hres => ⟨hacc, fun z' hz' hne => ?_⟩⟩
                  rcases List.mem_cons.1 hz' with rfl | hz'
                  · exact .inr (i₃.true (d₃ (i₄ hres).1))
                  · exact (i₄ hres).2 z' hz' hne
                · have hstep : (if !acc.1 then acc
                      else if z.1 == v || inC.getD z.1 false then acc
                      else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
                      else (false, acc.2)) = (false, acc.2) := by
                    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                      Bool.eq_false_iff.2 hz, Bool.eq_false_iff.2 hd]
                  rw [hstep]
                  obtain ⟨i₁, i₂, i₃, i₄⟩ := ih (false, acc.2) ha hk
                  exact ⟨i₁, i₂, i₃, fun hres => absurd (i₄ hres).1 (by simp)⟩
            · have hstep : (if !acc.1 then acc
                  else if z.1 == v || inC.getD z.1 false then acc
                  else if deep z.1 then derived log reason inC deep fuel acc.2 z.1
                  else (false, acc.2)) = acc := by
                simp only [Bool.eq_false_iff.2 hacc, Bool.not_false, ↓reduceIte]
              rw [hstep]
              obtain ⟨i₁, i₂, i₃, i₄⟩ := ih acc ha hk
              exact ⟨i₁, i₂, i₃, fun hres => absurd (i₄ hres).1 hacc⟩
        obtain ⟨f₁, f₂, -, f₄⟩ := hfold R (true, memo.set v (some false)) h₁ fun _ _ => rfl
        generalize hres : R.foldl _ (true, memo.set v (some false)) = res at f₁ f₂ f₄
        -- the variable `v` is still recorded as not derived
        have hvres : res.2.value v = some false :=
          (f₂ v (by simp [Assign.value_set])).trans (by simp [Assign.value_set])
        refine ⟨fun w hw => ?_, fun w hw => ?_,
          fun h => by rw [Assign.value_set, ite_eq_left rfl, h]⟩
        · rw [Assign.value_set] at hw
          split at hw
          · rename_i hwv
            subst hwv
            simp only [Option.some.injEq] at hw
            refine ⟨r, R, hr, hRr, fun z hz hne => (((f₄ hw).2 z hz hne)).imp id fun hzt => ?_⟩
            rw [Assign.value_set, ite_eq_right hne]
            exact hzt
          · rename_i hwv
            obtain ⟨r', R', hr', hR', hz⟩ := f₁ w hw
            refine ⟨r', R', hr', hR', fun z hz' hne => (hz z hz' hne).imp id fun hzt => ?_⟩
            rw [Assign.value_set, ite_eq_right]
            · exact hzt
            · rintro hzv; rw [hzv, hvres] at hzt; simp at hzt
        · have hwv : w ≠ v := by rintro rfl; exact hw hv
          rw [Assign.value_set, ite_eq_right hwv]
          exact (f₂ w (by rw [hk₁ w hw]; exact hw)).trans (hk₁ w hw)

/-- **The redundant literals are derived**: they are literals of the clause other than `lit`,
recorded as derived in a sound memo. -/
private theorem redundant_spec {log : LRATLog φ} {reason : Array (Option ℕ)} {inC : Array Bool}
    {deep : ℕ → Bool} {fuel : ℕ} {lit : Literal ℕ} {C : Clause ℕ} {memo : Assign}
    (h : MemoSound log reason inC memo) :
    MemoSound log reason inC (redundant log reason inC deep fuel lit C memo).2 ∧
      ∀ y ∈ (redundant log reason inC deep fuel lit C memo).1, y ∈ C ∧ y ≠ lit ∧
        (redundant log reason inC deep fuel lit C memo).2.value y.1 = some true := by
  suffices ∀ (Cs : Clause ℕ) (acc : List (Literal ℕ) × Assign), MemoSound log reason inC acc.2 →
      (∀ y ∈ acc.1, y ∈ C ∧ y ≠ lit ∧ acc.2.value y.1 = some true) → (∀ y ∈ Cs, y ∈ C) →
      let res := Cs.foldl (fun (acc : List (Literal ℕ) × Assign) y =>
        if y == lit then acc
        else
          let r := derived log reason inC deep fuel acc.2 y.1
          (if r.1 then y :: acc.1 else acc.1, r.2)) acc
      MemoSound log reason inC res.2 ∧ ∀ y ∈ res.1, y ∈ C ∧ y ≠ lit ∧ res.2.value y.1 = some true
    from this C ([], memo) h (by simp) fun _ h => h
  intro Cs
  induction Cs with
  | nil => exact fun acc ha hacc _ => ⟨ha, hacc⟩
  | cons y Cs ih =>
    intro acc ha hacc hC
    simp only [List.foldl_cons]
    have hC' : ∀ z ∈ Cs, z ∈ C := fun z hz => hC z (List.mem_cons_of_mem _ hz)
    split
    · exact ih acc ha hacc hC'
    · rename_i hy
      obtain ⟨d₁, d₂, d₃⟩ := derived_spec (deep := deep) fuel acc.2 y.1 ha
      refine ih _ d₁ (fun z hz => ?_) hC'
      split at hz
      · rename_i hd
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨hC _ List.mem_cons_self, by simpa using hy, d₃ hd⟩
        · obtain ⟨h₁, h₂, h₃⟩ := hacc z hz
          exact ⟨h₁, h₂, d₂.true h₃⟩
      · obtain ⟨h₁, h₂, h₃⟩ := hacc z hz
        exact ⟨h₁, h₂, d₂.true h₃⟩

/-- The derived literals of the trail `T`: the implied literals recorded as derived. -/
private def derivedLits (T : XTrail) (memo : Assign) : List (Literal ℕ) :=
  T.filterMap fun x => match x with
    | .implied l _ => if memo.value l.1 == some true then some l else none
    | .decision _ => none

/-- **Propagating the derived literals**: if no decision is recorded as derived, and the reason of
each derived literal has its other literals false under `τ` or derived, then unit propagation from
`τ` along the reasons of the derived literals, oldest first, propagates every derived literal, and
continues with `hs`. -/
private theorem propagate_derivedHints {log : LRATLog φ} {memo : Assign} {τ : List (Literal ℕ)} :
    ∀ (T : XTrail) (hs : List ℕ), Reasons log T →
      (∀ d, XEntry.decision d ∈ T → memo.value d.1 ≠ some true) →
      (∀ l r R, XEntry.implied l r ∈ T → memo.value l.1 = some true → log.clause? r = some R →
        ∀ z ∈ R, z ≠ l → z.negate ∈ τ ∨ memo.value z.1 = some true) →
      (∀ t, (∀ y ∈ τ, y ∈ t) → (∀ y ∈ derivedLits T memo, y ∈ t) →
        propagateHints log.db t hs = true) →
      propagateHints log.db τ (derivedHints T memo ++ hs) = true
  | [], hs, _, _, _, h => h τ (fun _ h => h) (by simp [derivedLits])
  | x :: T, hs, hreasons, hdec, hred, h => by
    have hdec' : ∀ d, XEntry.decision d ∈ T → memo.value d.1 ≠ some true :=
      fun d hd => hdec d (List.mem_cons_of_mem _ hd)
    have hred' : ∀ l r R, XEntry.implied l r ∈ T → memo.value l.1 = some true →
        log.clause? r = some R → ∀ z ∈ R, z ≠ l → z.negate ∈ τ ∨ memo.value z.1 = some true :=
      fun l r R hx => hred l r R (List.mem_cons_of_mem _ hx)
    -- a literal of `T` recorded as derived is a derived literal of `T`
    have hlits : ∀ y, y ∈ Trail.lits (XTrail.trail T) → memo.value y.1 = some true →
        y ∈ derivedLits T memo := fun y hy hm => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
      obtain ⟨x', hx', rfl⟩ := List.mem_map.1 he
      cases x' with
      | decision d => exact absurd hm (hdec' d hx')
      | implied l r =>
        simp only [XEntry.entry_implied] at hm
        exact List.mem_filterMap.2 ⟨_, hx', by simpa using hm⟩
    cases x with
    | decision d =>
      have hh : derivedHints (.decision d :: T) memo = derivedHints T memo := by
        simp [derivedHints]
      rw [hh]
      exact propagate_derivedHints T hs hreasons.tail hdec' hred' fun t hτ hd =>
        h t hτ fun y hy => hd y (by simpa [derivedLits] using hy)
    | implied l r =>
      by_cases hm : memo.value l.1 = some true
      · have hh : derivedHints (.implied l r :: T) memo ++ hs = derivedHints T memo ++ r :: hs := by
          simp [derivedHints, hm]
        rw [hh]
        obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hreasons.isSome
        refine propagate_derivedHints T (r :: hs) hreasons.tail hdec' hred' fun t hτ hd => ?_
        refine propagateHints_cons_unit (l := l) (LRATLog.find?_of_clause? hR)
          (fun z hz hne => ?_) ?_
        · rcases hred l r R List.mem_cons_self hm hR z hz hne with h' | h'
          · exact hτ _ h'
          · exact hd _ (hlits _ ((hreasons.reason hR).2 z hz hne)
              (by simpa [Std.Sat.Literal.negate]))
        · refine h _ (fun y hy => List.mem_cons_of_mem _ (hτ y hy)) fun y hy => ?_
          have : derivedLits (.implied l r :: T) memo = l :: derivedLits T memo := by
            simp [derivedLits, hm]
          rw [this] at hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hd y hy)
      · have hh : derivedHints (.implied l r :: T) memo = derivedHints T memo := by
          simp [derivedHints, hm]
        rw [hh]
        exact propagate_derivedHints T hs hreasons.tail hdec' hred' fun t hτ hd =>
          h t hτ fun y hy => hd y (by simpa [derivedLits, hm] using hy)

/-- The other literals of a reason are on variables other than its literal's, on a trail assigning
each variable once. -/
private theorem Reasons.var_ne {log : LRATLog φ} {T : XTrail} (h : Reasons log T)
    (hnd : (Trail.vars (XTrail.trail T)).Nodup) {l : Literal ℕ} {r : ℕ} {R : Clause ℕ}
    (hx : XEntry.implied l r ∈ T) (hR : log.clause? r = some R) :
    ∀ z ∈ R, z ≠ l → z.negate ∈ Trail.lits (XTrail.trail T) ∧ z.1 ≠ l.1 := by
  induction h with
  | nil => simp at hx
  | decision d _ ih =>
    simp only [XTrail.trail_cons, Trail.vars, List.map_cons, List.nodup_cons] at hnd
    intro z hz hne
    obtain ⟨h₁, h₂⟩ := ih hnd.2 (by simpa using hx) z hz hne
    exact ⟨mem_lits_cons.2 (.inr h₁), h₂⟩
  | @implied M l' r' R' _ hr' _ hfalse ih =>
    simp only [XTrail.trail_cons, Trail.vars, List.map_cons, List.nodup_cons] at hnd
    intro z hz hne
    rcases List.mem_cons.1 hx with hx | hx
    · cases hx
      rw [hR] at hr'
      cases hr'
      have hzM := hfalse z hz hne
      refine ⟨mem_lits_cons.2 (.inr hzM), fun hzl => hnd.1 ?_⟩
      have := Trail.mem_vars_of_mem_lits hzM
      rw [show (Std.Sat.Literal.negate z).1 = z.1 from rfl, hzl] at this
      exact this
    · obtain ⟨h₁, h₂⟩ := ih hnd.2 hx z hz hne
      exact ⟨mem_lits_cons.2 (.inr h₁), h₂⟩

/-- On a trail assigning each variable once, two entries on one variable are equal. -/
private theorem XTrail.eq_of_var_eq {T : XTrail} (hnd : (Trail.vars (XTrail.trail T)).Nodup)
    {x y : XEntry}
    (hx : x ∈ T) (hy : y ∈ T) (h : x.entry.lit.1 = y.entry.lit.1) : x = y := by
  have : (T.map (Entry.var ∘ XEntry.entry)).Nodup := by
    simpa [Trail.vars, XTrail.trail, List.map_map] using hnd
  exact List.inj_on_of_nodup_map this hx hy h

variable {log₀ : LRATLog φ} {A : Trail}

/-- **The minimized clause is a RUP clause**: unit propagation from its negation along the reasons
of the derived literals, oldest first, and then the hints of the learned clause reaches a conflict.
This is what `Cslib.Algorithms.Lean.CDCL.Learned.minimize` logs, with no check at run time. -/
theorem Learned.propagateHints_minimized {T : XTrail} (L : Learned log₀ A (XTrail.trail T))
    (hreasons : Reasons log₀ T) (hnd : (Trail.vars (XTrail.trail T)).Nodup) (recursive : Bool)
    (n : ℕ) :
    let C := L.clause
    let r := minimizeRedundant log₀ T C L.lit recursive n
    propagateHints log₀.db ((L.lit :: C.filter fun y => y != L.lit && !r.1.contains y).map
      Std.Sat.Literal.negate) (derivedHints T r.2 ++ L.hints) = true := by
  intro C r
  let D := L.lit :: C.filter fun y => y != L.lit && !r.1.contains y
  change propagateHints log₀.db (D.map Std.Sat.Literal.negate) _ = true
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let root := Assign.ofTrail (XTrail.trail (XTrail.root T))
      fun v => root.assigned v
  have hspec := redundant_spec (log := log₀) (reason := T.reasons n) (inC := clauseVars C n)
    (deep := deep) (fuel := n + 1) (lit := L.lit) (C := C)
    (memo := ⟨Array.replicate n 0⟩) fun w hw => by
      simp only [Assign.value, Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hw
      split at hw <;> simp at hw
  -- a literal of the learned clause is kept or removed
  have hD : ∀ y ∈ C, y ∈ D ∨ (y ∈ r.1 ∧ r.2.value y.1 = some true) := fun y hy => by
    by_cases hyr : y ∈ r.1
    · exact .inr ⟨hyr, (hspec.2 y hyr).2.2⟩
    · by_cases hyl : y = L.lit
      · exact .inl (hyl ▸ List.mem_cons_self)
      · exact .inl (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hy, by simp [hyl, hyr]⟩))
  -- the variables recorded as derived are implied on the trail
  have hderiv : ∀ w, r.2.value w = some true → ∃ b r', XEntry.implied (w, b) r' ∈ T := by
    intro w hw
    obtain ⟨r', -, hr', -⟩ := hspec.1 w hw
    obtain ⟨b, hb⟩ := XTrail.mem_of_reasons hr'
    exact ⟨b, r', hb⟩
  exact propagate_derivedHints T L.hints hreasons
    (fun d hd hm => by
      obtain ⟨b, r', hx⟩ := hderiv _ hm
      exact absurd (XTrail.eq_of_var_eq hnd hd hx rfl) (by simp))
    (fun l r' R hx hm hR z hz hne => by
      obtain ⟨r'', R', hr'', hR', hz'⟩ := hspec.1 l.1 hm
      obtain ⟨b, hb⟩ := XTrail.mem_of_reasons hr''
      obtain ⟨hzT, hzl⟩ := hreasons.var_ne hnd hx hR z hz hne
      -- the reason recorded is that of `l`
      have hxe := XTrail.eq_of_var_eq hnd hx hb rfl
      simp only [XEntry.implied.injEq] at hxe
      obtain ⟨-, rfl⟩ := hxe
      rw [hR] at hR'
      cases hR'
      rcases hz' z hz hzl with hC | hm'
      · -- `z` is on a variable of the learned clause, hence one of its literals
        obtain ⟨y, hy, hyz⟩ := mem_of_clauseVars hC
        have hyL := hy
        have hyl : y ≠ L.lit := fun h => L.undef (by
          rw [← h, hyz]
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hzT)
        have hyz' : y = z := negate_inj (eq_of_mem_lits hnd (L.false_below y hyL hyl) hzT
          (by simpa [Std.Sat.Literal.negate] using hyz))
        subst hyz'
        rcases hD y hy with h' | ⟨-, h'⟩
        · exact .inl (List.mem_map.2 ⟨y, h', rfl⟩)
        · exact .inr h'
      · exact .inr hm')
    fun t hτ hd => propagateHints_mono (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        by_cases hyl : y = L.lit
        · exact hτ _ (List.mem_map.2 ⟨y, hyl ▸ List.mem_cons_self, rfl⟩)
        rcases hD y hy with h' | ⟨-, h'⟩
        · exact hτ _ (List.mem_map.2 ⟨y, h', rfl⟩)
        · refine hd _ ?_
          have hyT := L.false_below y hy hyl
          obtain ⟨e, he, hey⟩ := List.mem_map.1 hyT
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
          cases x with
          | decision d =>
            obtain ⟨b, r', hx'⟩ := hderiv _ h'
            exact absurd (XTrail.eq_of_var_eq hnd hx hx' (by
              simp only [XEntry.entry] at hey ⊢
              rw [hey]; rfl)) (by simp)
          | implied l r' =>
            simp only [XEntry.entry] at hey
            subst hey
            exact List.mem_filterMap.2 ⟨_, hx, by simpa [Std.Sat.Literal.negate] using h'⟩)
      L.rup


/-- `XTrail.reasons` of the entries below position `p`, read from the arrays of the trail
(`ATrail.reasonsBelow_eq`). -/
def ATrail.reasonsBelow (T : ATrail) (p n : ℕ) : Array (Option ℕ) :=
  T.foldDown (fun a c r => match r with
    | 0 => a
    | r + 1 => a.setIfInBounds (c / 2) (some r)) 0 p (Array.replicate n none)

theorem ATrail.reasonsBelow_eq (T : ATrail) (p n : ℕ) :
    T.reasonsBelow p n = XTrail.reasons (T.seg 0 p) n := by
  rw [reasonsBelow, foldDown_eq, XTrail.reasons]
  congr 1
  funext a x
  cases x <;> simp only [XEntry.rsnCode, XEntry.lit, litCode_div_two]

/-- `derivedHints` of the entries below position `p`, read from the arrays of the trail in one
pass, newest first, without reversing them (`ATrail.derivedHintsBelow_eq`). -/
def ATrail.derivedHintsBelow (T : ATrail) (p : ℕ) (memo : Assign) : List ℕ :=
  T.foldDown (fun acc c r => match r with
    | 0 => acc
    | r + 1 => if memo.value (c / 2) == some true then r :: acc else acc) 0 p []

theorem ATrail.derivedHintsBelow_eq (T : ATrail) (p : ℕ) (memo : Assign) :
    T.derivedHintsBelow p memo = derivedHints (T.seg 0 p) memo := by
  rw [derivedHintsBelow, foldDown_eq, ← List.append_nil (derivedHints _ _), ← foldl_derivedHints]
  congr 1
  funext a x
  cases x <;> simp only [XEntry.rsnCode, XEntry.lit, litCode_div_two]

/-- `minimizeRedundant` on the entries below position `p`, with the reasons read from the arrays of
the trail. -/
def minimizeRedundantBelow (log : LRATLog φ) (T : ATrail) (p : ℕ) (C : Clause ℕ) (lit : Literal ℕ)
    (recursive : Bool) (n : ℕ) : List (Literal ℕ) × Assign :=
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let root := Assign.ofTrail (XTrail.trail (XTrail.root (T.seg 0 p)))
      fun v => root.assigned v
  redundant log (T.reasonsBelow p n) (clauseVars C n) deep (n + 1) lit C ⟨Array.replicate n 0⟩

theorem minimizeRedundantBelow_eq (log : LRATLog φ) (T : ATrail) (p : ℕ) (C : Clause ℕ)
    (lit : Literal ℕ) (recursive : Bool) (n : ℕ) :
    minimizeRedundantBelow log T p C lit recursive n =
      minimizeRedundant log (T.seg 0 p) C lit recursive n := by
  rw [minimizeRedundantBelow, minimizeRedundant, ATrail.reasonsBelow_eq]

/-- **Minimizing a learned clause**, whose false literals are on the entries of the trail `T` below
position `p`, recursively if `recursive` (MiniSat's `ccmin_mode = 2`) and otherwise in the basic
way (`ccmin_mode = 1`): the learned clause without its redundant literals. Its hints are the
reasons of the derived literals of the trail, oldest first, which propagate the negations of the
literals removed, and then those of the learned clause
(`Cslib.Algorithms.Lean.CDCL.Learned.propagateHints_minimized`). The reasons and the hints are read
from the arrays of the trail. The learned clause is kept if nothing is redundant. -/
def Learned.minimize (T : ATrail) (p : ℕ) (L : Learned log₀ A (XTrail.trail (T.seg 0 p)))
    (hreasons : Reasons log₀ (T.seg 0 p)) (hnd : (Trail.vars (XTrail.trail (T.seg 0 p))).Nodup)
    (n : ℕ) (recursive : Bool := true) : Learned log₀ A (XTrail.trail (T.seg 0 p)) :=
  let C := L.clause
  let r := minimizeRedundantBelow log₀ T p C L.lit recursive n
  if r.1.isEmpty then L
  else
    let D := L.lit :: C.filter fun y => y != L.lit && !r.1.contains y
    have hsub : ∀ y ∈ D, y ∈ L.clause := fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact L.mem
      · exact (List.mem_filter.1 hy).1
    { L with
      clause := D
      hints := T.derivedHintsBelow p r.2 ++ L.hints
      rup := by
        have h := L.propagateHints_minimized hreasons hnd recursive n
        simp only [] at h
        rw [← minimizeRedundantBelow_eq] at h
        rw [ATrail.derivedHintsBelow_eq]
        exact h
      vars_mem := fun l hl => L.vars_mem l (hsub l hl)
      mem := List.mem_cons_self
      false_below := fun y hy hne => L.false_below y (hsub y hy) hne
      nodup := List.nodup_cons.2 ⟨fun h => by simp at h, L.nodup.filter _⟩
      head := rfl }

end Cslib.Algorithms.Lean.CDCL
