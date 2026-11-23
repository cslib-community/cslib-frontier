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

On the solver's array trail (`Cslib.Algorithms.Lean.CDCL.ATrail`), reasons are looked up in
constant time through self-certifying position hints (`Cslib.Algorithms.Lean.CDCL.ATrail.reasonAt`),
and the clause-variable and memo arrays are cleared along the variables touched and reused across
conflicts without per-conflict array allocation.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.MinStep`, `Cslib.Algorithms.Lean.CDCL.derived`,
  `Cslib.Algorithms.Lean.CDCL.redundant`: memoized search for derived literals.
* `Cslib.Algorithms.Lean.CDCL.Learned.minimize`: the minimized learned clause, reusing scratch
  arrays.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Learned.propagateHints_redundant`,
  `Cslib.Algorithms.Lean.CDCL.Learned.propagateHints_minimized`: the minimized clause, with the
  reasons of the derived literals, oldest first, before the hints of the learned clause, is a RUP
  clause.

## References

* [N. Sörensson, A. Biere, *Minimizing Learned Clauses*][SorenssonBiere2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

variable {φ : CNF ℕ}

/-- The reason code (`0` for none/decision, `r + 1` for reason `r`) of each implied variable of the
trail `T`, indexed by variable, for the variables below `n`. -/
def XTrail.reasonCodes (T : XTrail) (n : ℕ) : Array ℕ :=
  T.foldl (fun a x => match x with
    | .implied l r => a.setIfInBounds l.1 (r + 1)
    | .decision _ => a) (Array.replicate n 0)

/-- State of the memoized search for derived literals: `ok` holds the answer of the current step (or
whether any literal was removed in `redundant`), `memo` caches answers (`some true` for derived,
`some false` for not derived or active), and `visited` lists every variable written in `memo` so
the caller can clear `memo` in time proportional to the search. -/
structure MinStep where
  /-- Answer of the current search step, or whether any literal was found redundant. -/
  ok : Bool
  /-- Memoized outcomes indexed by variable. -/
  memo : Assign
  /-- Variables given a value in `memo` during this search. -/
  visited : List ℕ

/-- **Whether the literal of the trail on `v` is derived** from the literals of the learned clause,
whose variables satisfy `inC`: its reason, looked up in `log` through `reasonCode` (`0` for none or
a decision, `r + 1` for reason `r`), has every other literal either on a variable of the learned
clause or, on a variable where `deep` allows the recursion, derived. The results are memoized in
`memo`, where `v` counts as not derived while its reason is searched; `visited` records every
variable written in `memo`; `fuel` bounds the depth of the search, and running out of it counts as
not derived. -/
def derived (log : LRATLog φ) (reasonCode : ℕ → ℕ) (inC : ℕ → Bool) (deep : ℕ → Bool) :
    (fuel : ℕ) → (memo : Assign) → (visited : List ℕ) → (v : ℕ) → MinStep
  | 0, memo, visited, _ => ⟨false, memo, visited⟩
  | fuel + 1, memo, visited, v =>
    match memo.value v with
    | some b => ⟨b, memo, visited⟩
    | none =>
      match reasonCode v with
      | 0 => ⟨false, memo.set v (some false), v :: visited⟩
      | r + 1 =>
        match log.clause? r with
        | none => ⟨false, memo.set v (some false), v :: visited⟩
        | some R =>
          let res := R.foldl (fun (acc : MinStep) z =>
            if !acc.ok then acc
            else if z.1 == v || inC z.1 then acc
            else if deep z.1 then derived log reasonCode inC deep fuel acc.memo acc.visited z.1
            else ⟨false, acc.memo, acc.visited⟩) ⟨true, memo.set v (some false), v :: visited⟩
          ⟨res.ok, if res.ok then res.memo.set v (some true) else res.memo, res.visited⟩

/-- Whether any literal of the clause `C` other than `lit` has its negation derived, together with
the memoized search and the list of variables written in `memo`. -/
def redundant (log : LRATLog φ) (reasonCode : ℕ → ℕ) (inC : ℕ → Bool) (deep : ℕ → Bool)
    (fuel : ℕ) (lit : Literal ℕ) (C : Clause ℕ) (memo : Assign) : MinStep :=
  C.foldl (fun (acc : MinStep) y =>
    if Assign.litEq y lit then acc
    else
      let r := derived log reasonCode inC deep fuel acc.memo acc.visited y.1
      ⟨acc.ok || r.ok, r.memo, r.visited⟩) ⟨false, memo, []⟩

/-- The reasons of the derived literals of the trail `T`, oldest first: the hints that propagate
them. -/
def derivedHints (T : XTrail) (memo : Assign) : List ℕ :=
  T.reverse.filterMap fun x => match x with
    | .implied l r => if memo.value l.1 == some true then some r else none
    | .decision _ => none

/-- `derivedHints` in one pass over the trail, newest first, without reversing it. -/
def derivedHintsFast (T : XTrail) (memo : Assign) : List ℕ :=
  T.foldl (fun acc x => match x with
    | .implied l r => if memo.holds (l.1, true) then r :: acc else acc
    | .decision _ => acc) []

private theorem holds_true_eq_beq (memo : Assign) (v : ℕ) :
    memo.holds (v, true) = (memo.value v == some true) :=
  Bool.eq_iff_iff.2 (by rw [Assign.holds_eq_true, beq_iff_eq])

private theorem foldl_derivedHints (memo : Assign) : ∀ (T : XTrail) (acc : List ℕ),
    T.foldl (fun acc x => match x with
      | .implied l r => if memo.holds (l.1, true) then r :: acc else acc
      | .decision _ => acc) acc = derivedHints T memo ++ acc
  | [], _ => by simp [derivedHints]
  | x :: T, acc => by
    rw [List.foldl_cons, foldl_derivedHints memo T]
    cases x with
    | decision d => simp [derivedHints]
    | implied l r =>
      dsimp only
      rw [holds_true_eq_beq]
      by_cases h : memo.value l.1 = some true <;> simp [derivedHints, h]

theorem derivedHintsFast_eq (T : XTrail) (memo : Assign) :
    derivedHintsFast T memo = derivedHints T memo := by
  rw [derivedHintsFast, foldl_derivedHints, List.append_nil]

/-- The array marking the variables of the clause `C`, below `n`. -/
def clauseVars (C : Clause ℕ) (n : ℕ) : Array Bool :=
  C.foldl (fun a y => a.setIfInBounds y.1 true) (Array.replicate n false)

/-- **The redundant search** on the learned clause `C` with asserting literal `lit`, whose false
literals are on the trail `T`: recursively if `recursive`, and otherwise following only the reasons
of the literals implied at the root. -/
def minimizeRedundant (log : LRATLog φ) (T : XTrail) (C : Clause ℕ) (lit : Literal ℕ)
    (recursive : Bool) (n : ℕ) : MinStep :=
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let root := Assign.ofTrail (XTrail.trail (XTrail.root T))
      fun v => root.assigned v
  let reasons := T.reasonCodes n
  let inC := clauseVars C n
  redundant log (fun v => reasons.getD v 0) (fun v => inC.getD v false) deep (n + 1) lit C
    ⟨Array.replicate n 0⟩

/-! ### The minimized clause is a RUP clause -/

/-- The entries of the reason-code array are reasons of the trail. -/
private theorem XTrail.mem_of_reasonCodes {T : XTrail} {n v r : ℕ}
    (h : (T.reasonCodes n).getD v 0 = r + 1) :
    ∃ b, XEntry.implied (v, b) r ∈ T := by
  suffices ∀ (T : XTrail) (a : Array ℕ),
      (T.foldl (fun a x => match x with
        | .implied l r => a.setIfInBounds l.1 (r + 1)
        | .decision _ => a) a).getD v 0 = r + 1 →
        a.getD v 0 = r + 1 ∨ ∃ b, XEntry.implied (v, b) r ∈ T by
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
variables satisfying `inC` or recorded as derived. -/
private def MemoSound (log : LRATLog φ) (reasonCode : ℕ → ℕ) (inC : ℕ → Bool)
    (memo : Assign) : Prop :=
  ∀ w, memo.value w = some true → ∃ r R, reasonCode w = r + 1 ∧ log.clause? r = some R ∧
    ∀ z ∈ R, z.1 ≠ w → inC z.1 = true ∨ memo.value z.1 = some true

/-- The search only fills entries of the memo. -/
private def Keeps (memo memo' : Assign) : Prop :=
  ∀ w, memo.value w ≠ none → memo'.value w = memo.value w

/-- Every variable with a value in `memo` is listed in `visited`. -/
private def VisitedCovers (memo : Assign) (visited : List ℕ) : Prop :=
  ∀ w, w ∉ visited → memo.value w = none

private theorem Keeps.trans {a b c : Assign} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  fun w hw => (h₂ w (by rw [h₁ w hw]; exact hw)).trans (h₁ w hw)

private theorem Keeps.true {a b : Assign} (h : Keeps a b) {w : ℕ} (hw : a.value w = some true) :
    b.value w = some true := (h w (by simp [hw])).trans hw

private theorem VisitedCovers.set {memo : Assign} {visited : List ℕ}
    (hc : VisitedCovers memo visited) (v : ℕ) (x : Option Bool) :
    VisitedCovers (memo.set v x) (v :: visited) := fun w hw => by
  simp only [List.mem_cons, not_or] at hw
  rw [Assign.value_set, ite_eq_right hw.1]
  exact hc w hw.2

/-- Recording a variable without a value as not derived keeps the memo sound. -/
private theorem MemoSound.set_false {log : LRATLog φ} {reasonCode : ℕ → ℕ} {inC : ℕ → Bool}
    {memo : Assign} (h : MemoSound log reasonCode inC memo) {v : ℕ} (hv : memo.value v = none) :
    MemoSound log reasonCode inC (memo.set v (some false)) ∧
      Keeps memo (memo.set v (some false)) := by
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

/-- **The search for derived literals is sound**: it keeps the memo sound, only fills entries,
records every written variable in `visited`, and records a literal found derived. -/
private theorem derived_spec {log : LRATLog φ} {reasonCode : ℕ → ℕ} {inC : ℕ → Bool}
    {deep : ℕ → Bool} : ∀ (fuel : ℕ) (memo : Assign) (visited : List ℕ) (v : ℕ),
      MemoSound log reasonCode inC memo → VisitedCovers memo visited →
      let s := derived log reasonCode inC deep fuel memo visited v
      MemoSound log reasonCode inC s.memo ∧ Keeps memo s.memo ∧ VisitedCovers s.memo s.visited ∧
        (s.ok = true → s.memo.value v = some true)
  | 0, memo, visited, _, h, hc => ⟨h, fun _ _ => rfl, hc, by simp [derived]⟩
  | fuel + 1, memo, visited, v, h, hc => by
    simp only [derived]
    split
    · rename_i b hb
      exact ⟨h, fun _ _ => rfl, hc, fun hb' => by simp only at hb'; rw [hb, hb']⟩
    · rename_i hv
      obtain ⟨h₁, hk₁⟩ := h.set_false hv
      have hc₁ := hc.set v (some false)
      split
      · exact ⟨h₁, hk₁, hc₁, by simp⟩
      · rename_i r hr
        split
        · exact ⟨h₁, hk₁, hc₁, by simp⟩
        · rename_i R hRr
          have hfold : ∀ (Rs : Clause ℕ) (acc : MinStep),
              MemoSound log reasonCode inC acc.memo → Keeps (memo.set v (some false)) acc.memo →
              VisitedCovers acc.memo acc.visited →
              let res := Rs.foldl (fun (acc : MinStep) z =>
                if !acc.ok then acc
                else if z.1 == v || inC z.1 then acc
                else if deep z.1 then derived log reasonCode inC deep fuel acc.memo acc.visited z.1
                else ⟨false, acc.memo, acc.visited⟩) acc
              MemoSound log reasonCode inC res.memo ∧ Keeps (memo.set v (some false)) res.memo ∧
                Keeps acc.memo res.memo ∧ VisitedCovers res.memo res.visited ∧
                (res.ok = true → acc.ok = true ∧
                  ∀ z ∈ Rs, z.1 ≠ v → inC z.1 = true ∨ res.memo.value z.1 = some true) := by
            intro Rs
            induction Rs with
            | nil => exact fun acc ha hk hcv => ⟨ha, hk, fun _ _ => rfl, hcv,
                fun h => ⟨h, by simp⟩⟩
            | cons z Rs ih =>
              intro acc ha hk hcv
              simp only [List.foldl_cons]
              by_cases hacc : acc.ok = true
              · by_cases hz : (z.1 == v || inC z.1) = true
                · have hstep : (if !acc.ok then acc
                      else if z.1 == v || inC z.1 then acc
                      else if deep z.1 then
                        derived log reasonCode inC deep fuel acc.memo acc.visited z.1
                      else ⟨false, acc.memo, acc.visited⟩) = acc := by
                    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz]
                  rw [hstep]
                  obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := ih acc ha hk hcv
                  refine ⟨i₁, i₂, i₃, i₄, fun hres => ⟨hacc, fun z' hz' hne => ?_⟩⟩
                  rcases List.mem_cons.1 hz' with rfl | hz'
                  · simp only [Bool.or_eq_true, beq_iff_eq] at hz
                    exact .inl (hz.resolve_left hne)
                  · exact (i₅ hres).2 z' hz' hne
                · by_cases hd : deep z.1 = true
                  · have hstep : (if !acc.ok then acc
                        else if z.1 == v || inC z.1 then acc
                        else if deep z.1 then
                          derived log reasonCode inC deep fuel acc.memo acc.visited z.1
                        else ⟨false, acc.memo, acc.visited⟩) =
                          derived log reasonCode inC deep fuel acc.memo acc.visited z.1 := by
                      simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        Bool.eq_false_iff.2 hz, hd]
                    rw [hstep]
                    obtain ⟨d₁, d₂, d₃, d₄⟩ := derived_spec fuel acc.memo acc.visited z.1 ha hcv
                    obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := ih _ d₁ (hk.trans d₂) d₃
                    refine ⟨i₁, i₂, d₂.trans i₃, i₄, fun hres => ⟨hacc, fun z' hz' hne => ?_⟩⟩
                    rcases List.mem_cons.1 hz' with rfl | hz'
                    · exact .inr (i₃.true (d₄ (i₅ hres).1))
                    · exact (i₅ hres).2 z' hz' hne
                  · have hstep : (if !acc.ok then acc
                        else if z.1 == v || inC z.1 then acc
                        else if deep z.1 then
                          derived log reasonCode inC deep fuel acc.memo acc.visited z.1
                        else ⟨false, acc.memo, acc.visited⟩) =
                          ⟨false, acc.memo, acc.visited⟩ := by
                      simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        Bool.eq_false_iff.2 hz, Bool.eq_false_iff.2 hd]
                    rw [hstep]
                    obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := ih ⟨false, acc.memo, acc.visited⟩ ha hk hcv
                    exact ⟨i₁, i₂, i₃, i₄, fun hres => absurd (i₅ hres).1 (by simp)⟩
              · have hstep : (if !acc.ok then acc
                    else if z.1 == v || inC z.1 then acc
                    else if deep z.1 then
                      derived log reasonCode inC deep fuel acc.memo acc.visited z.1
                    else ⟨false, acc.memo, acc.visited⟩) = acc := by
                  simp only [Bool.eq_false_iff.2 hacc, Bool.not_false, ↓reduceIte]
                rw [hstep]
                obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := ih acc ha hk hcv
                exact ⟨i₁, i₂, i₃, i₄, fun hres => absurd (i₅ hres).1 hacc⟩
          obtain ⟨f₁, f₂, -, f₄, f₅⟩ :=
            hfold R { ok := true, memo := memo.set v (some false), visited := v :: visited } h₁
              (fun _ _ => rfl) hc₁
          dsimp only
          generalize (R.foldl _
            { ok := true, memo := memo.set v (some false), visited := v :: visited } : MinStep) =
              res at f₁ f₂ f₄ f₅ ⊢
          have hvres : res.memo.value v = some false :=
            (f₂ v (by simp [Assign.value_set])).trans (by simp [Assign.value_set])
          by_cases hok : res.ok = true
          · rw [ite_eq_left hok]
            refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
              fun _ => by rw [Assign.value_set, ite_eq_left rfl]⟩
            · rw [Assign.value_set] at hw
              split at hw
              · rename_i hwv
                subst hwv
                refine ⟨r, R, hr, hRr, fun z hz hne => ((f₅ hok).2 z hz hne).imp id fun hzt => ?_⟩
                rw [Assign.value_set, ite_eq_right hne]
                exact hzt
              · obtain ⟨r', R', hr', hR', hz⟩ := f₁ w hw
                refine ⟨r', R', hr', hR', fun z hz' hne => (hz z hz' hne).imp id fun hzt => ?_⟩
                rw [Assign.value_set, ite_eq_right]
                · exact hzt
                · rintro hzv; rw [hzv, hvres] at hzt; simp at hzt
            · have hwv : w ≠ v := by rintro rfl; exact hw hv
              rw [Assign.value_set, ite_eq_right hwv]
              exact (f₂ w (by rw [hk₁ w hw]; exact hw)).trans (hk₁ w hw)
            · have hwv : w ≠ v := by
                rintro rfl
                have := f₄ w hw
                rw [hvres] at this
                simp at this
              rw [Assign.value_set, ite_eq_right hwv]
              exact f₄ w hw
          · rw [ite_eq_right hok]
            exact ⟨f₁, hk₁.trans f₂, f₄, fun h' => absurd h' hok⟩

/-- **The redundant search is sound**: it keeps the memo sound and tracks every written variable in
`visited`. -/
private theorem redundant_spec {log : LRATLog φ} {reasonCode : ℕ → ℕ} {inC : ℕ → Bool}
    {deep : ℕ → Bool} {fuel : ℕ} {lit : Literal ℕ} {C : Clause ℕ} {memo : Assign}
    (h : MemoSound log reasonCode inC memo) (h0 : ∀ w, memo.value w = none) :
    let s := redundant log reasonCode inC deep fuel lit C memo
    MemoSound log reasonCode inC s.memo ∧ VisitedCovers s.memo s.visited := by
  suffices ∀ (Cs : Clause ℕ) (acc : MinStep),
      MemoSound log reasonCode inC acc.memo → VisitedCovers acc.memo acc.visited →
      let res := Cs.foldl (fun (acc : MinStep) y =>
        if Assign.litEq y lit then acc
        else
          let r := derived log reasonCode inC deep fuel acc.memo acc.visited y.1
          ⟨acc.ok || r.ok, r.memo, r.visited⟩) acc
      MemoSound log reasonCode inC res.memo ∧ VisitedCovers res.memo res.visited from
    this C ⟨false, memo, []⟩ h fun w _ => h0 w
  intro Cs
  induction Cs with
  | nil => exact fun acc ha hc => ⟨ha, hc⟩
  | cons y Cs ih =>
    intro acc ha hc
    simp only [List.foldl_cons]
    split
    · exact ih acc ha hc
    · obtain ⟨d₁, -, d₃, -⟩ := derived_spec (deep := deep) fuel acc.memo acc.visited y.1 ha hc
      exact ih _ d₁ d₃

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

/-- **Removing derived literals yields a RUP clause**, for any sound reason lookup `reasonCode`,
clause-variable predicate `inC`, depth filter `deep`, fuel, and empty initial `memo₀`. -/
theorem Learned.propagateHints_redundant {T : XTrail} (L : Learned log₀ A (XTrail.trail T))
    (hreasons : Reasons log₀ T) (hnd : (Trail.vars (XTrail.trail T)).Nodup)
    {reasonCode : ℕ → ℕ} (hrc : ∀ v r, reasonCode v = r + 1 → ∃ b, XEntry.implied (v, b) r ∈ T)
    {inC : ℕ → Bool} (hinC : ∀ w, inC w = true → ∃ y ∈ L.clause, y.1 = w)
    (deep : ℕ → Bool) (fuel : ℕ) {memo₀ : Assign} (hmemo₀ : ∀ w, memo₀.value w = none) :
    let C := L.clause
    let r := redundant log₀ reasonCode inC deep fuel L.lit C memo₀
    propagateHints log₀.db
      ((L.lit :: C.filter fun y => !Assign.litEq y L.lit && !r.memo.holds (y.1, true)).map
        Std.Sat.Literal.negate)
      (derivedHints T r.memo ++ L.hints) = true := by
  intro C r
  let D := L.lit :: C.filter fun y => !Assign.litEq y L.lit && !r.memo.holds (y.1, true)
  change propagateHints log₀.db (D.map Std.Sat.Literal.negate) _ = true
  have hspec := (redundant_spec (log := log₀) (reasonCode := reasonCode) (inC := inC)
    (deep := deep) (fuel := fuel) (lit := L.lit) (C := C)
    (fun w hw => absurd hw (by simp [hmemo₀ w])) hmemo₀).1
  have hD : ∀ y ∈ C, y ∈ D ∨ r.memo.value y.1 = some true := fun y hy => by
    by_cases hyl : y = L.lit
    · exact .inl (hyl ▸ List.mem_cons_self)
    · by_cases hyr : r.memo.value y.1 = some true
      · exact .inr hyr
      · refine .inl (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hy, ?_⟩))
        rw [Assign.litEq_eq_decide, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
        refine ⟨decide_eq_false hyl, Bool.eq_false_iff.2 fun hh => hyr ?_⟩
        exact (Assign.holds_eq_true r.memo (y.1, true)).1 hh
  have hderiv : ∀ w, r.memo.value w = some true → ∃ b r', XEntry.implied (w, b) r' ∈ T := by
    intro w hw
    obtain ⟨r', -, hr', -⟩ := hspec w hw
    obtain ⟨b, hb⟩ := hrc w r' hr'
    exact ⟨b, r', hb⟩
  exact propagate_derivedHints T L.hints hreasons
    (fun d hd hm => by
      obtain ⟨b, r', hx⟩ := hderiv _ hm
      exact absurd (XTrail.eq_of_var_eq hnd hd hx rfl) (by simp))
    (fun l r' R hx hm hR z hz hne => by
      obtain ⟨r'', R', hr'', hR', hz'⟩ := hspec l.1 hm
      obtain ⟨b, hb⟩ := hrc l.1 r'' hr''
      obtain ⟨hzT, hzl⟩ := hreasons.var_ne hnd hx hR z hz hne
      have hxe := XTrail.eq_of_var_eq hnd hx hb rfl
      simp only [XEntry.implied.injEq] at hxe
      obtain ⟨-, rfl⟩ := hxe
      rw [hR] at hR'
      cases hR'
      rcases hz' z hz hzl with hC | hm'
      · obtain ⟨y, hy, hyz⟩ := hinC z.1 hC
        have hyl : y ≠ L.lit := fun h => L.undef (by
          rw [← h, hyz]
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hzT)
        have hyz' : y = z := negate_inj (eq_of_mem_lits hnd (L.false_below y hy hyl) hzT
          (by simpa [Std.Sat.Literal.negate] using hyz))
        subst hyz'
        rcases hD y hy with h' | h'
        · exact .inl (List.mem_map.2 ⟨y, h', rfl⟩)
        · exact .inr h'
      · exact .inr hm')
    fun t hτ hd => propagateHints_mono (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        by_cases hyl : y = L.lit
        · exact hτ _ (List.mem_map.2 ⟨y, hyl ▸ List.mem_cons_self, rfl⟩)
        rcases hD y hy with h' | h'
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

/-- **The minimized clause is a RUP clause** (`minimizeRedundant` on `XTrail`). -/
theorem Learned.propagateHints_minimized {T : XTrail} (L : Learned log₀ A (XTrail.trail T))
    (hreasons : Reasons log₀ T) (hnd : (Trail.vars (XTrail.trail T)).Nodup) (recursive : Bool)
    (n : ℕ) :
    let C := L.clause
    let r := minimizeRedundant log₀ T C L.lit recursive n
    propagateHints log₀.db
      ((L.lit :: C.filter fun y => !Assign.litEq y L.lit && !r.memo.holds (y.1, true)).map
        Std.Sat.Literal.negate)
      (derivedHints T r.memo ++ L.hints) = true :=
  L.propagateHints_redundant hreasons hnd (fun _ _ => XTrail.mem_of_reasonCodes)
    (fun _ => mem_of_clauseVars) _ (n + 1) (Assign.value_replicate n)

/-- `derivedHintsFast` of the entries below position `p`, read from the arrays of the trail
(`ATrail.derivedHintsBelow_eq`). -/
def ATrail.derivedHintsBelow (T : ATrail) (p : ℕ) (memo : Assign) : List ℕ :=
  T.foldDown (fun acc c r => match r with
    | 0 => acc
    | r + 1 => if memo.holds (c / 2, true) then r :: acc else acc) 0 p []

theorem ATrail.derivedHintsBelow_eq (T : ATrail) (p : ℕ) (memo : Assign) :
    T.derivedHintsBelow p memo = derivedHints (T.seg 0 p) memo := by
  rw [derivedHintsBelow, foldDown_eq, ← derivedHintsFast_eq, derivedHintsFast]
  congr 1
  funext a x
  cases x <;> simp only [XEntry.rsnCode, XEntry.lit, litKey_div_two]

/-- **Minimizing a learned clause**, whose false literals are on the entries of the trail `T` below
position `p`, recursively if `recursive` (MiniSat's `ccmin_mode = 2`) and otherwise in the basic
way (`ccmin_mode = 1`): the learned clause without its redundant literals, together with the
restored scratch memo array. Reasons are looked up in constant time through `ATrail.reasonAt vpos
p`, the clause variables are marked in `L.seenMarks` and cleared back into `L'.seenMarks`, and the
memo is cleared along `res.visited`, allocating no arrays per conflict. -/
def Learned.minimize (T : ATrail) (vpos : Array ℕ) (p : ℕ)
    (L : Learned log₀ A (XTrail.trail (T.seg 0 p)))
    (memoClean : {A : Assign // ∀ v, A.value v = none})
    (hreasons : Reasons log₀ (T.seg 0 p)) (hnd : (Trail.vars (XTrail.trail (T.seg 0 p))).Nodup)
    (recursive : Bool := true) :
    Learned log₀ A (XTrail.trail (T.seg 0 p)) × {A : Assign // ∀ v, A.value v = none} :=
  let C := L.clause
  let seen₀ := L.seenMarks
  let inCArr := seen₀.1.markLits C
  have hinC : ∀ w, inCArr.assigned w = true → ∃ y ∈ C, y.1 = w := fun w hw => by
    have hw' : w ∈ C.map Prod.fst ∨ seen₀.1.assigned w = true := by
      simpa only [inCArr, Assign.markLits_eq, Assign.assigned_mark] using hw
    rcases hw' with hw' | hw'
    · exact List.mem_map.1 hw'
    · rw [Assign.assigned_eq_isSome, seen₀.2 w] at hw'
      exact absurd hw' (by decide)
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else
      let r0 := T.firstDecGo 0 p
      fun v =>
        let i := vpos.getD v 0
        i < r0 && T.lits.getD i 0 / 2 == v
  let res := redundant log₀ (T.reasonAt vpos p) inCArr.assigned deep (T.size + 1) L.lit C
    memoClean.1
  have hmemo' : ∀ v, (res.memo.unassign res.visited).value v = none := by
    have hres := redundant_spec (log := log₀) (reasonCode := T.reasonAt vpos p)
      (inC := inCArr.assigned) (deep := deep) (fuel := T.size + 1) (lit := L.lit) (C := C)
      (fun w hw => absurd hw (by simp [memoClean.2 w])) memoClean.2
    exact Assign.value_unassign_eq_none hres.2
  let seen' : {A : Assign // ∀ v, A.value v = none} :=
    ⟨inCArr.unassignLits C, Assign.unassignLits_eq inCArr C ▸
      Assign.value_unassign_eq_none fun v hv => by
        rw [show inCArr = seen₀.1.mark (C.map Prod.fst) from Assign.markLits_eq _ _,
          Assign.value_mark, ite_eq_right_iff.2 fun h => absurd h hv]
        exact seen₀.2 v⟩
  if !res.ok then
    ({ L with seenMarks := seen' }, ⟨res.memo.unassign res.visited, hmemo'⟩)
  else
    let D := L.lit :: C.filter fun y => !Assign.litEq y L.lit && !res.memo.holds (y.1, true)
    let hints := T.derivedHintsBelow p res.memo ++ L.hints
    let memo' : {A : Assign // ∀ v, A.value v = none} :=
      ⟨res.memo.unassign res.visited, hmemo'⟩
    have hsub : ∀ y ∈ D, y ∈ L.clause := fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact L.mem
      · exact (List.mem_filter.1 hy).1
    ({ L with
      clause := D
      hints := hints
      rup := by
        have h := L.propagateHints_redundant hreasons hnd
          (fun _ _ => T.mem_seg_of_reasonAt vpos) hinC deep (T.size + 1) memoClean.2
        dsimp only [D, hints, res, C]
        rw [ATrail.derivedHintsBelow_eq]
        exact h
      vars_mem := fun l hl => L.vars_mem l (hsub l hl)
      mem := List.mem_cons_self
      false_below := fun y hy hne => L.false_below y (hsub y hy) hne
      seenMarks := seen'
      nodup := List.nodup_cons.2 ⟨fun h => by
        have := (List.mem_filter.1 h).2
        simp [Assign.litEq_eq_decide] at this, L.nodup.filter _⟩
      head := rfl }, memo')

end Cslib.Algorithms.Lean.CDCL
