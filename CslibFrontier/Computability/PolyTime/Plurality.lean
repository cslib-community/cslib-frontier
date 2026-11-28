/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Plurality
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time plurality

The multitape certificate for `Cslib.ProbComp.plurality` works on framed lists.
The scan compares the frequencies of the current and next candidates, retaining the current
candidate on ties. The accumulator is empty or holds one input element.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Plurality of a framed list takes polynomial time in its encoded length. The first
most frequent element wins, with a fixed fallback for the empty list. -/
@[fun_prop]
theorem plurality {α : Type} [DecidableEq α] (enc : α ↪ List Bool) (fallback : α) :
    ComputableInPolyTime (Cslib.ProbComp.plurality fallback) (encList enc) enc := by
  let step (xs : List α) : Option α → α → Option α :=
    List.argAux (fun next best => xs.count best < xs.count next)
  let encStep := encPair (encPair (encList enc) (encOption enc)) enc
  let encCompare := encPair encStep enc
  have htake : ComputableInPolyTime (fun p : (List α × Option α) × α => some p.2)
      encStep (encOption enc) :=
    (optionSome enc).comp (snd _ _)
  have hstep : ComputableInPolyTime (fun p : (List α × Option α) × α => step p.1.1 p.1.2 p.2)
      encStep (encOption enc) := by
    let hinput := fst encStep enc
    have hxs : ComputableInPolyTime (fun p : ((List α × Option α) × α) × α => p.1.1.1)
        encCompare (encList enc) :=
      ((fst (encList enc) (encOption enc)).comp (fst _ _)).comp hinput
    have hbest : ComputableInPolyTime (fun p : ((List α × Option α) × α) × α => p.2)
        encCompare enc := snd _ _
    have hcandidate : ComputableInPolyTime (fun p : ((List α × Option α) × α) × α => p.1.2)
        encCompare enc := (snd _ _).comp hinput
    have htest := unary_lt' (countWithInput hxs hbest) (countWithInput hxs hcandidate)
    have hcompare := htest.ite' (htake.comp hinput) ((optionSome enc).comp hbest)
    have hopt : ComputableInPolyTime (fun p : (List α × Option α) × α => p.1.2)
        encStep (encOption enc) :=
      (snd _ _).comp (fst _ _)
    have hchoose : ComputableInPolyTime (fun p : ((List α × Option α) × α) × α =>
        if p.1.1.1.count p.2 < p.1.1.1.count p.1.2 then some p.1.2 else some p.2)
        encCompare (encOption enc) := by
      simpa only [Function.comp_def, decide_eq_true_eq] using hcompare
    have hrun := optionElimWithInput (body := fun p best =>
      if p.1.1.count best < p.1.1.count p.2 then some p.2 else some best) hopt htake hchoose
    refine hrun.of_enc_eq fun p => ?_
    cases p.1.2 <;> simp [step, List.argAux]
  have hgrowth (xs : List α) (current : Option α) (next : α) (hn : next ∈ xs) :
      (encOption enc (step xs current next)).length ≤
        (encOption enc current).length + ((encList enc xs).length + 1) := by
    have hlen := SizedListEncoding.length_elem_le
      (encA := enc) (encL := encList enc) xs next hn
    cases current with
    | none => simp only [step, List.argAux, encOption_some, List.length_cons]; omega
    | some best =>
      simp only [step, List.argAux]
      split <;> simp only [encOption_some, List.length_cons] <;> omega
  have hfold := foldlWith_of_bounded_growth (encA := enc) (encL := encList enc)
    (par := id) (list := id) (init := fun _ => none) (step := step)
    id' id' (const none) hstep (PolyBounded.self.add (.const 1)) hgrowth
  exact (optionGetD enc).comp (hfold.prod (const fallback))

end Turing.MultiTapeTM.ComputableInPolyTime
