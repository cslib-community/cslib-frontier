/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Initial
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Execution

/-!
# Executing the CNF terminal

The terminal evaluates the matrix, converts its value and the try signal to red, and returns
satisfaction through an AND vertex [HearnDemaine2005, Section 3.1]. Its literal continuations
end in unconstrained pairs. An explicit successful configuration and creation-order activation
give a path from the inactive terminal with the same inputs. The final move reverses only sat;
all preceding moves are internal. Reversing the path resets the terminal for a second call.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Matrix.Evaluation.evalTerminalBase`: an explicit evaluation of the
  network, return gate and literal caps.
* `Cslib.Complexity.NCL.QBF.Matrix.Evaluation.idle`: the inactive terminal with trying in and
  the prescribed literal inputs.

## Main results

* `Cslib.Complexity.NCL.QBF.Matrix.Evaluation.reachable_sat`: a satisfied matrix has an actual
  terminal execution that fixes trying and every literal direction throughout.
* `Cslib.Complexity.NCL.QBF.Matrix.Evaluation.reachable_sat_iff`: with these directions fixed,
  success from the inactive terminal is equivalent to matrix truth.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Matrix.Evaluation

open Diagram Gate Network

local notation "B" => Color.blue

/-- Try is active; a true matrix value permits either direction of the returned sat wire. -/
@[expose] def evalReturn (sat value : Bool) (h : sat = false → value = true) :
    Realization Gate.interp returnGate [sat, true, value] [] where
  orient := fun e => ([1, 3] ++ (if sat then [0] else []) ++
    (if value then [2, 5] else [])).contains (returnGate.num e)
  legal := by
    cases sat with
    | false =>
      have hv := h rfl
      subst value
      decide +kernel
    | true => cases value <;> decide +kernel
  top_eq := by cases sat <;> cases value <;> decide +kernel
  bot_eq := rfl

/-- End arbitrary literal directions in unconstrained red pairs. -/
@[expose] def evalCaps : (p : ℕ) → (ls : List Bool) → ls.length = 2 * p →
    Realization Gate.interp (caps [] p) ls []
  | 0, [], _ => .id [] [] rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | _ + 1, [_], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | p + 1, x :: y :: ls, h =>
    (show Realization Gate.interp (gen cap) [x, y] [] from
      { orient := Sum.elim (fun i => if i.val = 0 then x else y) Fin.elim0
        legal := by cases x <;> cases y <;> decide +kernel
        top_eq := rfl
        bot_eq := rfl }).tensor (evalCaps p ls (by simp only [List.length_cons] at h; omega))

/-- Evaluate the actual terminal on arbitrary literal inputs. Its return sat may point up
when the matrix evaluates to true; trying remains active. -/
@[expose] def evalTerminalBase (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) (sat : Bool) (h : sat = false → ms.all (hits · ls) = true) :
    Realization Gate.interp (terminalBase p ms) ([sat, true] ++ ls) [] := by
  have hn : Realization Gate.interp (network [] (2 * p) ms) ls
      (ls ++ [ms.all (hits · ls)]) := by
    rw [← hl]
    simpa only [List.append_nil] using evalNetwork [] [] rfl ls ms
  have hm : Realization Gate.interp (moveLeft (bundle (2 * p)) B [])
      (ls ++ [ms.all (hits · ls)]) (ms.all (hits · ls) :: ls) := by
    simpa only [List.append_nil] using
      Realization.moveLeft (I := Gate.interp) B (ms.all (hits · ls)) [] [] rfl
        (bundle (2 * p)) ls (by simpa only [bundle, List.length_replicate] using hl)
  have hi := Realization.id (I := Gate.interp) [B, B] [sat, true] rfl
  exact ((hi.tensor hn).comp (hi.tensor hm)).comp ((evalReturn sat _ h).tensor (evalCaps p ls hl))

private theorem evalReturn_inner (sat value : Bool) (h : sat = false → value = true) :
    ∀ e : returnGate.Inner,
      (evalReturn sat value h).orient (.inr e) =
        (evalReturn true value (by simp)).orient (.inr e) := by
  dsimp only [evalReturn]
  cases sat <;> cases value <;> decide +kernel

private theorem evalTerminalBase_inner (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) (sat : Bool) (h : sat = false → ms.all (hits · ls) = true)
    (e : (terminalBase p ms).Inner) :
    (evalTerminalBase p ls hl ms sat h).orient (.inr e) =
      (evalTerminalBase p ls hl ms true (by simp)).orient (.inr e) := by
  rcases e with ((e | _) | (e | _)) | (e | _)
  · exact e.elim
  · rfl
  · exact e.elim
  · rfl
  · exact evalReturn_inner sat _ h e
  · rfl

private theorem evalTerminalBase_sat (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) (h : ms.all (hits · ls) = true) :
    (evalTerminalBase p ls hl ms false (fun _ => h)).orient =
      reverse (evalTerminalBase p ls hl ms true (by simp)).orient (.inl ⟨0, by simp⟩) := by
  funext e
  rcases e with i | e
  · by_cases hi : i.val = 0
    · rw [← show i = ⟨0, by simp⟩ from Fin.ext hi, reverse_self, Realization.orient_top,
        Realization.orient_top]
      simp [hi]
    · rw [reverse_of_ne _ (fun he => hi (congrArg (fun e => e.elim Fin.val fun _ => 0) he)),
        Realization.orient_top, Realization.orient_top]
      rcases hn : i.val with _ | _
      · exact (hi hn).elim
      · simp
  · rw [reverse_of_ne _ (by simp)]
    exact evalTerminalBase_inner p ls hl ms false (fun _ => h) e

/-- Clear all created terminal wires, retaining sat down, trying in, and the literal inputs. -/
@[expose] def idle (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p) (ms : List (List Bool)) :
    (terminalBase p ms).Edge → Bool :=
  (terminalBase p ms).off (evalTerminalBase p ls hl ms true (by simp)).orient

@[simp] theorem topList_idle (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) : (terminalBase p ms).topList (idle p ls hl ms) = [true, true] ++ ls :=
  (evalTerminalBase p ls hl ms true (by simp)).top_eq

/-- The inactive terminal is legal for every literal input, including unsatisfied matrices. -/
theorem legal_idle (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p) (ms : List (List Bool)) :
    ((terminalBase p ms).graph Gate.interp).Legal (idle p ls hl ms) := by
  refine legal_top_mono Gate.interp_forward _ (Initial.terminalBase p ms).legal (fun i => ?_)
    fun e => (congrFun (Initial.terminalBase_off p ms) (.inr e)).symm
  have htail (xs : List Bool) : List.Forall₂ (· ≤ ·) (List.replicate xs.length false) xs := by
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (Bool.false_le x) ih
  have hb : List.Forall₂ (· ≤ ·)
      ((terminalBase p ms).topList (Initial.terminalBase p ms).orient)
      ((terminalBase p ms).topList (evalTerminalBase p ls hl ms true (by simp)).orient) := by
    rw [(Initial.terminalBase p ms).top_eq, (evalTerminalBase p ls hl ms true (by simp)).top_eq]
    simpa only [Initial.controls, bundle, List.length_append, List.length_replicate,
      List.length_nil, Nat.add_zero, List.cons_append, List.nil_append, ← hl] using
      List.Forall₂.cons le_rfl (.cons (Bool.false_le true) (htail ls))
  unfold topList at hb
  have hget := hb.get (by simpa only [List.length_ofFn] using i.isLt)
    (by simpa only [List.length_ofFn] using i.isLt)
  change (Initial.terminalBase p ms).orient (.inl i) ≤
    (evalTerminalBase p ls hl ms true (by simp)).orient (.inl i)
  simpa only [List.get_ofFn, Function.comp_apply, Fin.cast_mk, Fin.eta] using hget

/-- Activate the terminal internally while fixing all boundary directions. -/
theorem prepare (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p) (ms : List (List Bool)) :
    InnerReach Gate.interp (terminalBase p ms) (idle p ls hl ms)
      (evalTerminalBase p ls hl ms true (by simp)).orient := by
  refine innerReach_of_le Gate.interp_forward _ (legal_idle p ls hl ms)
    (evalTerminalBase p ls hl ms true (by simp)).legal
    (Sum.rec (fun _ => le_rfl) fun _ => Bool.false_le _) ?_
  rintro e (⟨_, rfl⟩ | ⟨j, rfl⟩)
  · rfl
  · exact Fin.elim0 j

/-- A true matrix reverses the terminal's sat wire. All moves fix try and every literal input;
the whole path can be reversed for the next call. -/
theorem reachable_sat (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) (h : ms.all (hits · ls) = true) :
    ((terminalBase p ms).graph Gate.interp).ReachableOn
      (AllowsTop 0) (idle p ls hl ms)
      (evalTerminalBase p ls hl ms false (fun _ => h)).orient :=
  (Relation.ReflTransGen.mono
    (fun _ _ ⟨hs, ht, e, he, hend⟩ => ⟨hs, ht, e, fun i _ hi => he (Or.inl ⟨i, hi⟩), hend⟩) _ _
    (prepare p ls hl ms)).tail
    ⟨(evalTerminalBase p ls hl ms true (by simp)).legal,
      (evalTerminalBase p ls hl ms false (fun _ => h)).legal, .inl ⟨0, by simp⟩,
      (allowsTop_inl _ _).2 rfl, evalTerminalBase_sat p ls hl ms h⟩

/-- With trying and all literals fixed, terminal success is equivalent to matrix truth. -/
theorem reachable_sat_iff (p : ℕ) (ls : List Bool) (hl : ls.length = 2 * p)
    (ms : List (List Bool)) :
    (∃ t, ((terminalBase p ms).graph Gate.interp).ReachableOn
      (AllowsTop 0) (idle p ls hl ms) t ∧
      t (.inl ⟨0, by simp⟩) = false) ↔ ms.all (hits · ls) = true := by
  refine ⟨?_, fun h => ⟨_, reachable_sat p ls hl ms h, by rw [Realization.orient_top]; rfl⟩⟩
  rintro ⟨t, ht, hsat⟩
  have htop := topList_of_reachableOn ht (topList_idle p ls hl ms)
  rw [hsat] at htop
  have hc := holds_terminal [] p ms t (ht.reachable.legal (legal_idle p ls hl ms))
  rw [show (terminal p [] ms).topList t = [false, true] ++ ls from htop] at hc
  exact (hc rfl).2

end Cslib.Complexity.NCL.QBF.Matrix.Evaluation
