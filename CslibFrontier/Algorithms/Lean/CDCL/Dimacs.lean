/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Watched
public import CslibFrontier.Logics.Propositional.CNF.Dimacs

/-! # The CDCL solver on DIMACS text

What the executable `lake exe cdcl` prints, apart from the statistics and times:
`Cslib.Algorithms.Lean.CDCL.answerDIMACS` reads a DIMACS CNF formula, solves it on renamed
variables (`Cslib.Algorithms.Lean.CDCL.solveCompactWith`), and gives the answer in the format of
the SAT competitions with MiniSat's exit code: `s SATISFIABLE` and the model on `v` lines, exit
code `10`, or `s UNSATISFIABLE` and the certificate, exit code `20`.

The model lists one literal for each variable occurring in the formula, in increasing order, and
ends with `0`: a formula without variables gets `v 0`, and a formula over the single DIMACS
variable `10⁶` gets one literal, not one for each smaller name.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.occurringVars`: the distinct variables of a formula.
* `Cslib.Algorithms.Lean.CDCL.modelLines`: the `v` lines of a model.
* `Cslib.Algorithms.Lean.CDCL.answerFor`, `Cslib.Algorithms.Lean.CDCL.answerDIMACS`: the answer
  for a formula, and for DIMACS text.

## Main statements

* `Cslib.Algorithms.Lean.CDCL.mem_occurringVars`, `Cslib.Algorithms.Lean.CDCL.nodup_occurringVars`,
  `Cslib.Algorithms.Lean.CDCL.pairwise_occurringVars`: the variable list passed to `modelLines`
  holds exactly the variables of the formula, each once, in increasing order. The `v` lines
  rendered from it are covered only by the checked examples.
* `Cslib.Algorithms.Lean.CDCL.satisfiable_of_answerFor_code`: exit code `10` only for a satisfiable
  formula.
* `Cslib.Algorithms.Lean.CDCL.checkLRAT_of_answerFor_cert`: the certificate given is accepted by
  the LRAT checker (`Cslib.Logic.PL.CNF.checkLRAT`).
* `Cslib.Algorithms.Lean.CDCL.answerDIMACS_toDIMACS`: on the text `φ.toDIMACS` that
  `Cslib.Logic.PL.CNF.toDIMACS` prints, the answer is that for `φ`, so
  `Cslib.Algorithms.Lean.CDCL.satisfiable_of_answerDIMACS_toDIMACS` and
  `Cslib.Algorithms.Lean.CDCL.checkLRAT_of_answerDIMACS_toDIMACS` conclude about `φ` itself. For a
  formula built in Lean and printed, the DIMACS parser is then outside the trusted base; for a file
  from elsewhere, the parser is still trusted to read it as intended.

The text itself (`modelLines` and the `s` lines) is output formatting, with no theorem about it.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- The variables occurring in `φ`, each once, in increasing order. -/
def occurringVars (φ : CNF ℕ) : List ℕ := (φ.vars.mergeSort (· ≤ ·)).eraseReps

/-- Erasing repeats keeps the elements: the worker of `List.eraseReps`, with `acc` the elements
kept so far, newest first, and `a` the last one seen. -/
private theorem mem_eraseRepsLoop {x a : ℕ} {as acc : List ℕ} :
    x ∈ List.eraseRepsBy.loop (· == ·) a as acc ↔ x ∈ acc ∨ x = a ∨ x ∈ as := by
  induction as generalizing a acc with
  | nil =>
    simp only [List.eraseRepsBy.loop, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false]
    exact or_comm
  | cons a' as ih =>
    unfold List.eraseRepsBy.loop
    by_cases h : a = a'
    · subst h
      rw [beq_self_eq_true, ih, List.mem_cons]
      tauto
    · rw [beq_eq_false_iff_ne.2 h, ih, List.mem_cons, List.mem_cons]
      tauto

/-- Erasing repeats from a sorted list leaves an increasing one: with `acc` decreasing below `a`
and `a :: as` sorted, the worker of `List.eraseReps` returns an increasing list. -/
private theorem pairwise_eraseRepsLoop {a : ℕ} {as acc : List ℕ}
    (hacc : (a :: acc).Pairwise (· > ·)) (has : (a :: as).Pairwise (· ≤ ·)) :
    (List.eraseRepsBy.loop (· == ·) a as acc).Pairwise (· < ·) := by
  induction as generalizing a acc with
  | nil =>
    rw [List.eraseRepsBy.loop, List.pairwise_reverse]
    exact hacc
  | cons a' as ih =>
    unfold List.eraseRepsBy.loop
    obtain ⟨hle, has'⟩ := List.pairwise_cons.1 has
    by_cases h : a = a'
    · subst h
      rw [beq_self_eq_true]
      exact ih hacc (List.pairwise_cons.2 ⟨fun b hb => hle b (List.mem_cons_of_mem _ hb),
        (List.pairwise_cons.1 has').2⟩)
    · rw [beq_eq_false_iff_ne.2 h]
      have hlt : a < a' := lt_of_le_of_ne (hle a' List.mem_cons_self) h
      refine ih (List.pairwise_cons.2 ⟨fun b hb => ?_, hacc⟩) has'
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hlt
      · exact lt_trans ((List.pairwise_cons.1 hacc).1 b hb) hlt

/-- Erasing repeats keeps the elements. -/
private theorem mem_eraseReps {x : ℕ} {l : List ℕ} : x ∈ l.eraseReps ↔ x ∈ l := by
  cases l with
  | nil => rfl
  | cons a as =>
    rw [List.eraseReps, List.eraseRepsBy, mem_eraseRepsLoop, List.mem_cons]
    simp only [List.not_mem_nil, false_or]

/-- Erasing repeats from a sorted list leaves an increasing one. -/
private theorem pairwise_eraseReps {l : List ℕ} (h : l.Pairwise (· ≤ ·)) :
    l.eraseReps.Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a as => exact pairwise_eraseRepsLoop (List.pairwise_singleton _ a) h

/-- **The variables passed to `modelLines` are those of the formula.** -/
theorem mem_occurringVars {φ : CNF ℕ} {v : ℕ} : v ∈ occurringVars φ ↔ v ∈ φ.vars := by
  rw [occurringVars, mem_eraseReps, List.mem_mergeSort]

/-- **The variables passed to `modelLines` increase**, so each appears once. -/
theorem pairwise_occurringVars (φ : CNF ℕ) : (occurringVars φ).Pairwise (· < ·) :=
  pairwise_eraseReps <| (List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
    (fun a b => by simpa using le_total a b) φ.vars).imp of_decide_eq_true

/-- **The variables passed to `modelLines` have no repeats.** -/
theorem nodup_occurringVars (φ : CNF ℕ) : (occurringVars φ).Nodup :=
  (pairwise_occurringVars φ).imp Nat.ne_of_lt

/-- The model `σ` on the variables `vs` as DIMACS literals on `v` lines of at most 80 characters,
the variable `v` as `v + 1`, negated where `σ` is false, and the final `0`. -/
def modelLines (σ : ℕ → Bool) (vs : List ℕ) : String := Id.run do
  let mut out := ""
  let mut line := "v"
  for v in vs do
    let lit := if σ v then s!" {v + 1}" else s!" -{v + 1}"
    if line.length + lit.length > 78 then
      out := out ++ line ++ "\n"
      line := "v"
    line := line ++ lit
  return out ++ line ++ " 0\n"

/-- The answer of the solver for a DIMACS formula. -/
structure DimacsAnswer where
  /-- The formula read. -/
  formula : CNF ℕ
  /-- The `s` line, and for a satisfiable formula the `v` lines. -/
  output : String
  /-- MiniSat's exit code: `10` for satisfiable, `20` for unsatisfiable. -/
  code : UInt32
  /-- The statistics of the solver. -/
  stats : Stats
  /-- The certificate, for an unsatisfiable formula. -/
  cert : Option (Array Std.Tactic.BVDecide.LRAT.IntAction)

/-- **The answer for a formula**, solved with the options `o` on renamed variables. -/
def answerFor (o : Options) (φ : CNF ℕ) : DimacsAnswer :=
  match solveCompactWith o φ with
  | (.sat σ, st) => ⟨φ, "s SATISFIABLE\n" ++ modelLines σ (occurringVars φ), 10, st, none⟩
  | (.unsat cert, st) => ⟨φ, "s UNSATISFIABLE\n", 20, st, some cert⟩

/-- **Exit code `10` only for a satisfiable formula.** -/
theorem satisfiable_of_answerFor_code {o : Options} {φ : CNF ℕ} (h : (answerFor o φ).code = 10) :
    φ.Satisfiable := by
  unfold answerFor at h
  split at h
  · rename_i σ st hs
    exact ⟨σ, solveCompactWith_sat (congrArg Prod.fst hs)⟩
  · simp at h

/-- **The certificate given is accepted by the LRAT checker.** -/
theorem checkLRAT_of_answerFor_cert {o : Options} {φ : CNF ℕ}
    {cert : Array Std.Tactic.BVDecide.LRAT.IntAction} (h : (answerFor o φ).cert = some cert) :
    φ.checkLRAT cert = true := by
  unfold answerFor at h
  split at h
  · cases h
  · rename_i cert' st hs
    cases h
    exact solveCompactWith_unsat (congrArg Prod.fst hs)

/-- **The answer for a DIMACS formula**, read by `Cslib.Logic.PL.CNF.ofDIMACS`; an error if the
text is not a DIMACS formula. -/
def answerDIMACS (o : Options) (text : String) : Except String DimacsAnswer :=
  return answerFor o (← CNF.ofDIMACS text)

/-- **The answer for a printed formula is the answer for the formula**: reading
`Cslib.Logic.PL.CNF.toDIMACS` gives the formula back (`Cslib.Logic.PL.CNF.ofDIMACS_toDIMACS`). -/
theorem answerDIMACS_toDIMACS (o : Options) (φ : CNF ℕ) :
    answerDIMACS o φ.toDIMACS = .ok (answerFor o φ) := by
  simp [answerDIMACS, CNF.ofDIMACS_toDIMACS, bind, Except.bind, pure, Except.pure]

/-- **Exit code `10` on the printed formula only for a satisfiable formula**, end to end: the
hypothesis is about the text `φ.toDIMACS`, the conclusion about `φ`. -/
theorem satisfiable_of_answerDIMACS_toDIMACS {o : Options} {φ : CNF ℕ} {a : DimacsAnswer}
    (h : answerDIMACS o φ.toDIMACS = .ok a) (hc : a.code = 10) : φ.Satisfiable := by
  rw [answerDIMACS_toDIMACS, Except.ok.injEq] at h
  exact satisfiable_of_answerFor_code (h ▸ hc)

/-- **A certificate given for the printed formula is accepted for the formula**, end to end, so
the formula is unsatisfiable (`Cslib.Logic.PL.CNF.not_satisfiable_of_checkLRAT`). -/
theorem checkLRAT_of_answerDIMACS_toDIMACS {o : Options} {φ : CNF ℕ} {a : DimacsAnswer}
    {cert : Array Std.Tactic.BVDecide.LRAT.IntAction} (h : answerDIMACS o φ.toDIMACS = .ok a)
    (hc : a.cert = some cert) : φ.checkLRAT cert = true := by
  rw [answerDIMACS_toDIMACS, Except.ok.injEq] at h
  exact checkLRAT_of_answerFor_cert (h ▸ hc)

end Cslib.Algorithms.Lean.CDCL
