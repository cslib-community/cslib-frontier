/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Tactic.LRATTauto
import Mathlib.Tactic.Tauto
import Lean.Elab.Frontend

/-!
# Benchmarks of `lrat_tauto`

Elaborates families of propositional tautologies with `lrat_tauto`, which generates its
certificate with the CDCL solver, and with Mathlib's `tauto`. For `lrat_tauto` it prints the
clauses of the formula refuted, the steps of the solver's certificate before and after trimming,
the time to generate and trim it, the time the kernel took to check it, and the time of the whole
elaboration; for `tauto`, the time of the whole elaboration, or the error when it fails, as when it
exceeds `maxHeartbeats` (here `400000`, twice the default; `lrat_tauto` runs without a
limit).

The families, over the atoms `p i`, `a i` and `b i`:

* `chain n`: `(p 0 → p 1) → … → (p (n - 2) → p (n - 1)) → p 0 → p (n - 1)`;
* `php n`: the pigeonhole principle for `n + 1` pigeons and `n` holes;
* `dist n`: `(a 0 ∨ b 0) ∧ … ∧ (a (n - 1) ∨ b (n - 1))` implies the disjunction of the `2 ^ n`
  conjunctions choosing `a i` or `b i` for each `i`;
* `iff n`: the left- and right-associated `↔` of `p 0, …, p (n - 1)` are equivalent.

Times are wall-clock milliseconds on the machine running the script, with Lean's interpreter
running the solver; they compare the runs with each other only. Run it with

```
lake env lean --run scripts/LRATTautoBench.lean [quick]
```
-/

open Lean Elab

namespace LRATTautoBench

/-- `xs` joined by `sep`, in parentheses when there are several. -/
def join (sep : String) (xs : List String) : String :=
  match xs with
  | [x] => x
  | _ => "(" ++ s!" {sep} ".intercalate xs ++ ")"

/-- The chain of `n` implications. -/
def chain (n : ℕ) : String :=
  let steps := (List.range (n - 1)).map fun i => s!"(p {i} → p {i + 1}) → "
  s!"∀ p : Fin {n} → Prop, {String.join steps}p 0 → p {n - 1}"

/-- The pigeonhole principle for `n + 1` pigeons and `n` holes. -/
def php (n : ℕ) : String :=
  let pigeons := List.range (n + 1)
  let holes := List.range n
  let placed := pigeons.map fun i => join "∨" (holes.map fun j => s!"p {i} {j}") ++ " → "
  let shared := holes.flatMap fun j => pigeons.flatMap fun i =>
    (pigeons.filter (i < ·)).map fun k => s!"(p {i} {j} ∧ p {k} {j})"
  s!"∀ p : Fin {n + 1} → Fin {n} → Prop, {String.join placed}{join "∨" shared}"

/-- Distributivity of `∧` over `∨` on `n` disjunctions. -/
def dist (n : ℕ) : String :=
  let idx := List.range n
  let choices := (List.range (2 ^ n)).map fun s =>
    join "∧" (idx.map fun i => if s.testBit i then s!"a {i}" else s!"b {i}")
  s!"∀ a b : Fin {n} → Prop, {join "∧" (idx.map fun i => s!"(a {i} ∨ b {i})")} → \
    {join "∨" choices}"

/-- The associativity of `↔` on `n` atoms. -/
def iffAssoc (n : ℕ) : String :=
  let atoms := (List.range n).map fun i => s!"p {i}"
  let left := atoms.tail.foldl (fun acc a => s!"({acc} ↔ {a})") atoms.head!
  let right := atoms.dropLast.foldr (fun a acc => s!"({a} ↔ {acc})") atoms.getLast!
  s!"∀ p : Fin {n} → Prop, {left} ↔ {right}"

/-- Elaborates the commands `src` in `env`, returning the milliseconds taken and the messages. -/
def run (env : Environment) (src : String) : IO (ℕ × List String) := do
  let opts := Elab.async.set ({} : Options) false
  let start ← IO.monoMsNow
  let (_, log) ← Elab.process src env opts
  let stop ← IO.monoMsNow
  let msgs ← log.toArray.toList.mapM fun m => do
    let text ← m.data.toString
    return s!"{if m.severity == .error then "error: " else ""}{text.replace "\n" " "}"
  return (stop - start, msgs)

/-- The figure after `key` in a message, such as the milliseconds after `"; "`. -/
def figure (msgs : List String) (before after : String) : String :=
  msgs.findSome? (fun m => do
    let rest := (m.splitOn before)[1]?
    let r ← rest
    (r.splitOn after).head?) |>.getD "?"

/-- One row of the table: a goal proved by `lrat_tauto` and by `tauto`. -/
def row (env : Environment) (name : String) (goal : String) : IO Unit := do
  let (lt, lmsgs) ← run env
    s!"set_option maxHeartbeats 0 in\nset_option trace.lrat_tauto true in\n\
    example : {goal} := by lrat_tauto"
  let ok := !lmsgs.any (·.startsWith "error")
  let clauses := figure lmsgs "[lrat_tauto] " " clauses"
  let steps := figure lmsgs "certificate has " " steps"
  let trimmed := figure lmsgs "steps, " " after"
  let solveMs := figure lmsgs "trimming; " " ms"
  let kernelMs := figure lmsgs "certificate in " " ms"
  let (tt, tmsgs) ← run env
    s!"set_option maxHeartbeats 400000 in\nexample : {goal} := by tauto"
  let tauto := match tmsgs.find? (·.startsWith "error") with
    | some e => s!"fails after {tt} ({(e.take 40).toString}…)"
    | none => s!"{tt}"
  IO.println s!"| {name} | {clauses} | {steps} | {trimmed} | {solveMs} | {kernelMs} | \
    {if ok then toString lt else "error"} | {tauto} |"
  unless ok do IO.eprintln s!"{name}: {lmsgs}"
  (← IO.getStdout).flush

end LRATTautoBench

open LRATTautoBench in
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `CslibFrontier.Tactic.LRATTauto },
    { module := `Mathlib.Tactic.Tauto }] {} (loadExts := true)
  let quick := args.contains "quick"
  IO.println "| goal | clauses | steps | trimmed | solve ms | kernel ms | lrat_tauto ms | \
    tauto ms |"
  IO.println "|---|---|---|---|---|---|---|---|"
  for n in if quick then [10] else [10, 20, 40, 80] do row env s!"chain {n}" (chain n)
  for n in if quick then [2, 3] else [2, 3, 4, 5] do row env s!"php {n}" (php n)
  for n in if quick then [2, 3] else [2, 3, 4, 5] do row env s!"dist {n}" (dist n)
  for n in if quick then [3] else [3, 4, 5] do row env s!"iff {n}" (iffAssoc n)
