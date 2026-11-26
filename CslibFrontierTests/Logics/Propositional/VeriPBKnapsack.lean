/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP
import Mathlib.Data.Fin.VecNotation
-- `#guard` runs the dynamic program, the checkers and `profitDP` at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP

/-! Certified knapsack (`CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack`) for an
ordinary client, which imports the module without `import all`:

* the end-to-end theorem applied to an accepted proof, and the encoding theorems on an instance;
* `#guard` runs of the checker on the proofs of the dynamic program: they are accepted, their
  optimum agrees with `Cslib.Algorithms.Lean.Knapsack.profitDP`, and a proof claiming a larger
  or a smaller optimum is rejected; on boundary instances (no items, capacity `0`, items heavier
  than the capacity, zero weights and profits, a capacity above the total weight) and on random
  instances of up to `20` items;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`
  (`opbText`), and a test-only printer of the proofs as kernel text (`pbpText`), whose output the
  text front end parses and accepts with the same conclusion. VeriPB 3.0.2 and
  CakePB (cakepb `438b8f8`) report `s VERIFIED BOUNDS` on the printed texts of the instances
  below, as written out by `printCases`.

The kernel-checked client is `CslibFrontierTests.Logics.Propositional.VeriPBKnapsackDecide`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsack

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack

/-! ### The theorems for an ordinary client -/

/-- Acceptance of the proof of the dynamic program gives the optimum. -/
example {n : ℕ} (w p : Fin n → ℕ) (B : ℕ)
    (h : checkRed (formula w B) (some (objective p)) (certify w p B).proof = true) :
    ∀ S : Finset (Fin n), ∑ i ∈ S, w i ≤ B → ∑ i ∈ S, p i ≤ (certify w p B).optimum :=
  fun S hS => (isGreatest_of_checkRed_certify h).2 ⟨S, hS, rfl⟩

/-- The encoding on an instance: taking the items `0` and `2`, of weight `2 + 4 > 5`, violates
the capacity, and the objective value is `-(3 + 5)`. -/
example : ¬ (capacity ![2, 3, 4] 5).Holds (fun v => v == 0 || v == 2) ∧
    (objective ![3, 4, 5]).eval (fun v => v == 0 || v == 2) = -8 := by
  rw [holds_capacity_iff, eval_objective]
  decide

/-! ### Evaluated runs -/

/-- Run the dynamic program on the weights `ws`, the profits `ps` and the capacity `B`: its
optimum, whether the checker accepts its proof, and the profit of `profitDP`'s selection. -/
def run (ws ps : List ℕ) (B : ℕ) : ℕ × Bool × ℕ :=
  let w : Fin ws.length → ℕ := fun i => ws.getD i 0
  let p : Fin ws.length → ℕ := fun i => ps.getD i 0
  let c := certify w p B
  (c.optimum, checkRed (formula w B) (some (objective p)) c.proof,
    ((Cslib.Algorithms.Lean.Knapsack.profitDP w p B (List.finRange ws.length)).map p).sum)

/-- The run is accepted and agrees with `profitDP`. -/
def agrees (ws ps : List ℕ) (B : ℕ) : Bool :=
  let (k, ok, k') := run ws ps B
  ok && k == k'

/-- The proof of the dynamic program with its conclusion changed to the optimum `k + d`. -/
def shifted (ws ps : List ℕ) (B : ℕ) (d : ℤ) : Bool :=
  let w : Fin ws.length → ℕ := fun i => ws.getD i 0
  let p : Fin ws.length → ℕ := fun i => ps.getD i 0
  let c := certify w p B
  match c.proof.conclusion with
  | .bounds _ q _ _ =>
    checkRed (formula w B) (some (objective p))
      ⟨c.proof.steps, .bounds (some (-(c.optimum + d))) q (some (-(c.optimum + d))) none⟩
  | _ => false

#guard run [] [] 0 == (0, true, 0)
#guard run [2, 3, 4] [3, 4, 5] 0 == (0, true, 0)
#guard run [6, 7] [5, 9] 5 == (0, true, 0)
#guard run [2, 3, 4] [3, 4, 5] 5 == (7, true, 7)
#guard run [0, 3, 4, 1] [3, 0, 5, 2] 5 == (10, true, 10)
#guard run [2, 3, 4] [3, 4, 5] 100 == (12, true, 12)
#guard run [5, 4, 6, 3, 7, 2, 8] [10, 40, 30, 50, 35, 40, 30] 15 == (160, true, 160)

-- A wrong optimum is rejected, above or below the true one.
#guard !shifted [2, 3, 4] [3, 4, 5] 5 1
#guard !shifted [2, 3, 4] [3, 4, 5] 5 (-1)
#guard shifted [2, 3, 4] [3, 4, 5] 5 0

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `m` random items with weights and profits in `[1, 10]`, from the seed `s`. -/
def randItems (s m : ℕ) : List ℕ × List ℕ :=
  ((List.range m).foldl (fun (s, ws, ps) _ =>
    let s₁ := lcg s
    let s₂ := lcg s₁
    (s₂, (s₁ / 65536 % 10 + 1) :: ws, (s₂ / 65536 % 10 + 1) :: ps)) (s, [], [])).2

#guard (List.range 40).all fun s =>
  let (ws, ps) := randItems s (s % 12)
  agrees ws ps (s * 7 % 40)

#guard let (ws, ps) := randItems 7 20; agrees ws ps 40

/-! ### Kernel text -/

/-- The name of a literal. -/
def litText (l : Literal ℕ) : String := (if l.2 then "x" else "~x") ++ toString (l.1 + 1)

/-- A constraint `a₁ ℓ₁ … >= d`. -/
def constrText (c : PBConstr) : String :=
  String.join (c.terms.map fun t => s!"{t.1} {litText t.2} ") ++ s!">= {c.degree}"

/-- A witness `x -> 0 …`. -/
def witnessText (ω : Witness) : String :=
  " ".intercalate (ω.map fun e => s!"x{e.1 + 1} -> " ++ match e.2 with
    | .zero => "0"
    | .one => "1"
    | .lit l => litText l)

/-- The operations of a `pol` step. -/
def opText : PolOp → String
  | .id k => toString k
  | .lit l => litText l
  | .add => "+"
  | .mul k => s!"{k} *"
  | .div k => s!"{k} d"
  | .sat => "s"
  | .weaken v => s!"x{v + 1} w"

/-- A top-level step, in the fragment the dynamic program writes. -/
def stepText : TopStep → String
  | .step (.pol ops) => s!"pol {" ".intercalate (ops.map opText)} ;\n"
  | .step (.rup c hs) =>
    s!"rup {constrText c} : " ++
      " ".intercalate (hs.map fun | .neg => "~" | .id k => toString k) ++ " ;\n"
  | .red c ω (some []) none => s!"red {constrText c} : {witnessText ω} : subproof\nqed ;\n"
  | .soli ρ => s!"soli {" ".intercalate (ρ.map litText)} ;\n"
  | .deld ids => s!"deld {" ".intercalate (ids.map toString)} ;\n"
  | _ => "unsupported ;\n"

/-- An optional bound, `INF` for none. -/
def boundText : Option ℤ → String
  | some b => toString b
  | none => "INF"

/-- A proof for a formula of `m` constraints, in the kernel format. -/
def pbpText (m : ℕ) (P : RedProof) : String :=
  s!"pseudo-Boolean proof version 3.0\nf {m} ;\n" ++ String.join (P.steps.map stepText) ++
    "output NONE ;\n" ++
    (match P.conclusion with
      | .bounds lb q ub none => s!"conclusion BOUNDS {boundText lb} : {q} {boundText ub} ;\n"
      | _ => "conclusion NONE ;\n") ++
    "end pseudo-Boolean proof ;\n"

/-- The knapsack instance as OPB text, by the library's printer. -/
def opbText (ws ps : List ℕ) (B : ℕ) : String :=
  let w : Fin ws.length → ℕ := fun i => ws.getD i 0
  let p : Fin ws.length → ℕ := fun i => ps.getD i 0
  Text.printOPB ⟨formula w B, some (objective p), none⟩

/-- The proof of the dynamic program as kernel text. -/
def proofText (ws ps : List ℕ) (B : ℕ) : String :=
  pbpText 1 (certify (fun i : Fin ws.length => ws.getD i 0) (fun i => ps.getD i 0) B).proof

/-- The text front end accepts the printed proof against the printed instance, with the
conclusion `BOUNDS -k : q -k` of the dynamic program. -/
def textAgrees (ws ps : List ℕ) (B : ℕ) : Bool :=
  let c := certify (fun i : Fin ws.length => ws.getD i 0) (fun i => ps.getD i 0) B
  Text.checkOPB (opbText ws ps B) (pbpText 1 c.proof) == some c.proof.conclusion

/-- The instances whose texts were checked by VeriPB and CakePB. -/
def printCases : List (List ℕ × List ℕ × ℕ) :=
  [([], [], 0), ([2, 3, 4], [3, 4, 5], 0), ([6, 7], [5, 9], 5), ([2, 3, 4], [3, 4, 5], 5),
    ([0, 3, 4, 1], [3, 0, 5, 2], 5), ([2, 3, 4], [3, 4, 5], 100),
    ([5, 4, 6, 3, 7, 2, 8], [10, 40, 30, 50, 35, 40, 30], 15),
    let (ws, ps) := randItems 7 20; (ws, ps, 40)]

#guard printCases.all fun (ws, ps, B) => textAgrees ws ps B

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsack
