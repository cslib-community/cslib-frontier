/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
-- `#guard` runs the propagator, the checkers and a brute-force search at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! The knapsack propagator
(`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator`) for an ordinary client,
which imports the module without `import all`:

* the theorems applied to the propagator's output, and the definitions `Supported`,
  `propFormula` and `remClause` unfolded;
* `#guard` runs of the propagator: its removals agree with a brute-force search for the
  unsupported values, and the checker accepts its proof, with and without a preserved set, on
  boundary instances (no items, an infeasible constraint, fixed items, zero weights and profits,
  a capacity above the total weight) and on random instances of up to `8` items with random
  domains;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`
  (`opbText`), and a test-only printer of the proofs as kernel text (`pbpText`, as in
  `CslibFrontierTests.Logics.Propositional.VeriPBKnapsack`), whose output the text front end
  parses and accepts. VeriPB 3.0.2 and CakePB (cakepb `438b8f8`) report `s VERIFIED` on the
  printed texts of the instances `printCases`.

The kernel-checked client is
`CslibFrontierTests.Logics.Propositional.VeriPBKnapsackPropagatorDecide`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsackPropagator

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack

/-! ### The theorems for an ordinary client -/

/-- A removed value is unsupported. -/
example {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n) (b : Bool)
    (h : (j.val, b) ∈ (propagate w p C P dom).removed) : ¬ Supported w p C P dom j b :=
  ((mem_removed_iff w p C P dom j b).1 h).2

/-- A supported value of a free item is kept. -/
example {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n) (b : Bool)
    (h : Supported w p C P dom j b) : (j.val, b) ∉ (propagate w p C P dom).removed :=
  fun hm => ((mem_removed_iff w p C P dom j b).1 hm).2 h

/-- `Supported` unfolds: a supported value comes with a set of items that agrees with the domains,
takes `j` exactly when `b`, weighs at most `C` and earns at least `P`. -/
example {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n) (b : Bool)
    (h : Supported w p C P dom j b) :
    ∃ S : Finset (Fin n), (∀ i c, dom i = some c → (i ∈ S ↔ c = true)) ∧ (j ∈ S ↔ b = true) ∧
      ∑ i ∈ S, w i ≤ C ∧ P ≤ ∑ i ∈ S, p i := by
  obtain ⟨S, hd, hj, hw, hp⟩ := h
  exact ⟨S, hd, hj, hw, hp⟩

/-- `propFormula` unfolds: the knapsack constraint holds exactly when the items taken weigh at
most `C` and earn at least `P`. -/
example {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (σ : ℕ → Bool) :
    (∀ c ∈ propFormula w p C P, c.Holds σ) ↔
      ∑ i ∈ chosen n σ, w i ≤ C ∧ P ≤ ∑ i ∈ chosen n σ, p i := by
  simp [propFormula, holds_capacity_iff, holds_profitBound_iff]

/-- The proof derives the removal clause `D ⇒ xⱼ ≠ b` of every removed value: the checker reaches
a database holding it. -/
example {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n) (b : Bool)
    (h : (j.val, b) ∈ (propagate w p C P dom).removed) :
    ∃ s, runTop (propFormula w p C P) none
        (State.init (propFormula w p C P) none (some (List.range n)))
        (propagate w p C P dom).proof.steps = some s ∧
      ∃ k, lookup s.db k = some (remClause dom j b).normalize :=
  have ⟨s, hs, hrem⟩ := runTop_propagate w p C P dom
  ⟨s, hs, hrem j b h⟩

/-- The removal clause says `D ⇒ xⱼ ≠ b`. -/
example {n : ℕ} (dom : Fin n → Option Bool) (j : Fin n) (b : Bool) (σ : ℕ → Bool)
    (hD : ∀ i c, dom i = some c → σ i = c) (h : (remClause dom j b).Holds σ) : σ j ≠ b :=
  (holds_remClause_iff dom j b σ).1 h hD

/-! ### Evaluated runs -/

/-- The instance of the lists `ws`, `ps`, `ds`. -/
structure Case where
  ws : List ℕ
  ps : List ℕ
  C : ℕ
  P : ℕ
  ds : List (Option Bool)

/-- The propagator's output on a case. -/
def Case.out (c : Case) : Propagation :=
  propagate (fun i : Fin c.ws.length => c.ws.getD i 0) (fun i => c.ps.getD i 0) c.C c.P
    (fun i => c.ds.getD i none)

/-- The formula of a case. -/
def Case.formula (c : Case) : List PBConstr :=
  propFormula (fun i : Fin c.ws.length => c.ws.getD i 0) (fun i => c.ps.getD i 0) c.C c.P

/-- The checker accepts the proof, with the item variables preserved and without a preserved
set. -/
def Case.accepted (c : Case) : Bool :=
  checkRed c.formula none c.out.proof (some (List.range c.ws.length)) &&
    checkRed c.formula none c.out.proof

/-- The value `b` of item `j` is supported, by brute force over all sets of items. -/
def Case.supported (c : Case) (j : ℕ) (b : Bool) : Bool :=
  (List.range (2 ^ c.ws.length)).any fun m =>
    let σ := fun i => m.testBit i
    (List.range c.ws.length).all (fun i => (c.ds.getD i none).all (σ i == ·)) &&
      σ j == b &&
      decide (((List.range c.ws.length).map fun i => if σ i then c.ws.getD i 0 else 0).sum ≤
        c.C) &&
      decide (c.P ≤ ((List.range c.ws.length).map fun i => if σ i then c.ps.getD i 0 else 0).sum)

/-- The values the propagator should remove: those in the domains and unsupported. -/
def Case.expected (c : Case) : List (ℕ × Bool) :=
  (List.range c.ws.length).flatMap fun j =>
    ([false, true].filter fun b => (c.ds.getD j none).all (· == b) && !c.supported j b).map
      fun b => (j, b)

/-- The run is accepted and removes exactly the expected values. -/
def Case.agrees (c : Case) : Bool :=
  c.accepted && c.out.removed.all (c.expected.contains ·) &&
    c.expected.all (c.out.removed.contains ·)

/-- The boundary and hand-made cases. -/
def cases : List Case :=
  [⟨[], [], 0, 0, []⟩, ⟨[], [], 0, 1, []⟩,
    ⟨[3, 4, 5, 2], [4, 5, 6, 3], 7, 9, [none, some true, none, none]⟩,
    ⟨[3, 4, 5, 2], [4, 5, 6, 3], 7, 9, [none, none, none, none]⟩,
    ⟨[3, 4, 5], [4, 5, 6], 2, 9, [none, none, none]⟩,
    ⟨[0, 3, 0, 2], [1, 0, 0, 2], 3, 3, [none, none, some false, none]⟩,
    ⟨[2, 3, 4], [3, 4, 5], 100, 0, [none, none, none]⟩,
    ⟨[2, 3, 4], [3, 4, 5], 100, 12, [none, none, none]⟩,
    ⟨[5, 4, 6, 3, 7], [10, 40, 30, 50, 35], 12, 90, [none, none, none, none, none]⟩]

#guard cases.all Case.agrees

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- A random case of `m` items from the seed `s`: weights and profits in `[0, 9]`, each domain
free with probability `3/5`, and a capacity and a profit bound around half the totals. -/
def randCase (s m : ℕ) : Case :=
  let r := (List.range m).foldl (fun (s, ws, ps, ds) _ =>
    let s₁ := lcg s
    let s₂ := lcg s₁
    let s₃ := lcg s₂
    let d := match s₃ / 65536 % 5 with
      | 0 => some false
      | 1 => some true
      | _ => none
    (s₃, (s₁ / 65536 % 10) :: ws, (s₂ / 65536 % 10) :: ps, d :: ds)) (s, [], [], [])
  let (_, ws, ps, ds) := r
  ⟨ws, ps, ws.sum / 2 + s % 3, ps.sum / 2 + s % 4, ds⟩

#guard (List.range 60).all fun s => (randCase s (s % 9)).agrees

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

/-- A top-level step, in the fragment the propagator writes. -/
def stepText : TopStep → String
  | .step (.pol ops) => s!"pol {" ".intercalate (ops.map opText)} ;\n"
  | .step (.rup c hs) =>
    s!"rup {constrText c} : " ++
      " ".intercalate (hs.map fun | .neg => "~" | .id k => toString k) ++ " ;\n"
  | .red c ω (some []) none => s!"red {constrText c} : {witnessText ω} : subproof\nqed ;\n"
  | _ => "unsupported ;\n"

/-- A proof without a conclusion for a formula of `m` constraints, in the kernel format. -/
def pbpText (m : ℕ) (P : RedProof) : String :=
  s!"pseudo-Boolean proof version 3.0\nf {m} ;\n" ++ String.join (P.steps.map stepText) ++
    "output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n"

/-- The formula of a case as OPB text, by the library's printer. -/
def Case.opbText (c : Case) : String := Text.printOPB ⟨c.formula, none, none⟩

/-- The proof of a case as kernel text. -/
def Case.proofText (c : Case) : String := pbpText 2 c.out.proof

/-- The text front end accepts the printed proof against the printed formula. -/
def Case.textAgrees (c : Case) : Bool :=
  Text.checkOPB c.opbText c.proofText == some .noClaim

/-- The cases whose texts were checked by VeriPB and CakePB. -/
def printCases : List Case := cases ++ [randCase 17 8, randCase 25 7, randCase 44 8]

#guard printCases.all Case.textAgrees

/-- Write the texts of `printCases` to `dir`, for the external checkers. -/
def writeCases (dir : System.FilePath) : IO Unit := do
  for (c, k) in printCases.zipIdx do
    IO.FS.writeFile (dir / s!"prop{k}.opb") c.opbText
    IO.FS.writeFile (dir / s!"prop{k}.pbp") c.proofText

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsackPropagator
