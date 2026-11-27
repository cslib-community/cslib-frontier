/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrickProof
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBProofText
-- `#guard` runs the propagator, the checkers and a brute-force search at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrickProof
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! The two-equality knapsack propagator
(`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrick`) for an ordinary client:

* the theorems applied to the propagator's output;
* `#guard` runs of the propagator: its removals agree with a brute-force search for the
  unsupported values of the items, the weight and the profit, and the checker accepts its proof,
  on boundary instances (no items, an empty domain, values out of every current domain, zero
  weights and profits) and on random instances of up to `3` items;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`,
  and the proofs printed as kernel text by the test-only printer
  `CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`, whose output the text front end
  parses and accepts. VeriPB 3.0.2 and CakePB report `s VERIFIED` on the printed texts of the
  instances `printCases`.

The kernel-checked client is `CslibFrontierTests.Logics.Propositional.VeriPBKnapsackTrickDecide`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBKnapsackTrick

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Knapsack.Trick
open CslibFrontierTests.Logics.Propositional.VeriPBProofText (pbpText)

/-! ### The theorems for an ordinary client -/

/-- The checker accepts every proof of the propagator. -/
example (I : Inst) : checkRed I.formula none I.propagate.proof (some I.pres) = true :=
  I.checkRed_propagate

/-- A removed value of an item is unsupported. -/
example (I : Inst) {j k : ℕ} (h : (j, k) ∈ I.propagate.removed) : ¬ I.SupportedN j k :=
  (I.mem_removed_iff.1 h).2.2

/-- A supported value of the weight in its current domain is kept. -/
example (I : Inst) {k : ℕ} (h : I.SupportedS false k) : k ∉ I.propagate.removedW :=
  fun hm => (I.mem_removedW_iff.1 hm).2 h

/-- The proof derives the removal clause `D ⇒ [xⱼ ≠ v]` of every removed item value: the checker
reaches a database holding it. -/
example (I : Inst) {j k : ℕ} (h : (j, k) ∈ I.propagate.removed) :
    ∃ s, runTop I.formula none (State.init I.formula none (some I.pres))
        I.propagate.proof.steps = some s ∧
      ∃ m, lookup s.db m = some (I.remClause j k).normalize :=
  have ⟨s, hs, hrem, _⟩ := I.runTop_propagate
  ⟨s, hs, hrem j k h⟩

/-- The removal clause says `D ⇒ [xⱼ ≠ v]`. -/
example (I : Inst) {j k : ℕ} (σ : ℕ → Bool) (hD : Consistent σ I.antecedent)
    (h : (I.remClause j k).Holds σ) : σ (I.var j k) = false :=
  (I.holds_remClause_iff j k σ).1 h hD

/-- The solutions of the encoding under the antecedent pick values of the current domains. -/
example (I : Inst) (σ : ℕ → Bool) (hF : ∀ c ∈ I.formula, c.Holds σ)
    (hD : Consistent σ I.antecedent) : ∃ c, I.Solution c := by
  obtain ⟨c, kw, kp, hc, hkw, hkp, hw, hp, -⟩ := (I.holds_formula_iff σ).1 ⟨hF, hD⟩
  exact ⟨c, hc, ⟨kw, hkw, hw⟩, kp, hkp, hp⟩

/-- `SupportedN` and `SupportedS` unfold: a supported value comes with a choice of positions of
the current domains whose weight and profit are values of the current domains of `W` and `P`. -/
example (I : Inst) {j k : ℕ} (h : I.SupportedN j k) :
    j < I.n ∧ ∃ c : ℕ → ℕ, (∀ i < I.n, c i ∈ livePos (I.dom i)) ∧ c j = k ∧
      (∃ kw ∈ livePos I.wDom, dval I.wDom kw = ((List.range I.n).map fun i => I.cw i (c i)).sum) ∧
      ∃ kp ∈ livePos I.pDom, dval I.pDom kp = ((List.range I.n).map fun i => I.cp i (c i)).sum := by
  obtain ⟨hj, c, ⟨hc, hw, hp⟩, hcj⟩ := h
  exact ⟨hj, c, hc, hcj, hw, hp⟩

example (I : Inst) {k : ℕ} (h : I.SupportedS true k) :
    k ∈ livePos I.pDom ∧ ∃ c : ℕ → ℕ, I.Solution c ∧
      dval I.pDom k = ((List.range I.n).map fun i => I.cp i (c i)).sum := by
  obtain ⟨hk, c, hs, he⟩ := h
  exact ⟨hk, c, hs, he⟩

/-! ### Evaluated runs -/

/-- A domain from its values and its removed values. -/
def mkDom (vs : List ℕ) (dead : List ℕ := []) : Dom := vs.map fun v => (v, !dead.contains v)

/-- An instance from lists: the items as weight, profit and domain, and the sums' domains. -/
def mk (items : List (ℕ × ℕ × Dom)) (W P : Dom) : Inst :=
  ⟨items.length, fun j => (items.getD j (0, 0, [])).1, fun j => (items.getD j (0, 0, [])).2.1,
    fun j => (items.getD j (0, 0, [])).2.2, W, P⟩

/-- Two items, `x₀ ∈ {0, 1, 2}` of weight `2` and profit `1` and `x₁ ∈ {0, 1}` of weight `3` and
profit `2`, with `W ∈ {0, …, 4}` and `P ∈ {2, 3}`. -/
def ex : Inst := mk [(2, 1, mkDom [0, 1, 2]), (3, 2, mkDom [0, 1])] (mkDom [0, 1, 2, 3, 4])
  (mkDom [2, 3])

/-- On a concrete choice: `(x₀, x₁) = (2, 0)`, of weight `4` and profit `2`, supports the value
`2` of `x₀`. -/
example : ex.SupportedN 0 2 :=
  ⟨by decide, fun j => if j = 0 then 2 else 0, ⟨by decide, ⟨4, by decide, by decide⟩, 0,
    by decide, by decide⟩, rfl⟩

/-- On a concrete choice: `(x₀, x₁) = (0, 1)`, of weight `3` and profit `2`, supports the value
`3` of `W`, at position `3`. -/
example : ex.SupportedS false 3 :=
  ⟨by decide, fun j => if j = 0 then 0 else 1, ⟨by decide, ⟨3, by decide, by decide⟩, 0,
    by decide, by decide⟩, by decide⟩

/-- All choices of positions for domains of the given lengths. -/
def choices : List ℕ → List (List ℕ)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap fun k => (choices ms).map (k :: ·)

/-- The solutions, by brute force: the choices of positions of the current domains whose weight
and profit are in theirs. -/
def sols (I : Inst) : List (List ℕ) :=
  let wt (c : List ℕ) := ((List.range I.n).map fun j => I.cw j (c.getD j 0)).sum
  let pt (c : List ℕ) := ((List.range I.n).map fun j => I.cp j (c.getD j 0)).sum
  (choices ((List.range I.n).map I.len)).filter fun c =>
    (List.range I.n).all (fun j => dlive (I.dom j) (c.getD j 0)) &&
      (livePos I.wDom).any (fun k => dval I.wDom k == wt c) &&
      (livePos I.pDom).any (fun k => dval I.pDom k == pt c)

/-- The values to remove, by brute force. -/
def expected (I : Inst) : List (ℕ × ℕ) × List ℕ × List ℕ :=
  let wt (c : List ℕ) := ((List.range I.n).map fun j => I.cw j (c.getD j 0)).sum
  let pt (c : List ℕ) := ((List.range I.n).map fun j => I.cp j (c.getD j 0)).sum
  let S := sols I
  ((List.range I.n).flatMap fun j =>
      ((livePos (I.dom j)).filter fun k => !(S.any fun c => c.getD j 0 == k)).map (j, ·),
    (livePos I.wDom).filter fun k => !(S.any fun c => wt c == dval I.wDom k),
    (livePos I.pDom).filter fun k => !(S.any fun c => pt c == dval I.pDom k))

/-- Two lists have the same elements, once each. -/
def same {α : Type} [BEq α] (x y : List α) : Bool :=
  x.all (y.contains ·) && y.all (x.contains ·) && x.length == y.length

/-- The run is accepted, with and without the preserved set, and removes exactly the expected
values. -/
def agrees (I : Inst) : Bool :=
  let P := I.propagate
  let E := expected I
  checkRed I.formula none P.proof (some I.pres) && checkRed I.formula none P.proof &&
    same P.removed E.1 && same P.removedW E.2.1 && same P.removedP E.2.2

/-- The boundary and hand-made cases. -/
def cases : List Inst :=
  [mk [] (mkDom [0]) (mkDom [0]), mk [] (mkDom [1]) (mkDom [0]), mk [] [] [],
    mk [(2, 1, mkDom [0, 1, 2]), (3, 2, mkDom [0, 1])] (mkDom [0, 1, 2, 3, 4]) (mkDom [2, 3]),
    mk [(2, 3, mkDom [0, 1, 2]), (3, 1, mkDom [0, 1]), (1, 2, mkDom [0, 1, 3] [3])]
      (mkDom [0, 1, 2, 3, 4, 5, 6, 7] [3]) (mkDom [3, 4, 5, 6, 7, 8]),
    mk [(1, 1, mkDom [0, 1]), (2, 0, [])] (mkDom [0, 1, 2]) (mkDom [0, 1]),
    mk [(0, 0, mkDom [0, 5]), (1, 1, mkDom [1, 1])] (mkDom [0, 1, 1]) (mkDom [1]),
    mk [(3, 2, mkDom [0, 1, 2] [0, 1, 2])] (mkDom [0, 3, 6]) (mkDom [0, 2, 4]),
    mk [(1, 2, mkDom [0, 1]), (2, 1, mkDom [0, 1])] (mkDom [0, 1, 2, 3] [1, 3]) (mkDom [0, 3])]

#guard cases.all agrees

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- A random number below `m` and the next seed. -/
def rnd (s m : ℕ) : ℕ × ℕ := let s' := lcg s; (s', s' / 65536 % m)

/-- A random domain of `len` values below `maxv`, each in the current domain with probability
`3/4`. -/
def randDom (s len maxv : ℕ) : ℕ × Dom :=
  (List.range len).foldl (fun (s, D) _ =>
    let (s, v) := rnd s maxv
    let (s, l) := rnd s 4
    (s, D ++ [(v, l != 0)])) (s, [])

/-- A random instance from the seed `s`: up to `3` items of weights and profits below `4` with
domains of up to `3` values below `4`, and domains of up to `7` values below `12` for the sums. -/
def randInst (s : ℕ) : Inst :=
  let (s, n) := rnd s 4
  let (s, items) := (List.range n).foldl (fun (s, items) _ =>
    let (s, w) := rnd s 4
    let (s, p) := rnd s 4
    let (s, l) := rnd s 4
    let (s, D) := randDom s l 4
    (s, items ++ [(w, p, D)])) (s, [])
  let (s, lw) := rnd s 8
  let (s, W) := randDom s lw 12
  let (s, lp) := rnd s 8
  let (_, P) := randDom s lp 12
  mk items W P

#guard (List.range 150).all fun s => agrees (randInst (s * 7919 + 3))

/-! ### Kernel text -/

/-- The formula of an instance as OPB text, by the library's printer. -/
def opbText (I : Inst) : String := Text.printOPB ⟨I.formula, none, none⟩

/-- The proof of an instance as kernel text. -/
def proofText (I : Inst) : String := pbpText I.formula.length I.propagate.proof

/-- The text front end accepts the printed proof against the printed formula. -/
def textAgrees (I : Inst) : Bool := Text.checkOPB (opbText I) (proofText I) == some .noClaim

/-- The cases whose texts were checked by VeriPB and CakePB. -/
def printCases : List Inst := cases ++ [randInst 10, randInst 31, randInst 58, randInst 93]

#guard printCases.all textAgrees

/-- Write the texts of `printCases` to `dir`, for the external checkers. -/
def writeCases (dir : System.FilePath) : IO Unit := do
  for (c, k) in printCases.zipIdx do
    IO.FS.writeFile (dir / s!"trick{k}.opb") (opbText c)
    IO.FS.writeFile (dir / s!"trick{k}.pbp") (proofText c)

end CslibFrontierTests.Logics.Propositional.VeriPBKnapsackTrick
