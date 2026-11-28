/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Symmetry
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CslibFrontierTests.Logics.Propositional.VeriPBProofText
-- `meta`: the `#guard` below runs the printer.
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Symmetry
-- `import all`: the kernel evaluates `stepTop`, `printOPB` and the text checker, whose bodies are
-- not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Clients of certified symmetry breaking (`CslibFrontier.Logics.Propositional.PseudoBoolean.
Symmetry`).

* **Pigeonhole.** `PHP(m, m - 1)` with its adjacent pigeon swaps broken by lex-leader
  constraints over all its variables, followed by a cutting-planes refutation. The prefix is
  accepted by `runTop_symmetryBreaking`, whose hypothesis `MapsInto` is decided; the refutation is
  decided by the kernel from the state it gives. The refutation is the one used without symmetry
  breaking: for cutting planes, the lex-leader constraints do not shorten it, and the prefix adds
  `2 + (m - 1)` steps (and `6 (m - 1)` constraint numbers).
* **A wrong symmetry**: a swap of two variables of different holes, which does not map the
  formula into itself, is rejected by the `dom` check.
* **Maximum clique** on the 5-cycle, whose rotation is broken; the proof, printed as VeriPB text,
  certifies the clique number `2` through `checkCliqueGraph`.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBSymmetry

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph
open CslibFrontierTests.Logics.Propositional.VeriPBProofText (pbpText)

/-! ### Pigeonhole -/

/-- The variable of pigeon `i` in hole `j`, with `n` holes. -/
def php.var (n i j : ℕ) : ℕ := i * n + j

/-- The pairs of pigeons `i < i'` among `m`, in order. -/
def php.pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun i => (List.range' (i + 1) (m - (i + 1))).map fun i' => (i, i')

/-- `PHP(m, n)`: every pigeon in some hole, then for each hole and pair of pigeons, not both. -/
def php (m n : ℕ) : List PBConstr :=
  (List.range m).map (fun i => ⟨(List.range n).map fun j => (1, (php.var n i j, true)), 1⟩) ++
    (List.range n).flatMap fun j => (php.pairs m).map fun p =>
      ⟨[(1, (php.var n p.1 j, false)), (1, (php.var n p.2 j, false))], 1⟩

/-- The swap of pigeons `i` and `i + 1`. -/
def php.swap (n i : ℕ) : List (ℕ × Literal ℕ) :=
  (List.range n).flatMap fun j =>
    [(php.var n i j, (php.var n (i + 1) j, true)), (php.var n (i + 1) j, (php.var n i j, true))]

/-- The adjacent pigeon swaps. -/
def php.swaps (m n : ℕ) : List (List (ℕ × Literal ℕ)) := (List.range (m - 1)).map (php.swap n)

/-- The number of the constraint "not both `i` and `i'` in hole `j`". -/
def php.pairId (m j i i' : ℕ) : ℕ :=
  m + j * (php.pairs m).length + (php.pairs m).idxOf (i, i') + 1

/-- One step of `php.amo`: from `∑_{i < k} ¬xᵢⱼ ≥ k - 1`, numbered `t`, multiplied by `k - 1`,
and the pairs `(i, k)`, divide by `k` to get `∑_{i ≤ k} ¬xᵢⱼ ≥ k`, numbered `c`. -/
def php.amoStep (m j : ℕ) : List TopStep × ℕ × ℕ → ℕ → List TopStep × ℕ × ℕ
  | (ss, t, c), k =>
    (ss ++ [.step (.pol ([.id t, .mul (k - 1)] ++
      ((List.range k).flatMap fun i => [.id (php.pairId m j i k), .add]) ++ [.div k]))],
      c, c + 1)

/-- The cutting-planes derivation of "at most one pigeon in hole `j`", `∑ᵢ ¬xᵢⱼ ≥ m - 1`, from
the next number `c`: its steps, the number of the result, and the next number after it. -/
def php.amo (m j c : ℕ) : List TopStep × ℕ × ℕ :=
  (List.range' 2 (m - 2)).foldl (php.amoStep m j) ([], php.pairId m j 0 1, c)

/-- The cutting-planes refutation of `PHP(m, n)` for `m = n + 1`, from the next number `c`: the
at-most-one constraints of the holes, then the sum of every pigeon and hole constraint, which is
a contradiction. Returns the steps and the number of the contradiction. -/
def php.refutation (m n c : ℕ) : List TopStep × ℕ :=
  match (List.range n).foldl (fun (acc : List TopStep × List ℕ × ℕ) j =>
      match acc, php.amo m j acc.2.2 with
      | (ss, ts, _), (ss', t, c') => (ss ++ ss', ts ++ [t], c')) ([], [], c) with
  | (ss, ts, c') =>
    (ss ++ [.step (.pol ([.id 1] ++ ((List.range' 2 (m - 1)).flatMap fun i => [.id i, .add]) ++
      ts.flatMap fun t => [.id t, .add]))], c')

/-- The symmetry-breaking prefix of `PHP(m, m - 1)`: the lexicographic order over all its
variables, and the adjacent pigeon swaps. -/
def php.prefix (m : ℕ) : List TopStep :=
  symmetryBreaking "lex" (List.range (m * (m - 1))) (php.swaps m (m - 1))
    ((php m (m - 1)).length + 1)

/-- The whole proof: the prefix, then the refutation. -/
def php.proof (m : ℕ) : RedProof :=
  let r := php.refutation m (m - 1) ((php m (m - 1)).length + 1 + 6 * (m - 1))
  ⟨php.prefix m ++ r.1, .unsat r.2⟩

-- The swaps are symmetries, as `MapsInto` decides.
example : ∀ π ∈ php.swaps 3 2, MapsInto (php 3 2) π = true := by decide +kernel
example : ∀ π ∈ php.swaps 4 3, MapsInto (php 4 3) π = true := by decide +kernel

/-- **PHP(m, m - 1) with its pigeon symmetries broken is refuted**, for `m = 3, 4`: the prefix is
accepted by `runTop_symmetryBreaking` and the refutation is decided from the state it gives. -/
theorem php_checkRed (m : ℕ) (hm : m = 3 ∨ m = 4) :
    checkRed (php m (m - 1)) none (php.proof m) = true := by
  have hsym : ∀ π ∈ php.swaps m (m - 1), MapsInto (php m (m - 1)) π = true := by
    rcases hm with rfl | rfl <;> decide +kernel
  have hpre := runTop_symmetryBreaking (F := php m (m - 1)) (obj := none) (pres := none)
    (name := "lex") (xs := List.range (m * (m - 1))) hsym (fun _ _ => rfl)
    (fun _ _ _ h => nomatch h)
  simp only [checkRed, php.proof, php.prefix]
  rw [runTop_append, hpre, Option.bind_some]
  rcases hm with rfl | rfl <;> decide +kernel

/-- So PHP(4, 3) has no solution. -/
example : ¬ ∃ σ, ∀ c ∈ php 4 3, c.Holds σ := fun ⟨σ, hσ⟩ =>
  not_satisfiable_of_checkRed (obj := none) (P := php.proof 4) (pres := none)
    (php_checkRed 4 (.inr rfl)) rfl σ hσ

/-! ### A wrong symmetry -/

/-- Swapping pigeon `0` in hole `0` with pigeon `1` in hole `1` does not map PHP(3, 2) into
itself. -/
def wrongSwap : List (ℕ × Literal ℕ) := [(php.var 2 0 0, (php.var 2 1 1, true)),
  (php.var 2 1 1, (php.var 2 0 0, true))]

example : MapsInto (php 3 2) wrongSwap = false := by decide +kernel

-- Its `dom` step is rejected.
example : runTop (php 3 2) none (State.init (php 3 2) none none)
    (symmetryBreaking "lex" (List.range 6) [wrongSwap] 10) = none := by
  decide +kernel

/-! ### Maximum clique on the 5-cycle -/

/-- The rotation `v ↦ v + 1` of the 5-cycle. -/
def rot5 : List (ℕ × Literal ℕ) := (List.range 5).map fun v => (v, ((v + 1) % 5, true))

/-- The constraints of the clique encoding of the 5-cycle. -/
abbrev c5F : List PBConstr := (encodeClique (SimpleGraph.cycleGraph 5)).constraints

example : MapsInto c5F rot5 = true := by decide +kernel

/-- Maximum clique on the 5-cycle with its rotation broken: the lex-leader constraint of the
rotation over `x1 … x5` is `11`; the lex-leading clique `{4, 5}` is logged, adding the improving
constraint `12`, `f ≤ 2`; the sum of the five non-edges, halved, is `∑ ¬x ≥ 3`, which with `12`
is the contradiction `13`. -/
def c5Proof : RedProof :=
  ⟨symmetryBreaking "lex" (List.range 5) [rot5] 6 ++
    [.soli [(0, false), (1, false), (2, false), (3, true), (4, true)],
      .step (.pol [.id 1, .id 2, .add, .id 3, .add, .id 4, .add, .id 5, .add, .div 2, .id 12,
        .add])],
    .bounds (some 3) 13 (some 3) none⟩

/-- The proof as VeriPB text, as `pbpText` prints it (checked below): the kernel evaluates the
text checker on a string literal, not the printer. VeriPB 3.0.2 and CakePB accept it against the
printed encoding (`s VERIFIED BOUNDS 3 <= obj <= 3`), and `cake_pb_clique` against the 5-cycle as
a DIMACS graph (`|CLIQUE| = 2`). -/
def c5ProofText : String := "pseudo-Boolean proof version 3.0
f 5 ;
def_order lex
vars
left u1 u2 u3 u4 u5;
right v1 v2 v3 v4 v5;
aux;
end;
def
16 ~u1 16 v1 8 ~u2 8 v2 4 ~u3 4 v3 2 ~u4 2 v4 1 ~u5 1 v5 >= 31;
end;
transitivity
vars
fresh_right w1 w2 w3 w4 w5;
end;
proof
proofgoal #1
pol 1 2 + 3 +;
qed : 4;
qed;
end;
reflexivity
proof
proofgoal #1
qed : 5;
qed;
end;
end;
load_order lex x1 x2 x3 x4 x5;
dom 16 ~x1 16 x2 8 ~x2 8 x3 4 ~x3 4 x4 2 ~x4 2 x5 1 ~x5 1 x1 >= 31 : x1 -> x2 x2 -> x3 x3 \
  -> x4 x4 -> x5 x5 -> x1 : subproof
proofgoal #1
pol 6 7 +;
qed : 8;
proofgoal #2
pol 6 9 +;
qed : 10;
qed;
soli ~x1 ~x2 ~x3 x4 x5 ;
pol 1 2 + 3 + 4 + 5 + 2 d 12 + ;
output NONE ;
conclusion BOUNDS 3 : 13 3 ;
end pseudo-Boolean proof ;
"

#guard pbpText 5 c5Proof == c5ProofText

/-- **The clique number of the 5-cycle is `2`**, certified with its rotation broken. -/
theorem c5_checkCliqueGraph :
    checkCliqueGraph (SimpleGraph.cycleGraph 5) c5ProofText = some (2, 2) := by
  decide +kernel

example : (SimpleGraph.cycleGraph 5).cliqueNum = 2 :=
  cliqueNum_eq_of_checkCliqueGraph c5_checkCliqueGraph

end CslibFrontierTests.Logics.Propositional.VeriPBSymmetry

end
