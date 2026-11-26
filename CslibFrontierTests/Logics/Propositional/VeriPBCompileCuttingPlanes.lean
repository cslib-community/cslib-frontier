/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CompileCuttingPlanes

/-! Compiling cutting planes proofs into VeriPB `pol` steps: the compiled cutting planes refutation
of the pigeonhole formula PHP(3, 2) is accepted by the kernel checker; a wrong premise is
rejected; the compiled constraint of a line can be strictly stronger than the line; and the
compilation theorem applies to the clause inequalities of a CNF. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBCompileCuttingPlanes

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- PHP(3, 2): pigeon `i` in hole `j` is the variable `2 i + j`. Constraints `1`–`3` say that each
pigeon is in a hole; constraints `4`–`6` and `7`–`9` say that no two pigeons share hole `0` and
hole `1`. -/
def php : CNF ℕ :=
  [[(0, true), (1, true)], [(2, true), (3, true)], [(4, true), (5, true)],
    [(0, false), (2, false)], [(0, false), (4, false)], [(2, false), (4, false)],
    [(1, false), (3, false)], [(1, false), (5, false)], [(3, false), (5, false)]]

/-- The cutting planes refutation of PHP(3, 2), first line first. Lines `0`–`5` add the three
hole-`0` inequalities `-xᵢ - xⱼ ≥ -1` to `-2 x₀ - 2 x₂ - 2 x₄ ≥ -3` and divide by `2`, giving
`-x₀ - x₂ - x₄ ≥ -1`; lines `6`–`11` do the same for hole `1`. Lines `12`–`16` add the pigeon
inequalities, and lines `17` and `18` add the two hole lines, giving `0 ≥ 1`. -/
def refutation : List CPLine :=
  [.hyp 4, .hyp 5, .add 0 1, .hyp 6, .add 2 3, .div 2 4,
    .hyp 7, .hyp 8, .add 6 7, .hyp 9, .add 8 9, .div 2 10,
    .hyp 1, .hyp 2, .add 12 13, .hyp 3, .add 14 15, .add 16 5, .add 17 11]

/-- The formula has `9` constraints, so the line at position `p` is constraint `10 + p` and the
last line, at position `18`, is constraint `28`. -/
def proof : Proof := ⟨refutation.map (CPLine.toStep 10), 28⟩

example : check (php.map Clause.toPB) proof = true := by decide

example : proof.steps.all Step.IsCP := by decide

-- Adding the first hole line twice instead of both hole lines is no contradiction.
example : check (php.map Clause.toPB)
    ⟨(refutation.take 18 ++ [CPLine.add 17 5]).map (CPLine.toStep 10), 28⟩ = false := by
  decide

/-- **The compiled constraint can be strictly stronger than its line.** The cutting planes line
`x₀ ≥ 0` plus `-x₀ ≥ -1` is `0 ≥ -1`. VeriPB adds and normalizes the literal axioms `x₀ ≥ 0` and
`¬x₀ ≥ 0` to `0 ≥ 0`, whose inequality has bound `0`: the degree of a constraint is a natural
number. -/
example : (PBConstr.litAxiom (0, true)).add (PBConstr.litAxiom (0, false)) = ⟨[], 0⟩ := by
  decide

/-- The compilation applies to any cutting planes refutation of a CNF's clause inequalities. -/
example {φ : CNF ℕ} {s : ℕ} (h : CuttingPlanes.RefutableInSize φ.toIneqs s) :
    ∃ P : Proof, check (φ.map Clause.toPB) P = true ∧ P.steps.length ≤ s :=
  let ⟨P, hP, hlen, _⟩ := exists_check_cnf_of_refutableInSize h
  ⟨P, hP, hlen⟩

end CslibFrontierTests.Logics.Propositional.VeriPBCompileCuttingPlanes

end
