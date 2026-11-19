/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes

/-! The VeriPB kernel-proof checker on the pigeonhole formula PHP(3, 2): a cutting-planes proof is
accepted, proves the formula unsatisfiable, and translates into a cutting planes refutation;
proofs with a corrupted step are rejected; RUP with and without hints, and proof by
contradiction. -/

namespace CslibFrontierTests.Logics.Propositional.VeriPB

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- PHP(3, 2): pigeon `i` in hole `j` is the variable `2 i + j`. Constraints `1`–`3` say that each
pigeon is in a hole; constraints `4`–`6` and `7`–`9` say that no two pigeons share hole `0` and
hole `1`. -/
def php : CNF ℕ :=
  [[(0, true), (1, true)], [(2, true), (3, true)], [(4, true), (5, true)],
    [(0, false), (2, false)], [(0, false), (4, false)], [(2, false), (4, false)],
    [(1, false), (3, false)], [(1, false), (5, false)], [(3, false), (5, false)]]

/-- The kernel proof, in VeriPB syntax:
```
pseudo-Boolean proof version 3.0
f 9 ;
pol 4 5 + 6 + 2 d ;
pol 7 8 + 9 + 2 d ;
pol 1 2 + 3 + 10 + 11 + ;
output NONE ;
conclusion UNSAT : 12 ;
end pseudo-Boolean proof ;
```
Constraint `10` is `~x0 + ~x2 + ~x4 >= 2`: the three hole-`0` clauses sum to
`2 ~x0 + 2 ~x2 + 2 ~x4 >= 3`, and division by `2` rounds `3 / 2` up. Constraint `11` is the same
for hole `1`. Constraint `12` adds the pigeon clauses to both: every variable appears with both
signs, so it normalizes to `0 >= 1`. -/
def proof : Proof :=
  ⟨[.pol [.id 4, .id 5, .add, .id 6, .add, .div 2],
    .pol [.id 7, .id 8, .add, .id 9, .add, .div 2],
    .pol [.id 1, .id 2, .add, .id 3, .add, .id 10, .add, .id 11, .add]], 12⟩

example : check (php.map Clause.toPB) proof = true := by decide

theorem php_unsat : ¬ php.Satisfiable := not_satisfiable_cnf_of_check (P := proof) (by decide)

-- The proof uses only `pol` steps without saturation, so it is a cutting planes refutation of the
-- clause inequalities of `php`.
example : ∃ s, CuttingPlanes.RefutableInSize php.toIneqs s :=
  exists_isProof_contra_of_check_cnf (P := proof) (by decide) (by decide)

-- Dividing by `3` instead of `2` gives `~x0 + ~x2 + ~x4 >= 1`, and the sum is no contradiction.
example : check (php.map Clause.toPB)
    ⟨[.pol [.id 4, .id 5, .add, .id 6, .add, .div 3],
      .pol [.id 7, .id 8, .add, .id 9, .add, .div 2],
      .pol [.id 1, .id 2, .add, .id 3, .add, .id 10, .add, .id 11, .add]], 12⟩ = false := by
  decide

-- Leaving out the third pigeon clause leaves `~x4 + ~x5 >= 2`, which is no contradiction.
example : check (php.map Clause.toPB)
    ⟨[.pol [.id 4, .id 5, .add, .id 6, .add, .div 2],
      .pol [.id 7, .id 8, .add, .id 9, .add, .div 2],
      .pol [.id 1, .id 2, .add, .id 10, .add, .id 11, .add]], 12⟩ = false := by
  decide

-- The conclusion must name a contradiction.
example : check (php.map Clause.toPB) ⟨proof.steps, 11⟩ = false := by decide

-- RUP with hints: from `x0 >= 1` (constraint `1`) and `~x0 >= 1` (constraint `2`), the empty
-- constraint `>= 1` follows; `~` is its negation `>= 0`, which propagates nothing.
example : check [⟨[(1, (0, true))], 1⟩, ⟨[(1, (0, false))], 1⟩]
    ⟨[.rup ⟨[], 1⟩ (some [.neg, .id 1, .id 2])], 3⟩ = true := by decide

-- The same without hints, and a wrong RUP claim rejected.
example : check [⟨[(1, (0, true))], 1⟩, ⟨[(1, (0, false))], 1⟩]
    ⟨[.rup ⟨[], 1⟩ none], 3⟩ = true := by decide

example : check [⟨[(1, (0, true)), (1, (1, true))], 1⟩]
    ⟨[.rup ⟨[(1, (0, true))], 1⟩ none], 2⟩ = false := by decide

-- Proof by contradiction: from `x1 >= 1` and `~x1 + x2 >= 1`, prove `x2 >= 1`. The subproof starts
-- from its negation `~x2 >= 1` (number `4`) and derives `>= 1` (number `5`) by RUP; `x2 >= 1`
-- takes number `6`, and with `~x2 >= 1`, the third constraint, RUP gives the contradiction `7`.
example : check [⟨[(1, (1, true))], 1⟩, ⟨[(1, (1, false)), (1, (2, true))], 1⟩,
      ⟨[(1, (2, false))], 1⟩]
    ⟨[.pbc ⟨[(1, (2, true))], 1⟩ [.rup ⟨[], 1⟩ (some [.id 4, .id 1, .id 2])] 5,
      .rup ⟨[], 1⟩ (some [.id 3, .id 6])], 7⟩ = true := by decide

-- The subproof's constraints are dropped after `qed`: number `5` is gone.
example : check [⟨[(1, (1, true))], 1⟩, ⟨[(1, (1, false)), (1, (2, true))], 1⟩,
      ⟨[(1, (2, false))], 1⟩]
    ⟨[.pbc ⟨[(1, (2, true))], 1⟩ [.rup ⟨[], 1⟩ (some [.id 4, .id 1, .id 2])] 5], 5⟩ = false := by
  decide

end CslibFrontierTests.Logics.Propositional.VeriPB
