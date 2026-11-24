/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-! Fixtures for orders and dominance-based strengthening in the VeriPB checker: PHP(3, 2) and a
proof that breaks its pigeon symmetry by `dom` under a lexicographic order, accepted by VeriPB
3.0.2 and CakePB, and the lexicographic order `lex2` on two bits with its transitivity and
reflexivity proofs, as checker values. They are shared by the `#guard` tests of
`CslibFrontierTests.Logics.Propositional.VeriPBText`, the decided checks of
`CslibFrontierTests.Logics.Propositional.VeriPBRed` and the decided client of
`CslibFrontierTests.Logics.Propositional.VeriPBTextDecide`. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBText

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- The lexicographic order on two bits, `(u1, u2) ⪯ (v1, v2)` when `2 u1 + u2 ≤ 2 v1 + v2`:
the constraint `-2 u1 - u2 + 2 v1 + v2 >= 0`, with `u1, u2, v1, v2` the variables `10`–`13`. -/
def lex2 : Order :=
  ⟨[10, 11], [12, 13], [], [],
    [⟨[(2, (10, false)), (1, (11, false)), (2, (12, true)), (1, (13, true))], 3⟩]⟩

/-- Transitivity, with the fresh right variables `14`, `15`: the premises `O⪯(u, v)` and
`O⪯(v, w)` are `1` and `2`, the negated goal `#1` is `3`, and their sum `4` is a
contradiction. -/
def lex2Trans : OrderProof :=
  ⟨[.goal (.hash 1) [.pol [.id 1, .id 2, .add, .id 3, .add]] 4], none⟩

/-- Reflexivity, numbered after transitivity: the goal `O⪯(u, u)` is trivial, and its negation
`5` is itself a contradiction. -/
def lex2Refl : OrderProof := ⟨[.goal (.hash 1) [] 5], none⟩


/-- PHP(3, 2) in OPB: pigeon `i` in hole `j` is `x(2i+j+1)`. -/
def php32 : String := "* #variable= 6 #constraint= 9
+1 x1 +1 x2 >= 1 ;
+1 x3 +1 x4 >= 1 ;
+1 x5 +1 x6 >= 1 ;
+1 ~x1 +1 ~x3 >= 1 ;
+1 ~x1 +1 ~x5 >= 1 ;
+1 ~x3 +1 ~x5 >= 1 ;
+1 ~x2 +1 ~x4 >= 1 ;
+1 ~x2 +1 ~x6 >= 1 ;
+1 ~x4 +1 ~x6 >= 1 ;
"

/-- The lexicographic order on four bits, `u ⪯ v` when `u ≤ v` as binary numbers. Transitivity:
the premises `O⪯(u, v)` and `O⪯(v, w)` are `1` and `2`, the negated goal is `3`, and the sum `4`
is a contradiction. Reflexivity is numbered after it: the negated goal `5` is a contradiction. -/
def lex4 : String := "def_order lex4
vars
left u1 u2 u3 u4;
right v1 v2 v3 v4;
aux;
end;
def
-8 u1 -4 u2 -2 u3 -1 u4 8 v1 4 v2 2 v3 1 v4 >= 0;
end;
transitivity
vars
fresh_right w1 w2 w3 w4;
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
"

/-- PHP(3, 2) with symmetry breaking (§5.4.2): `lex4` loaded over the variables of pigeons `1`
and `2`, and the lex-leader constraint of swapping them, `z ⪯ z∘σ`, derived by `dom` with the
swap. `¬C` is `10`, goal `#2` adds `O⪯(z, z↾ω)` as `11`, `10 + 11` is the contradiction `12`; the
core goals are the swapped input constraints, which are in the database, and goal `#1` follows
from `¬C`. Then the cutting-planes refutation. VeriPB 3.0.2 and CakePB accept. -/
def domPhp32 : String := "pseudo-Boolean proof version 3.0
f 9;
" ++ lex4 ++ "load_order lex4 x1 x2 x3 x4;
dom -6 x1 -3 x2 6 x3 3 x4 >= 0 : x1 -> x3 x2 -> x4 x3 -> x1 x4 -> x2 : subproof
proofgoal #2
pol 10 11 +;
qed : 12;
qed;
pol 4 5 + 6 + 2 d;
pol 7 8 + 9 + 2 d;
pol 1 2 + 3 + 14 + 15 +;
output NONE;
conclusion UNSAT : 16;
end pseudo-Boolean proof;
"

end CslibFrontierTests.Logics.Propositional.VeriPBText

end
