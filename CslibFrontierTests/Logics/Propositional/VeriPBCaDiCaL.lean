/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate
-- `#guard` runs the parsers and checkers at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate
-- `import all`: the kernel evaluates the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed, to decide the acceptance of the proofs.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! # VeriPB proofs written by CaDiCaL

CaDiCaL 3.0.1 writes VeriPB proofs of unsatisfiability in four modes, `--veripb=1` to `4`:

* modes `1` and `2` write each learned clause as a `pol` derivation of additions and
  saturations, followed by the check `e C : j;` (§5.11.1 of the VeriPB/CakePB documentation,
  22 June 2026 edition) that the derived constraint `j` is the clause `C`;
* modes `3` and `4` write `rup C;` without hints;
* all modes delete constraints with `del id j;`; the even modes also move every learned clause to
  the core with `core id j;`, and delete core constraints with the unchecked `delc j;`.

The proofs of PHP(4, 3) in the four modes, written by `cadical --veripb=M php43.cnf php43.vM.pbp`
for the formula `php43`, are accepted by the kernel text front end
(`Cslib.Logic.PL.VeriPB.Text.checkDIMACS`) and by the elaborator
(`Cslib.Logic.PL.VeriPB.Elab.checkAugmentedDIMACS`). For the hintless modes `3` and `4`, the
acceptance by the front end is decided by `decide +kernel`. The kernel's evaluation of the `pol`
derivations of modes `1` and `2` needs more than 6 GiB, so those proofs are checked by `#guard`,
as are the other checks here. The front end and the elaborator also accept the mode `2` proof of
PHP(5, 4) after bounded variable elimination (`cadical -P1 --veripb=2`), which has `del id`,
`delc` and `core id`. An `e` check that names the wrong constraint is rejected. VeriPB 3.0.2
accepts all of these proofs. CakePB (commit `438b8f8`) accepts the mode `1` and `2` proofs of
PHP(4, 3), and rejects the others, which use `rup` without hints or `del id`, outside its kernel
format. -/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBCaDiCaL

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Elab

/-- PHP(4, 3) in DIMACS: pigeon `i` in hole `j` is the variable `3 i + j + 1`. -/
def php43 : String := "p cnf 12 22
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
"

/-- CaDiCaL's `--veripb=1` proof of `php43`: `pol` derivations checked by `e`. -/
def php43V1 : String := "pseudo-Boolean proof version 3.0
f 22;
pol 6 3 + s 1 + s 16 + s 13 + s 19 + s 22 + s;
e 1 ~x11 1 ~x12 >= 1 : 23;
pol 11 2 + s 1 + s 8 + s 6 + s 19 + s 21 + s;
e 1 ~x7 1 ~x12 >= 1 : 24;
pol 5 2 + s 1 + s 14 + s 12 + s 3 + s 24 + s 22 + s 21 + s 19 + s;
e 1 ~x12 >= 1 : 25;
pol 17 2 + s 1 + s 9 + s 7 + s 4 + s 16 + s 14 + s 12 + s 25 + s;
e 1 ~x8 >= 1 : 26;
pol 17 2 + s 1 + s 15 + s 13 + s 4 + s 10 + s 8 + s 6 + s 25 + s;
e 1 ~x7 >= 1 : 27;
pol 3 26 + s 27 + s;
e 1 x9 >= 1 : 28;
pol 18 28 + s;
e 1 ~x3 >= 1 : 29;
pol 20 28 + s;
e 1 ~x6 >= 1 : 30;
pol 15 4 + s 2 + s 7 + s 5 + s 25 + s 30 + s;
e 1 ~x1 >= 1 : 31;
pol 1 29 + s 31 + s;
e 1 x2 >= 1 : 32;
pol 11 32 + s;
e 1 ~x5 >= 1 : 33;
pol 13 32 + s;
e 1 ~x11 >= 1 : 34;
pol 2 30 + s 33 + s;
e 1 x4 >= 1 : 35;
pol 4 25 + s 34 + s;
e 1 x10 >= 1 : 36;
pol 9 36 + s 35 + s;
e >= 1 : 37;
output NONE;
conclusion UNSAT : 37;
end pseudo-Boolean proof;
"

/-- CaDiCaL's `--veripb=2` proof of `php43`: `pol` derivations checked by `e`, and
`core id`. -/
def php43V2 : String := "pseudo-Boolean proof version 3.0
f 22;
pol 6 3 + s 1 + s 16 + s 13 + s 19 + s 22 + s;
e 1 ~x11 1 ~x12 >= 1 : 23;
pol 11 2 + s 1 + s 8 + s 6 + s 19 + s 21 + s;
e 1 ~x7 1 ~x12 >= 1 : 24;
pol 5 2 + s 1 + s 14 + s 12 + s 3 + s 24 + s 22 + s 21 + s 19 + s;
e 1 ~x12 >= 1 : 25;
core id 25;
pol 17 2 + s 1 + s 9 + s 7 + s 4 + s 16 + s 14 + s 12 + s 25 + s;
e 1 ~x8 >= 1 : 26;
core id 26;
pol 17 2 + s 1 + s 15 + s 13 + s 4 + s 10 + s 8 + s 6 + s 25 + s;
e 1 ~x7 >= 1 : 27;
core id 27;
pol 3 26 + s 27 + s;
e 1 x9 >= 1 : 28;
core id 28;
pol 18 28 + s;
e 1 ~x3 >= 1 : 29;
core id 29;
pol 20 28 + s;
e 1 ~x6 >= 1 : 30;
core id 30;
pol 15 4 + s 2 + s 7 + s 5 + s 25 + s 30 + s;
e 1 ~x1 >= 1 : 31;
core id 31;
pol 1 29 + s 31 + s;
e 1 x2 >= 1 : 32;
core id 32;
pol 11 32 + s;
e 1 ~x5 >= 1 : 33;
core id 33;
pol 13 32 + s;
e 1 ~x11 >= 1 : 34;
core id 34;
pol 2 30 + s 33 + s;
e 1 x4 >= 1 : 35;
core id 35;
pol 4 25 + s 34 + s;
e 1 x10 >= 1 : 36;
core id 36;
pol 9 36 + s 35 + s;
e >= 1 : 37;
core id 37;
output NONE;
conclusion UNSAT : 37;
end pseudo-Boolean proof;
"

/-- CaDiCaL's `--veripb=3` proof of `php43`: `rup` without hints. -/
def php43V3 : String := "pseudo-Boolean proof version 3.0
f 22;
rup 1 ~x11 1 ~x12 >= 1;
rup 1 ~x7 1 ~x12 >= 1;
rup 1 ~x12 >= 1;
rup 1 ~x8 >= 1;
rup 1 ~x7 >= 1;
rup 1 x9 >= 1;
rup 1 ~x3 >= 1;
rup 1 ~x6 >= 1;
rup 1 ~x1 >= 1;
rup 1 x2 >= 1;
rup 1 ~x5 >= 1;
rup 1 ~x11 >= 1;
rup 1 x4 >= 1;
rup 1 x10 >= 1;
rup >= 1;
output NONE;
conclusion UNSAT : 37;
end pseudo-Boolean proof;
"

/-- CaDiCaL's `--veripb=4` proof of `php43`: `rup` without hints, and `core id`. -/
def php43V4 : String := "pseudo-Boolean proof version 3.0
f 22;
rup 1 ~x11 1 ~x12 >= 1;
rup 1 ~x7 1 ~x12 >= 1;
rup 1 ~x12 >= 1;
core id 25;
rup 1 ~x8 >= 1;
core id 26;
rup 1 ~x7 >= 1;
core id 27;
rup 1 x9 >= 1;
core id 28;
rup 1 ~x3 >= 1;
core id 29;
rup 1 ~x6 >= 1;
core id 30;
rup 1 ~x1 >= 1;
core id 31;
rup 1 x2 >= 1;
core id 32;
rup 1 ~x5 >= 1;
core id 33;
rup 1 ~x11 >= 1;
core id 34;
rup 1 x4 >= 1;
core id 35;
rup 1 x10 >= 1;
core id 36;
rup >= 1;
core id 37;
output NONE;
conclusion UNSAT : 37;
end pseudo-Boolean proof;
"

#guard checkDIMACS php43 php43V1 == some (.unsat 37)

#guard checkDIMACS php43 php43V2 == some (.unsat 37)

theorem php43V3_accepted : checkDIMACS php43 php43V3 = some (.unsat 37) := by decide +kernel

theorem php43V4_accepted : checkDIMACS php43 php43V4 = some (.unsat 37) := by decide +kernel

-- So PHP(4, 3) has no solution.
example : ∃ φ, parseDIMACS php43 = some φ ∧ ¬ φ.Satisfiable :=
  not_satisfiable_of_checkDIMACS php43V4_accepted

-- The elaborator accepts the four proofs too, with the contradiction renumbered.
#guard [php43V1, php43V2, php43V3, php43V4].all fun p =>
  (checkAugmentedDIMACS php43 p).any (· matches .unsat _)

-- An `e` check naming the wrong constraint, or a constraint that is not there, is rejected.
#guard (checkDIMACS php43 (php43V1.replace "e 1 ~x12 >= 1 : 25;" "e 1 ~x12 >= 1 : 24;")).isNone
#guard (checkDIMACS php43 (php43V1.replace "e 1 ~x12 >= 1 : 25;" "e 1 ~x12 >= 1 : 99;")).isNone
#guard (checkDIMACS php43 (php43V1.replace "e 1 ~x12 >= 1 : 25;" "e 1 ~x12 >= 2 : 25;")).isNone

/-- PHP(5, 4) in DIMACS: pigeon `i` in hole `j` is the variable `4 i + j + 1`. -/
def php54 : String := "p cnf 20 45
1 2 3 4 0
5 6 7 8 0
9 10 11 12 0
13 14 15 16 0
17 18 19 20 0
-1 -5 0
-1 -9 0
-1 -13 0
-1 -17 0
-5 -9 0
-5 -13 0
-5 -17 0
-9 -13 0
-9 -17 0
-13 -17 0
-2 -6 0
-2 -10 0
-2 -14 0
-2 -18 0
-6 -10 0
-6 -14 0
-6 -18 0
-10 -14 0
-10 -18 0
-14 -18 0
-3 -7 0
-3 -11 0
-3 -15 0
-3 -19 0
-7 -11 0
-7 -15 0
-7 -19 0
-11 -15 0
-11 -19 0
-15 -19 0
-4 -8 0
-4 -12 0
-4 -16 0
-4 -20 0
-8 -12 0
-8 -16 0
-8 -20 0
-12 -16 0
-12 -20 0
-16 -20 0
"

/-- CaDiCaL's `cadical -P1 --veripb=2` proof of `php54`: an initial round of preprocessing
eliminates five variables, so the proof deletes input clauses by `delc` and resolvents by
`del id`. -/
def php54P1V2 : String := "pseudo-Boolean proof version 3.0
f 45;
pol 6 1 + s;
e 1 ~x5 1 x2 1 x3 1 x4 >= 1 : 46;
core id 46;
pol 7 1 + s;
e 1 ~x9 1 x2 1 x3 1 x4 >= 1 : 47;
core id 47;
pol 8 1 + s;
e 1 ~x13 1 x2 1 x3 1 x4 >= 1 : 48;
core id 48;
pol 9 1 + s;
e 1 ~x17 1 x2 1 x3 1 x4 >= 1 : 49;
core id 49;
pol 10 2 + s;
e 1 ~x9 1 x6 1 x7 1 x8 >= 1 : 50;
core id 50;
pol 11 2 + s;
e 1 ~x13 1 x6 1 x7 1 x8 >= 1 : 51;
core id 51;
pol 12 2 + s;
e 1 ~x17 1 x6 1 x7 1 x8 >= 1 : 52;
core id 52;
pol 2 46 + s;
e 1 x6 1 x7 1 x8 1 x2 1 x3 1 x4 >= 1 : 53;
core id 53;
pol 13 3 + s;
e 1 ~x13 1 x10 1 x11 1 x12 >= 1 : 54;
core id 54;
pol 14 3 + s;
e 1 ~x17 1 x10 1 x11 1 x12 >= 1 : 55;
core id 55;
pol 3 47 + s;
e 1 x10 1 x11 1 x12 1 x2 1 x3 1 x4 >= 1 : 56;
core id 56;
pol 3 50 + s;
e 1 x10 1 x11 1 x12 1 x6 1 x7 1 x8 >= 1 : 57;
core id 57;
pol 15 4 + s;
e 1 ~x17 1 x14 1 x15 1 x16 >= 1 : 58;
core id 58;
pol 4 48 + s;
e 1 x14 1 x15 1 x16 1 x2 1 x3 1 x4 >= 1 : 59;
core id 59;
pol 4 51 + s;
e 1 x14 1 x15 1 x16 1 x6 1 x7 1 x8 >= 1 : 60;
core id 60;
pol 4 54 + s;
e 1 x14 1 x15 1 x16 1 x10 1 x11 1 x12 >= 1 : 61;
core id 61;
pol 5 49 + s;
e 1 x18 1 x19 1 x20 1 x2 1 x3 1 x4 >= 1 : 62;
core id 62;
pol 5 52 + s;
e 1 x18 1 x19 1 x20 1 x6 1 x7 1 x8 >= 1 : 63;
core id 63;
pol 5 55 + s;
e 1 x18 1 x19 1 x20 1 x10 1 x11 1 x12 >= 1 : 64;
core id 64;
pol 5 58 + s;
e 1 x18 1 x19 1 x20 1 x14 1 x15 1 x16 >= 1 : 65;
core id 65;
pol 53 22 + s 19 + s 39 + s 42 + s 29 + s 32 + s;
e 1 ~x18 1 ~x19 1 ~x20 >= 1 : 66;
pol 23 60 + s 57 + s 42 + s 44 + s 45 + s 32 + s 34 + s 35 + s;
e 1 x6 1 ~x19 1 ~x20 >= 1 : 67;
pol 59 21 + s 16 + s 67 + s 35 + s 29 + s 39 + s 45 + s;
e 1 ~x19 1 ~x20 >= 1 : 68;
del id 67;
del id 66;
pol 27 61 + s 59 + s 39 + s 44 + s 45 + s 16 + s 20 + s 21 + s;
e 1 x15 1 ~x6 1 ~x20 >= 1 : 69;
pol 56 33 + s 28 + s 69 + s 20 + s 16 + s 39 + s 44 + s;
e 1 ~x6 1 ~x20 >= 1 : 70;
del id 69;
pol 17 57 + s 53 + s 33 + s 31 + s 28 + s 39 + s 42 + s 44 + s 70 + s;
e 1 ~x15 1 ~x20 >= 1 : 71;
pol 30 61 + s 60 + s 18 + s 17 + s 42 + s 44 + s 45 + s 70 + s 71 + s;
e 1 ~x2 1 ~x20 >= 1 : 72;
pol 56 23 + s 30 + s 59 + s 53 + s 39 + s 42 + s 44 + s 45 + s 70 + s 71 + s 72 + s;
e 1 x3 1 ~x20 >= 1 : 73;
pol 23 57 + s 60 + s 27 + s 26 + s 73 + s 71 + s 70 + s 45 + s 44 + s 42 + s;
e 1 ~x20 >= 1 : 74;
core id 74;
pol 53 29 + s 38 + s 63 + s 60 + s 23 + s 24 + s 74 + s;
e 1 x7 1 x8 1 ~x10 1 x2 1 x15 1 x6 >= 1 : 75;
pol 38 65 + s 62 + s 32 + s 26 + s 23 + s 24 + s 74 + s;
e 1 ~x7 1 ~x10 1 x2 1 x15 >= 1 : 76;
pol 29 59 + s 65 + s 41 + s 36 + s 75 + s 76 + s 24 + s 23 + s 74 + s;
e 1 ~x10 1 x2 1 x15 1 x6 >= 1 : 77;
del id 75;
pol 64 25 + s 29 + s 61 + s 56 + s 41 + s 36 + s 74 + s;
e 1 ~x8 1 x11 1 x12 1 x10 1 x2 1 x15 >= 1 : 78;
pol 61 25 + s 38 + s 64 + s 56 + s 32 + s 26 + s 57 + s 78 + s 77 + s 74 + s;
e 1 x11 1 x12 1 x2 1 x15 1 x6 >= 1 : 79;
pol 60 25 + s 38 + s 63 + s 53 + s 27 + s 30 + s 34 + s 74 + s;
e 1 x8 1 ~x11 1 x2 1 x15 1 x6 >= 1 : 80;
pol 25 59 + s 62 + s 41 + s 36 + s 80 + s 34 + s 27 + s 74 + s;
e 1 ~x11 1 x2 1 x15 1 x6 >= 1 : 81;
del id 80;
pol 32 62 + s 53 + s 74 + s;
e 1 x3 1 x18 1 x8 1 x4 1 x2 1 x6 >= 1 : 82;
pol 63 29 + s 26 + s 82 + s 74 + s;
e 1 x18 1 x8 1 x6 1 x4 1 x2 >= 1 : 83;
del id 82;
pol 26 59 + s 60 + s 25 + s 83 + s 43 + s 40 + s 37 + s 79 + s;
e 1 x11 1 x2 1 x6 1 x15 >= 1 : 84;
del id 79;
pol 84 81 + s;
e 1 x2 1 x15 1 x6 >= 1 : 85;
del id 81;
del id 84;
pol 63 29 + s 26 + s 74 + s;
e 1 ~x3 1 x8 1 x18 1 x6 >= 1 : 86;
pol 43 60 + s 57 + s 17 + s 18 + s 85 + s;
e 1 x7 1 x8 1 x11 1 x15 1 x6 >= 1 : 87;
pol 43 65 + s 64 + s 74 + s;
e 1 x19 1 x11 1 x18 1 x14 1 x10 1 x15 >= 1 : 88;
pol 61 41 + s 40 + s 87 + s 32 + s 88 + s 17 + s 18 + s 19 + s 85 + s;
e 1 x11 1 x15 1 x6 >= 1 : 89;
del id 87;
pol 41 65 + s 63 + s 34 + s 30 + s 89 + s 19 + s 18 + s 85 + s 74 + s;
e 1 x15 1 x6 >= 1 : 90;
del id 85;
pol 24 57 + s 63 + s 43 + s 41 + s 31 + s 33 + s 35 + s 90 + s 74 + s;
e 1 ~x16 1 x6 >= 1 : 91;
pol 37 57 + s 53 + s 28 + s 31 + s 33 + s 90 + s 19 + s 24 + s;
e 1 x8 1 ~x18 1 x6 >= 1 : 92;
pol 56 40 + s 36 + s 92 + s 24 + s 19 + s 28 + s 33 + s 90 + s;
e 1 ~x18 1 x6 >= 1 : 93;
del id 92;
pol 17 64 + s 62 + s 40 + s 36 + s 63 + s 93 + s 35 + s 33 + s 31 + s 28 + s 90 + s 74 + s;
e 1 x6 >= 1 : 94;
core id 94;
pol 16 94 + s;
e 1 ~x2 >= 1 : 95;
core id 95;
pol 20 94 + s;
e 1 ~x10 >= 1 : 96;
core id 96;
pol 21 94 + s;
e 1 ~x14 >= 1 : 97;
core id 97;
pol 22 94 + s;
e 1 ~x18 >= 1 : 98;
core id 98;
pol 35 64 + s 78 + s 95 + s 96 + s 74 + s 98 + s;
e 1 x12 1 ~x8 1 x11 >= 1 : 99;
del id 78;
pol 99 40 + s;
e 1 ~x8 1 x11 >= 1 : 100;
del id 99;
pol 38 61 + s 56 + s 35 + s 29 + s 64 + s 74 + s 98 + s 95 + s 96 + s 97 + s;
e 1 x12 1 x11 >= 1 : 101;
core id 101;
delc 64;
pol 59 35 + s 29 + s 37 + s 43 + s 97 + s 95 + s;
e 1 ~x19 1 ~x12 >= 1 : 102;
pol 28 62 + s 88 + s 102 + s 37 + s 101 + s 74 + s 95 + s 98 + s 97 + s 96 + s;
e 1 x11 >= 1 : 103;
core id 103;
pol 27 103 + s;
e 1 ~x3 >= 1 : 104;
core id 104;
pol 30 103 + s;
e 1 ~x7 >= 1 : 105;
core id 105;
pol 33 103 + s;
e 1 ~x15 >= 1 : 106;
core id 106;
pol 34 103 + s;
e 1 ~x19 >= 1 : 107;
core id 107;
pol 62 98 + s 104 + s 95 + s 74 + s 107 + s;
e 1 x4 >= 1 : 108;
core id 108;
pol 65 106 + s 98 + s 74 + s 97 + s 107 + s;
e 1 x16 >= 1 : 109;
core id 109;
pol 36 108 + s;
e 1 ~x8 >= 1 : 110;
core id 110;
pol 37 108 + s;
e 1 ~x12 >= 1 : 111;
core id 111;
pol 38 109 + s 108 + s;
e >= 1 : 112;
core id 112;
output NONE;
conclusion UNSAT : 112;
end pseudo-Boolean proof;
"

#guard checkDIMACS php54 php54P1V2 == some (.unsat 112)

#guard (checkAugmentedDIMACS php54 php54P1V2).any (· matches .unsat _)

end CslibFrontierTests.Logics.Propositional.VeriPBCaDiCaL
