/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of the lrat_tauto tactic)

import CslibFrontier.Tactic.LRATTauto

/-!
# Tests for `lrat_tauto`

The tests of `lrat_tauto` without `using` let the CDCL solver generate the certificate. In those
of `lrat_tauto using`, the certificate of contraposition comes from the test of
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT`. The others were produced by printing the
formula with `lrat_tauto?`, refuting it with CaDiCaL 3.0.0 (`cadical --lrat --no-binary`),
checking the proof with `lrat-check` of drat-trim, and dropping its deletion steps.
-/

public section

namespace CslibFrontierTests.LRATTautoTactic

open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### Contraposition -/

/-- A refutation of the numbered Plaisted–Greenbaum transformation of the negated
contraposition. -/
private def contrapositionCert : Array LRAT.IntAction := #[
  .addRup 13 #[-9, 10] #[1, 2],
  .addRup 14 #[-9] #[3, 13],
  .addRup 15 #[3] #[14, 4],
  .addRup 16 #[-8] #[14, 5],
  .addRup 17 #[5] #[16, 6],
  .addRup 18 #[-7] #[16, 7],
  .addRup 19 #[1] #[18, 8],
  .addRup 20 #[-6] #[18, 9],
  .addRup 21 #[-2, 4] #[17, 10],
  .addRup 22 #[-2] #[11, 21],
  .addEmpty 23 #[15, 19, 22, 12]]

theorem contraposition : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto using contrapositionCert

/--
info: 'CslibFrontierTests.LRATTautoTactic.contraposition' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms contraposition

/-- The atoms may be any propositions, here those of the local context. -/
example (a b : Prop) : (a → b) → ¬b → ¬a := by
  lrat_tauto using contrapositionCert

-- The formula the certificate refutes, with the atoms `p` and `q` as the variables 1 and 2.
/--
info: The numbered Plaisted–Greenbaum transformation of the negated goal, in DIMACS form:
c 1 := p
c 2 := q
p cnf 11 12
11 0
-11 -9 10 0
-10 0
9 3 0
9 -8 0
8 5 0
8 -7 0
7 1 0
7 -6 0
-5 -2 4 0
-4 0
-3 -1 2 0
-/
#guard_msgs in
example : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto?
  lrat_tauto using contrapositionCert

-- A certificate with a wrong hint, 3 for 2 in its first step, is rejected.
/--
error: lrat_tauto: the LRAT checker rejected the certificate. It must refute the numbered
Plaisted–Greenbaum transformation of the negated goal, which `lrat_tauto?` prints.
-/
#guard_msgs (whitespace := lax) in
example : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto using contrapositionCert.set! 0 (.addRup 13 #[-9, 10] #[1, 3])

-- A certificate the kernel cannot evaluate is reported as such.
/--
error: lrat_tauto: the kernel could not evaluate the LRAT checker on the certificate
  Classical.choice ⋯
It must be a closed term whose definition the kernel can unfold.
-/
#guard_msgs in
example : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto using Classical.choice ⟨#[]⟩

/-- A certificate for another goal is rejected. -/
example : ∀ p q : Prop, (p → q) → p → q := by
  fail_if_success lrat_tauto using contrapositionCert
  exact fun _ _ h => h

/-! ### `↔`, `True`, `False` and compound atoms -/

/-- A refutation for `iffGoal`. -/
private def iffCert : Array LRAT.IntAction := #[
  .addRup 22 #[-17, 18] #[1, 2],
  .addRup 23 #[-17] #[3, 22],
  .addRup 24 #[5] #[23, 4],
  .addRup 25 #[-16] #[23, 5],
  .addRup 26 #[7] #[25, 6],
  .addRup 27 #[-15] #[25, 7],
  .addRup 28 #[-13] #[27, 8],
  .addRup 29 #[-14] #[27, 9],
  .addRup 30 #[-9, -12] #[28, 10],
  .addRup 31 #[12] #[13, 11],
  .addRup 32 #[-9] #[31, 30],
  .addRup 33 #[1] #[32, 14],
  .addRup 34 #[-8] #[32, 15],
  .addRup 35 #[-2, 6] #[26, 16],
  .addRup 36 #[-2] #[17, 35],
  .addRup 37 #[3] #[24, 18],
  .addRup 38 #[4] #[24, 19],
  .addEmpty 39 #[37, 33, 36, 21]]

/-- The atoms are `n < 3` and `f n = y`; `3 > n` is `n < 3` at reducible transparency. -/
theorem iffGoal : ∀ (n y : ℕ) (f : ℕ → ℕ),
    (n < 3 ↔ f n = y) → ¬f n = y → (3 > n → False) ∧ True ∨ False := by
  lrat_tauto using iffCert

/--
info: 'CslibFrontierTests.LRATTautoTactic.iffGoal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iffGoal

-- The goal has two atoms, and `¬`, `↔` and `True` are encoded with `imp` and `and`.
/--
info: The numbered Plaisted–Greenbaum transformation of the negated goal, in DIMACS form:
c 1 := n < 3
c 2 := f n = y
p cnf 19 21
19 0
-19 -17 18 0
-18 0
17 5 0
17 -16 0
16 7 0
16 -15 0
15 -13 0
15 -14 0
13 -9 -12 0
12 10 0
12 -11 0
-10 0
9 1 0
9 -8 0
-7 -2 6 0
-6 0
-5 3 0
-5 4 0
-4 -2 1 0
-3 -1 2 0
-/
#guard_msgs in
example : ∀ (n y : ℕ) (f : ℕ → ℕ),
    (n < 3 ↔ f n = y) → ¬f n = y → (3 > n → False) ∧ True ∨ False := by
  lrat_tauto?
  lrat_tauto using iffCert

/-! ### The pigeonhole principle for four pigeons and three holes -/

/-- A refutation for `pigeonhole`, of 117 RUP steps. -/
private def pigeonholeCert : Array LRAT.IntAction := #[
  .addRup 72 #[-59, 60] #[1, 2],
  .addRup 73 #[-59] #[3, 72],
  .addRup 74 #[14] #[73, 4],
  .addRup 75 #[-58] #[73, 5],
  .addRup 76 #[16] #[75, 6],
  .addRup 77 #[-57] #[75, 7],
  .addRup 78 #[18] #[77, 8],
  .addRup 79 #[-56] #[77, 9],
  .addRup 80 #[20] #[79, 10],
  .addRup 81 #[-55] #[79, 11],
  .addRup 82 #[-21] #[81, 12],
  .addRup 83 #[-54] #[81, 13],
  .addRup 84 #[-22] #[83, 14],
  .addRup 85 #[-53] #[83, 15],
  .addRup 86 #[-23] #[85, 16],
  .addRup 87 #[-52] #[85, 17],
  .addRup 88 #[-24] #[87, 18],
  .addRup 89 #[-51] #[87, 19],
  .addRup 90 #[-25] #[89, 20],
  .addRup 91 #[-50] #[89, 21],
  .addRup 92 #[-26] #[91, 22],
  .addRup 93 #[-49] #[91, 23],
  .addRup 94 #[-27] #[93, 24],
  .addRup 95 #[-48] #[93, 25],
  .addRup 96 #[-28] #[95, 26],
  .addRup 97 #[-47] #[95, 27],
  .addRup 98 #[-29] #[97, 28],
  .addRup 99 #[-46] #[97, 29],
  .addRup 100 #[-30] #[99, 30],
  .addRup 101 #[-45] #[99, 31],
  .addRup 102 #[-31] #[101, 32],
  .addRup 103 #[-44] #[101, 33],
  .addRup 104 #[-32] #[103, 34],
  .addRup 105 #[-43] #[103, 35],
  .addRup 106 #[-33] #[105, 36],
  .addRup 107 #[-42] #[105, 37],
  .addRup 108 #[-34] #[107, 38],
  .addRup 109 #[-41] #[107, 39],
  .addRup 110 #[-35] #[109, 40],
  .addRup 111 #[-40] #[109, 41],
  .addRup 112 #[-36] #[111, 42],
  .addRup 113 #[-39] #[111, 43],
  .addRup 114 #[-37] #[113, 44],
  .addRup 115 #[-38] #[113, 45],
  .addRup 116 #[-9, -12] #[115, 46],
  .addRup 117 #[-6, -12] #[114, 47],
  .addRup 118 #[-6, -9] #[112, 48],
  .addRup 119 #[-3, -12] #[110, 49],
  .addRup 120 #[-3, -9] #[108, 50],
  .addRup 121 #[-3, -6] #[106, 51],
  .addRup 122 #[-8, -11] #[104, 52],
  .addRup 123 #[-5, -11] #[102, 53],
  .addRup 124 #[-5, -8] #[100, 54],
  .addRup 125 #[-2, -11] #[98, 55],
  .addRup 126 #[-2, -8] #[96, 56],
  .addRup 127 #[-2, -5] #[94, 57],
  .addRup 128 #[-7, -10] #[92, 58],
  .addRup 129 #[-4, -10] #[90, 59],
  .addRup 130 #[-4, -7] #[88, 60],
  .addRup 131 #[-1, -10] #[86, 61],
  .addRup 132 #[-1, -7] #[84, 62],
  .addRup 133 #[-1, -4] #[82, 63],
  .addRup 134 #[10, 19] #[80, 64],
  .addRup 135 #[7, 17] #[78, 66],
  .addRup 136 #[4, 15] #[76, 68],
  .addRup 137 #[1, 13] #[74, 70],
  .addRup 138 #[1, 2, 3] #[71, 137],
  .addRup 139 #[4, 5, 6] #[69, 136],
  .addRup 140 #[7, 8, 9] #[67, 135],
  .addRup 141 #[10, 11, 12] #[65, 134],
  .addRup 142 #[-10, 2, 3] #[138, 131],
  .addRup 143 #[-7, 2, 3] #[138, 132],
  .addRup 144 #[-4, 2, 3] #[138, 133],
  .addRup 145 #[-10, 5, 6] #[139, 129],
  .addRup 146 #[-7, 5, 6] #[139, 130],
  .addRup 147 #[5, 6, 2, 3] #[144, 139],
  .addRup 148 #[-10, 8, 9] #[140, 128],
  .addRup 149 #[8, 9, 2, 3] #[143, 140],
  .addRup 150 #[8, 9, 5, 6] #[146, 140],
  .addRup 151 #[11, 12, 2, 3] #[142, 141],
  .addRup 152 #[11, 12, 5, 6] #[145, 141],
  .addRup 153 #[11, 12, 8, 9] #[148, 141],
  .addRup 154 #[-11, 5, 6, 3] #[147, 125],
  .addRup 155 #[-8, 5, 6, 3] #[147, 126],
  .addRup 156 #[-11, 8, 9, 3] #[149, 125],
  .addRup 157 #[-5, 8, 9, 3] #[149, 127],
  .addRup 158 #[-8, 11, 12, 3] #[151, 126],
  .addRup 159 #[-5, 11, 12, 3] #[151, 127],
  .addRup 160 #[-11, 6, 3] #[154, 123],
  .addRup 161 #[-8, 6, 3] #[155, 124],
  .addRup 162 #[-11, 8, 9, 6] #[150, 123],
  .addRup 163 #[8, 9, 6, 3] #[157, 150],
  .addRup 164 #[8, 9, 6, 11, 12, 3] #[159, 150],
  .addRup 165 #[-8, 11, 12, 6] #[152, 124],
  .addRup 166 #[11, 12, 6, 8, 9, 3] #[157, 152],
  .addRup 167 #[11, 12, 6, 3] #[159, 152],
  .addRup 168 #[-12, -11, 8, 3] #[156, 116],
  .addRup 169 #[-12, -11, 8, 6] #[162, 116],
  .addRup 170 #[-12, 8, 6, 3] #[163, 116],
  .addRup 171 #[-6, 11, 12, 8] #[153, 118],
  .addRup 172 #[-6, -11, 8, 3] #[156, 118],
  .addRup 173 #[-3, 11, 12, 8] #[153, 120],
  .addRup 174 #[-3, -11, 8, 6] #[162, 120],
  .addRup 175 #[-6, 11, 8] #[171, 117],
  .addRup 176 #[-3, 11, 8] #[173, 119],
  .addRup 177 #[-6, -8, 11, 3] #[158, 117],
  .addRup 178 #[-3, -8, 11, 6] #[165, 119],
  .addRup 179 #[11, 6, 3, 8] #[170, 167],
  .addRup 180 #[-6, -11, 8] #[172, 121],
  .addRup 181 #[-6, -8, 11] #[177, 121],
  .addRup 182 #[11, 6, 8] #[179, 176],
  .addRup 183 #[-11, 8, 6] #[174, 160],
  .addRup 184 #[-8, 11, 6] #[178, 161],
  .addRup 185 #[11, 8] #[175, 182],
  .addRup 186 #[-11, 8] #[180, 183],
  .addRup 187 #[-8, 11] #[181, 184],
  .addRup 188 #[11] #[187, 185],
  .addEmpty 189 #[188, 122, 186]]

/-- If each of four pigeons sits in one of three holes, two share a hole. -/
theorem pigeonhole : ∀ p : Fin 4 → Fin 3 → Prop,
    (p 0 0 ∨ p 0 1 ∨ p 0 2) → (p 1 0 ∨ p 1 1 ∨ p 1 2) → (p 2 0 ∨ p 2 1 ∨ p 2 2) →
    (p 3 0 ∨ p 3 1 ∨ p 3 2) →
    (p 0 0 ∧ p 1 0) ∨ (p 0 0 ∧ p 2 0) ∨ (p 0 0 ∧ p 3 0) ∨ (p 1 0 ∧ p 2 0) ∨
    (p 1 0 ∧ p 3 0) ∨ (p 2 0 ∧ p 3 0) ∨
    (p 0 1 ∧ p 1 1) ∨ (p 0 1 ∧ p 2 1) ∨ (p 0 1 ∧ p 3 1) ∨ (p 1 1 ∧ p 2 1) ∨
    (p 1 1 ∧ p 3 1) ∨ (p 2 1 ∧ p 3 1) ∨
    (p 0 2 ∧ p 1 2) ∨ (p 0 2 ∧ p 2 2) ∨ (p 0 2 ∧ p 3 2) ∨ (p 1 2 ∧ p 2 2) ∨
    (p 1 2 ∧ p 3 2) ∨ (p 2 2 ∧ p 3 2) := by
  lrat_tauto using pigeonholeCert

/-! ### Certificates generated by the CDCL solver -/

theorem contraposition_solved : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto

/--
info: 'CslibFrontierTests.LRATTautoTactic.contraposition_solved' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms contraposition_solved

/-- The goal of `iffGoal`, with its compound atoms. -/
example : ∀ (n y : ℕ) (f : ℕ → ℕ),
    (n < 3 ↔ f n = y) → ¬f n = y → (3 > n → False) ∧ True ∨ False := by
  lrat_tauto

/-- Peirce's law, which needs classical logic. -/
example (p q : Prop) : ((p → q) → p) → p := by
  lrat_tauto

/-- Distributivity of `∧` over `∨` on three disjunctions, slow for `tauto`. -/
example (a b : Fin 3 → Prop) : (a 0 ∨ b 0) ∧ (a 1 ∨ b 1) ∧ (a 2 ∨ b 2) →
    (a 0 ∧ a 1 ∧ a 2) ∨ (a 0 ∧ a 1 ∧ b 2) ∨ (a 0 ∧ b 1 ∧ a 2) ∨ (a 0 ∧ b 1 ∧ b 2) ∨
    (b 0 ∧ a 1 ∧ a 2) ∨ (b 0 ∧ a 1 ∧ b 2) ∨ (b 0 ∧ b 1 ∧ a 2) ∨ (b 0 ∧ b 1 ∧ b 2) := by
  lrat_tauto

/-- If each of three pigeons sits in one of two holes, two share a hole. -/
example : ∀ p : Fin 3 → Fin 2 → Prop,
    (p 0 0 ∨ p 0 1) → (p 1 0 ∨ p 1 1) → (p 2 0 ∨ p 2 1) →
    (p 0 0 ∧ p 1 0) ∨ (p 0 0 ∧ p 2 0) ∨ (p 1 0 ∧ p 2 0) ∨
    (p 0 1 ∧ p 1 1) ∨ (p 0 1 ∧ p 2 1) ∨ (p 1 1 ∧ p 2 1) := by
  lrat_tauto

/-- If each of five pigeons sits in one of four holes, two share a hole. The kernel check of the
solver's certificate took about 8 seconds with the checker on lists, and takes about 1 with the
kernel checker. -/
example : ∀ p : Fin 5 → Fin 4 → Prop,
    (p 0 0 ∨ p 0 1 ∨ p 0 2 ∨ p 0 3) → (p 1 0 ∨ p 1 1 ∨ p 1 2 ∨ p 1 3) →
    (p 2 0 ∨ p 2 1 ∨ p 2 2 ∨ p 2 3) → (p 3 0 ∨ p 3 1 ∨ p 3 2 ∨ p 3 3) →
    (p 4 0 ∨ p 4 1 ∨ p 4 2 ∨ p 4 3) →
    (p 0 0 ∧ p 1 0) ∨ (p 0 0 ∧ p 2 0) ∨ (p 0 0 ∧ p 3 0) ∨ (p 0 0 ∧ p 4 0) ∨ (p 1 0 ∧ p 2 0) ∨
    (p 1 0 ∧ p 3 0) ∨ (p 1 0 ∧ p 4 0) ∨ (p 2 0 ∧ p 3 0) ∨ (p 2 0 ∧ p 4 0) ∨ (p 3 0 ∧ p 4 0) ∨
    (p 0 1 ∧ p 1 1) ∨ (p 0 1 ∧ p 2 1) ∨ (p 0 1 ∧ p 3 1) ∨ (p 0 1 ∧ p 4 1) ∨ (p 1 1 ∧ p 2 1) ∨
    (p 1 1 ∧ p 3 1) ∨ (p 1 1 ∧ p 4 1) ∨ (p 2 1 ∧ p 3 1) ∨ (p 2 1 ∧ p 4 1) ∨ (p 3 1 ∧ p 4 1) ∨
    (p 0 2 ∧ p 1 2) ∨ (p 0 2 ∧ p 2 2) ∨ (p 0 2 ∧ p 3 2) ∨ (p 0 2 ∧ p 4 2) ∨ (p 1 2 ∧ p 2 2) ∨
    (p 1 2 ∧ p 3 2) ∨ (p 1 2 ∧ p 4 2) ∨ (p 2 2 ∧ p 3 2) ∨ (p 2 2 ∧ p 4 2) ∨ (p 3 2 ∧ p 4 2) ∨
    (p 0 3 ∧ p 1 3) ∨ (p 0 3 ∧ p 2 3) ∨ (p 0 3 ∧ p 3 3) ∨ (p 0 3 ∧ p 4 3) ∨ (p 1 3 ∧ p 2 3) ∨
    (p 1 3 ∧ p 3 3) ∨ (p 1 3 ∧ p 4 3) ∨ (p 2 3 ∧ p 3 3) ∨ (p 2 3 ∧ p 4 3) ∨ (p 3 3 ∧ p 4 3) := by
  lrat_tauto

-- A goal that is not a tautology is refuted by an assignment to its atoms.
/--
error: lrat_tauto: the goal is not a propositional tautology. It is false under this assignment
to its atoms, read as independent propositions: p := False q := True
-/
#guard_msgs (whitespace := lax) in
example : ∀ p q : Prop, (p → q) → q → p := by
  lrat_tauto

-- The assignment is to the atoms as opaque propositions: `0 + n = n` is one atom, assigned
-- `False`, though the goal holds.
/--
error: lrat_tauto: the goal is not a propositional tautology. It is false under this assignment
to its atoms, read as independent propositions: 0 + n = n := False
-/
#guard_msgs (whitespace := lax) in
example : ∀ n : ℕ, 0 + n = n := by
  lrat_tauto

/-! ### Hypotheses of the context -/

/-- Modus ponens and modus tollens from the context. -/
theorem hyps_solved (p q r : Prop) (hpq : p → q) (hqr : q → r) (hnr : ¬r) : ¬p := by
  lrat_tauto

/--
info: 'CslibFrontierTests.LRATTautoTactic.hyps_solved' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hyps_solved

/-- The hypotheses are used with the goal's own premises, over shared atoms. -/
example (p q r : Prop) (h : p ∨ q) (hp : p → r) : (q → r) → r := by
  lrat_tauto

/-- A contradiction in the context proves any goal, even one that is a single atom. -/
example (p : Prop) (n : ℕ) (h₁ : p) (h₂ : ¬p) : n = 37 := by
  lrat_tauto

/-- Hypotheses that are not propositional formulas are atoms: here `∀ x, f x = 0` and
`f 1 = 0`, the latter shared with the goal. -/
example (f : ℕ → ℕ) (h : ∀ x, f x = 0) (h₁ : f 1 = 0 → f 2 = 0) (h₂ : f 1 = 0) :
    f 2 = 0 ∧ (∀ x, f x = 0) := by
  lrat_tauto

/-- Hypotheses whose types depend on other hypotheses and on variables of the context. -/
example (p : Prop) (f : p → ℕ) (hp : p) (h : f hp = 0 ∨ f hp = 1) (h₀ : f hp ≠ 0) :
    f hp = 1 := by
  lrat_tauto

/-- `-hyps` turns the hypotheses off. -/
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  fail_if_success lrat_tauto -hyps
  lrat_tauto

-- Unknown options are rejected.
/-- error: lrat_tauto: unknown option; the only option is `-hyps` -/
#guard_msgs in
example (p : Prop) (hp : p) : p := by
  lrat_tauto -zeta

-- Only the hypotheses whose clauses the certificate uses reach the kernel, so the unused
-- variables linter flags the others.
/--
warning: Variable name `hq` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively,
prefix the name with `_` to silence this warning:
  [apply] _hq

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `hpq` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively,
prefix the name with `_` to silence this warning:
  [apply] _hpq

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs (whitespace := lax) in
example (p q r : Prop) (hq : q) (hpq : p → q) (hr : r) (hrp : r → p) : p := by
  lrat_tauto

/-- Twenty irrelevant hypotheses, none of which reaches the kernel. -/
example (a b : Fin 20 → Prop) (p q : Prop)
    (_h0 : a 0 ∨ b 0) (_h1 : a 1 ∨ b 1) (_h2 : a 2 ∨ b 2) (_h3 : a 3 ∨ b 3) (_h4 : a 4 ∨ b 4)
    (_h5 : a 5 ∨ b 5) (_h6 : a 6 ∨ b 6) (_h7 : a 7 ∨ b 7) (_h8 : a 8 ∨ b 8) (_h9 : a 9 ∨ b 9)
    (_h10 : a 10 → b 10) (_h11 : a 11 → b 11) (_h12 : a 12 → b 12) (_h13 : a 13 → b 13)
    (_h14 : a 14 → b 14) (_h15 : a 15 → b 15) (_h16 : a 16 → b 16) (_h17 : a 17 → b 17)
    (_h18 : a 18 → b 18) (_h19 : a 19 → b 19)
    (hp : p) (hpq : p → q) (hq : q → a 0) : a 0 := by
  lrat_tauto

-- When the goal does not follow, the error names the hypotheses used and the assignment.
/--
error: lrat_tauto: the goal does not follow propositionally from the hypotheses hpq, hq. It is
false, and the hypotheses are true, under this assignment to the atoms of the goal and the
hypotheses, read as independent propositions: p := False q := True
-/
#guard_msgs (whitespace := lax) in
example (p q : Prop) (hpq : p → q) (hq : q) : p := by
  lrat_tauto

/-- A certificate supplied with `using` refutes the goal alone, so the hypotheses are ignored. -/
example (p q : Prop) (_hpq : p → q) (_hnq : ¬q) : (p → q) → ¬q → ¬p := by
  lrat_tauto using contrapositionCert

/-! ### Terms as premises -/

/-- Terms are premises like the hypotheses: here an instance of the universally quantified `h`,
which is an atom as a hypothesis, and of the lemma `Nat.le_total`. -/
theorem terms_used (f : ℕ → ℕ) (h : ∀ a, f a = 0 ∨ f a = 1) (a x y : ℕ) (hne : f a ≠ 0)
    (hxy : ¬x ≤ y) : f a = 1 ∧ y ≤ x := by
  fail_if_success lrat_tauto
  lrat_tauto [h a, Nat.le_total x y]

/-- Terms that the certificate does not need are dropped with the unused hypotheses. -/
theorem terms_dropped (p q : ℕ → Prop) (h : ∀ n, p n → q n) (h₀ : p 0) : q 0 := by
  lrat_tauto [Nat.le_total 0 1, h 0, Nat.lt_irrefl 2]

-- The proof of `terms_used` cites both terms, that of `terms_dropped` neither of the unused ones.
open Lean in
run_meta do
  -- The bodies of theorems are not exported, so they are read from the private view.
  let env := (← getEnv).setExporting false
  let usedIn (n : Name) : MetaM NameSet := do
    let some (.thmInfo ci) := env.find? n | throwError "no theorem {n}"
    return ci.value.getUsedConstantsAsSet
  unless (← usedIn ``terms_used).contains ``Nat.le_total do
    throwError "`Nat.le_total` is missing from the proof of `terms_used`"
  let used ← usedIn ``terms_dropped
  if used.contains ``Nat.le_total || used.contains ``Nat.lt_irrefl then
    throwError "an unused term reached the proof of `terms_dropped`"

-- Of the two hypotheses and three terms, the hypothesis `h₀` and the term `h 0` are used.
/-- [lrat_tauto] 2 of the 5 premises are used; the formula is read again from them -/
#guard_msgs (substring := true) in
example (p q : ℕ → Prop) (h : ∀ n, p n → q n) (h₀ : p 0) : q 0 := by
  set_option trace.lrat_tauto true in
  lrat_tauto [Nat.le_total 0 1, h 0, Nat.lt_irrefl 2]

/-- A type ascription gives the premise its type, as `have h : T := t` would: the type inferred
for `Or.inl rfl` is `3 = 3 ∨ 3 ∈ {4}`, which is not the atom `3 ∈ {3, 4}` at reducible
transparency. -/
example : 3 ∈ ({3, 4} : Set ℕ) ∨ False := by
  lrat_tauto [(Or.inl rfl : 3 ∈ ({3, 4} : Set ℕ))]

/-- With `-hyps`, the terms are still premises. -/
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  fail_if_success lrat_tauto -hyps
  lrat_tauto -hyps [hp, hpq]

-- When the goal does not follow, the error names the terms.
/--
error: lrat_tauto: the goal does not follow propositionally from the terms hpq. It is false, and
the terms are true, under this assignment to the atoms of the goal and the terms, read as
independent propositions: p := False q := False
-/
#guard_msgs (whitespace := lax) in
example (p q : Prop) (hpq : p → q) : p := by
  lrat_tauto -hyps [hpq]

-- A supplied certificate refutes the goal with the terms as premises, in the order given, and
-- without the hypotheses. Here that is the formula of `contraposition`.
/--
info: The numbered Plaisted–Greenbaum transformation of the negated goal, with the terms as
premises, in DIMACS form:
c 1 := p
c 2 := q
p cnf 11 12
11 0
-11 -9 10 0
-10 0
9 3 0
9 -8 0
8 5 0
8 -7 0
7 1 0
7 -6 0
-5 -2 4 0
-4 0
-3 -1 2 0
-/
#guard_msgs (whitespace := lax) in
example (p q : Prop) (hpq : p → q) (hnq : ¬q) : ¬p := by
  lrat_tauto? [hpq, hnq]
  lrat_tauto [hpq, hnq] using contrapositionCert

-- A term with metavariables left after elaboration is rejected.
/-- error: lrat_tauto: the term `h _` must elaborate fully, but it has metavariables: -/
#guard_msgs (substring := true) in
example (p q : ℕ → Prop) (h : ∀ n, p n → q n) (h₀ : p 0) : q 0 := by
  lrat_tauto [h _]

-- A term that is not a proof is rejected.
/--
error: lrat_tauto: the term `x` is not a proof of a proposition: its type is
  ℕ
-/
#guard_msgs in
example (x : ℕ) (h : x = x) : x = x := by
  lrat_tauto [x]

/-! ### Leaves closed by `rfl` and by a hypothesis -/

/-- `n = n` is one atom, which `rfl` proves. -/
example : ∀ n : ℕ, n = n := by
  lrat_tauto

/-- An atom proved by `rfl` at reducible transparency, here `HEq`, closes one side of a
disjunction. -/
example (p : Prop) (x : ℕ) : p ∨ HEq x x := by
  lrat_tauto

/-- `rfl` is tried at reducible transparency only: `0 + n = n` is not proved. -/
example (n : ℕ) : 0 + n = n ∨ False := by
  fail_if_success lrat_tauto
  simp

/-- An atom of the goal that is a hypothesis, as `assumption` closes it. -/
example (s : Set ℕ) (h : 3 ∈ s) : (3 ∈ s → False) → 4 ∈ s := by
  lrat_tauto

/-- An atom whose negation is a hypothesis. -/
example (x y : ℕ) (h : ¬x < y) : x < y → x = 7 := by
  lrat_tauto

/-! ### `≠` -/

/-- `a ≠ b` is read as `¬a = b`, so the hypothesis fixes the atom `a = b`. -/
example (a b : ℕ) (h : a ≠ b) : ¬a = b := by
  lrat_tauto

/-- `≠` and `=` over the same sides share their atom. -/
example (a b : ℕ) : a ≠ b ∨ a = b := by
  lrat_tauto

-- Equations are atoms: `a ≠ b → b = c → a ≠ c` needs `b = c` to be used as a rewrite, so it is
-- not propositional over the atoms `a = b`, `b = c` and `a = c`.
/--
error: lrat_tauto: the goal is not a propositional tautology. It is false under this assignment
to its atoms, read as independent propositions: a = b := False b = c := True a = c := True
-/
#guard_msgs (whitespace := lax) in
example (a b c : ℕ) : a ≠ b → b = c → a ≠ c := by
  lrat_tauto

/-- `a ≠ a` is `¬a = a`, and `rfl` proves the atom `a = a`. -/
example (p : Prop) (a : ℕ) : a ≠ a → p := by
  lrat_tauto

/-- The same from a hypothesis. -/
example (p : Prop) (a : ℕ) (h : a ≠ a) : p := by
  lrat_tauto

/-! ### Swapped equations -/

/-- `b = a` is read as the atom `a = b`, which occurs first. -/
example (p : Prop) (a b : ℕ) : (a = b → p) → b = a → p := by
  lrat_tauto

/-- A hypothesis `h : b = a` fixes the atom `a = b` of the goal, and a term's `f b = f a` the atom
`f a = f b` of a hypothesis. -/
example (p : Prop) (a b : ℕ) (f : ℕ → ℕ) (h : b = a) (hp : a = b → f a = f b → p)
    (hf : ∀ x y, x = y → f x = f y) : p ∧ a = b := by
  lrat_tauto [hf b a h]

/-- `a ≠ b` and `b ≠ a` are the negations of one atom. -/
example (a b : ℕ) : a ≠ b → b ≠ a := by
  lrat_tauto

example (a b : ℕ) (h : a ≠ b) (h' : b = a ∨ a < b) : a < b := by
  lrat_tauto

/-- The same for `HEq`. -/
example {α β : Type} (a : α) (b : β) (p : Prop) : (HEq a b → p) → HEq b a → p := by
  lrat_tauto

-- A goal false under independent atoms is still refuted: `a = b` is the atom `b = a`, so the
-- assignment has two atoms.
/--
error: lrat_tauto: the goal is not a propositional tautology. It is false under this assignment
to its atoms, read as independent propositions: b = a := True p := False
-/
#guard_msgs (whitespace := lax) in
example (p : Prop) (a b : ℕ) : b = a → a = b ∧ p := by
  lrat_tauto

-- Only the swap is identified: `b = a → c = b → a = c` needs transitivity.
/--
error: lrat_tauto: the goal is not a propositional tautology. It is false under this assignment
to its atoms, read as independent propositions: b = a := True c = b := True a = c := False
-/
#guard_msgs (whitespace := lax) in
example (a b c : ℕ) : b = a → c = b → a = c := by
  lrat_tauto

/-- A β-redex is reduced before it is read, so it is a formula over the atoms `a ∈ s` and
`a ∈ t`. -/
example (s t : Set ℕ) (a : ℕ) : (fun x => x ∈ s → x ∈ t) a ↔ ¬a ∈ s ∨ a ∈ t := by
  lrat_tauto

end CslibFrontierTests.LRATTautoTactic
