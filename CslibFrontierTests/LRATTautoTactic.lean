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

The certificate of contraposition comes from the test of
`Cslib.Logic.PL.Proposition.eval_prop_of_checkLRAT`. The others were produced by printing the
formula with `lrat_tauto?`, refuting it with CaDiCaL 3.0.0 (`cadical --lrat --no-binary`),
checking the proof with `lrat-check` of drat-trim, and dropping its deletion steps.
-/

public section

namespace CslibFrontierTests.LRATTautoTactic

open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### Contraposition -/

/-- A refutation of the numbered Tseitin transformation of the negated contraposition. -/
private def contrapositionCert : Array LRAT.IntAction := #[
  .addRup 23 #[-5, -2] #[18, 19],
  .addRup 24 #[-3, -1, -5] #[22, 23],
  .addRup 25 #[7, -3, -5] #[12, 24],
  .addRup 26 #[-3, -5, 8] #[25, 10],
  .addRup 27 #[8, -3] #[9, 26],
  .addRup 28 #[-3, 9] #[27, 7],
  .addRup 29 #[9] #[6, 28],
  .addRup 30 #[-11, 10] #[29, 4],
  .addRup 31 #[-11] #[30, 5],
  .addEmpty 32 #[1, 31]]

theorem contraposition : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto using contrapositionCert

/-- info: 'CslibFrontierTests.LRATTautoTactic.contraposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contraposition

/-- The atoms may be any propositions, here those of the local context. -/
example (a b : Prop) : (a → b) → ¬b → ¬a := by
  lrat_tauto using contrapositionCert

-- The formula the certificate refutes, with the atoms `p` and `q` as the variables 1 and 2.
/--
info: The numbered Tseitin transformation of the negated goal, in DIMACS form:
c 1 := p
c 2 := q
p cnf 11 22
11 0
11 9 0
11 -10 0
-11 -9 10 0
-10 0
9 3 0
9 -8 0
-9 -3 8 0
8 5 0
8 -7 0
-8 -5 7 0
7 1 0
7 -6 0
-7 -1 6 0
-6 0
5 2 0
5 -4 0
-5 -2 4 0
-4 0
3 1 0
3 -2 0
-3 -1 2 0
-/
#guard_msgs in
example : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto?
  lrat_tauto using contrapositionCert

-- A certificate with a wrong hint, 20 for 19 in its first step, is rejected.
/--
error: lrat_tauto: the LRAT checker rejected the certificate. It must refute the numbered Tseitin transformation of the negated goal, which `lrat_tauto?` prints.
-/
#guard_msgs in
example : ∀ p q : Prop, (p → q) → ¬q → ¬p := by
  lrat_tauto using contrapositionCert.set! 0 (.addRup 23 #[-5, -2] #[18, 20])

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
  .addRup 41 #[-17, 18] #[1, 4],
  .addRup 42 #[-17] #[5, 41],
  .addRup 43 #[5] #[42, 6],
  .addRup 44 #[-16] #[42, 7],
  .addRup 45 #[7] #[44, 9],
  .addRup 46 #[-15] #[44, 10],
  .addRup 47 #[-13] #[46, 12],
  .addRup 48 #[-14] #[46, 13],
  .addRup 49 #[-9, -12] #[47, 18],
  .addRup 50 #[12] #[23, 19],
  .addRup 51 #[-9] #[50, 49],
  .addRup 52 #[1] #[51, 24],
  .addRup 53 #[-8] #[51, 25],
  .addRup 54 #[-2, 6] #[45, 30],
  .addRup 55 #[-2] #[31, 54],
  .addRup 56 #[3] #[43, 32],
  .addRup 57 #[4] #[43, 33],
  .addEmpty 58 #[56, 52, 55, 40]]

/-- The atoms are `n < 3` and `f n = y`; `3 > n` is `n < 3` at reducible transparency. -/
theorem iffGoal : ∀ (n y : ℕ) (f : ℕ → ℕ),
    (n < 3 ↔ f n = y) → ¬f n = y → (3 > n → False) ∧ True ∨ False := by
  lrat_tauto using iffCert

/-- info: 'CslibFrontierTests.LRATTautoTactic.iffGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iffGoal

-- The goal has two atoms, and `¬`, `↔` and `True` are encoded with `imp` and `and`.
/--
info: The numbered Tseitin transformation of the negated goal, in DIMACS form:
c 1 := n < 3
c 2 := f n = y
p cnf 19 40
19 0
19 17 0
19 -18 0
-19 -17 18 0
-18 0
17 5 0
17 -16 0
-17 -5 16 0
16 7 0
16 -15 0
-16 -7 15 0
15 -13 0
15 -14 0
-15 13 14 0
-14 0
-13 9 0
-13 12 0
13 -9 -12 0
12 10 0
12 -11 0
-12 -10 11 0
-11 0
-10 0
9 1 0
9 -8 0
-9 -1 8 0
-8 0
7 2 0
7 -6 0
-7 -2 6 0
-6 0
-5 3 0
-5 4 0
5 -3 -4 0
4 2 0
4 -1 0
-4 -2 1 0
3 1 0
3 -2 0
-3 -1 2 0
-/
#guard_msgs in
example : ∀ (n y : ℕ) (f : ℕ → ℕ),
    (n < 3 ↔ f n = y) → ¬f n = y → (3 > n → False) ∧ True ∨ False := by
  lrat_tauto?
  lrat_tauto using iffCert

/-! ### The pigeonhole principle for four pigeons and three holes -/

/-- A refutation for `pigeonhole`, of 130 RUP steps. -/
private def pigeonholeCert : Array LRAT.IntAction := #[
  .addRup 147 #[-59, 60] #[1, 4],
  .addRup 148 #[-59] #[5, 147],
  .addRup 149 #[14] #[148, 6],
  .addRup 150 #[-58] #[148, 7],
  .addRup 151 #[16] #[150, 9],
  .addRup 152 #[-57] #[150, 10],
  .addRup 153 #[18] #[152, 12],
  .addRup 154 #[-56] #[152, 13],
  .addRup 155 #[20] #[154, 15],
  .addRup 156 #[-55] #[154, 16],
  .addRup 157 #[-21] #[156, 18],
  .addRup 158 #[-54] #[156, 19],
  .addRup 159 #[-22] #[158, 21],
  .addRup 160 #[-53] #[158, 22],
  .addRup 161 #[-23] #[160, 24],
  .addRup 162 #[-52] #[160, 25],
  .addRup 163 #[-24] #[162, 27],
  .addRup 164 #[-51] #[162, 28],
  .addRup 165 #[-25] #[164, 30],
  .addRup 166 #[-50] #[164, 31],
  .addRup 167 #[-26] #[166, 33],
  .addRup 168 #[-49] #[166, 34],
  .addRup 169 #[-27] #[168, 36],
  .addRup 170 #[-48] #[168, 37],
  .addRup 171 #[-28] #[170, 39],
  .addRup 172 #[-47] #[170, 40],
  .addRup 173 #[-29] #[172, 42],
  .addRup 174 #[-46] #[172, 43],
  .addRup 175 #[-30] #[174, 45],
  .addRup 176 #[-45] #[174, 46],
  .addRup 177 #[-31] #[176, 48],
  .addRup 178 #[-44] #[176, 49],
  .addRup 179 #[-32] #[178, 51],
  .addRup 180 #[-43] #[178, 52],
  .addRup 181 #[-33] #[180, 54],
  .addRup 182 #[-42] #[180, 55],
  .addRup 183 #[-34] #[182, 57],
  .addRup 184 #[-41] #[182, 58],
  .addRup 185 #[-35] #[184, 60],
  .addRup 186 #[-40] #[184, 61],
  .addRup 187 #[-36] #[186, 63],
  .addRup 188 #[-39] #[186, 64],
  .addRup 189 #[-37] #[188, 66],
  .addRup 190 #[-38] #[188, 67],
  .addRup 191 #[-9, -12] #[190, 71],
  .addRup 192 #[-6, -12] #[189, 74],
  .addRup 193 #[-6, -9] #[187, 77],
  .addRup 194 #[-3, -12] #[185, 80],
  .addRup 195 #[-3, -9] #[183, 83],
  .addRup 196 #[-3, -6] #[181, 86],
  .addRup 197 #[-8, -11] #[179, 89],
  .addRup 198 #[-5, -11] #[177, 92],
  .addRup 199 #[-5, -8] #[175, 95],
  .addRup 200 #[-2, -11] #[173, 98],
  .addRup 201 #[-2, -8] #[171, 101],
  .addRup 202 #[-2, -5] #[169, 104],
  .addRup 203 #[-7, -10] #[167, 107],
  .addRup 204 #[-4, -10] #[165, 110],
  .addRup 205 #[-4, -7] #[163, 113],
  .addRup 206 #[-1, -10] #[161, 116],
  .addRup 207 #[-1, -7] #[159, 119],
  .addRup 208 #[-1, -4] #[157, 122],
  .addRup 209 #[10, 19] #[155, 125],
  .addRup 210 #[7, 17] #[153, 131],
  .addRup 211 #[4, 15] #[151, 137],
  .addRup 212 #[1, 13] #[149, 143],
  .addRup 213 #[13, -10] #[206, 212],
  .addRup 214 #[13, -7] #[207, 212],
  .addRup 215 #[13, -4] #[208, 212],
  .addRup 216 #[15, -10] #[204, 211],
  .addRup 217 #[15, -7] #[205, 211],
  .addRup 218 #[15, 13] #[215, 211],
  .addRup 219 #[17, -10] #[203, 210],
  .addRup 220 #[17, 13] #[214, 210],
  .addRup 221 #[17, 15] #[217, 210],
  .addRup 222 #[19, 13] #[213, 209],
  .addRup 223 #[19, 15] #[216, 209],
  .addRup 224 #[19, 17] #[219, 209],
  .addRup 225 #[-11, -13, 3] #[146, 200],
  .addRup 226 #[-8, -13, 3] #[146, 201],
  .addRup 227 #[-5, -13, 3] #[146, 202],
  .addRup 228 #[-11, -15, 6] #[140, 198],
  .addRup 229 #[-8, -15, 6] #[140, 199],
  .addRup 230 #[-15, 6, -13, 3] #[227, 140],
  .addRup 231 #[-11, -17, 9] #[134, 197],
  .addRup 232 #[-17, 9, -13, 3] #[226, 134],
  .addRup 233 #[-17, 9, -15, 6] #[229, 134],
  .addRup 234 #[12, -19, -13, 3] #[225, 128],
  .addRup 235 #[12, -19, -15, 6] #[228, 128],
  .addRup 236 #[12, -19, -17, 9] #[231, 128],
  .addRup 237 #[-12, -15, 6, -13] #[230, 194],
  .addRup 238 #[-9, -15, 6, -13] #[230, 195],
  .addRup 239 #[-12, -17, 9, -13] #[232, 194],
  .addRup 240 #[-6, -17, 9, -13] #[232, 196],
  .addRup 241 #[-9, 12, -19, -13] #[234, 195],
  .addRup 242 #[-6, 12, -19, -13] #[234, 196],
  .addRup 243 #[13, -17, 9, 6] #[233, 218],
  .addRup 244 #[13, 12, -19, 6] #[235, 218],
  .addRup 245 #[17, 12, -19, 6] #[235, 221],
  .addRup 246 #[17, -12, 6, -13] #[237, 221],
  .addRup 247 #[17, -9, 6, -13] #[238, 221],
  .addRup 248 #[19, -17, 9, 6] #[233, 223],
  .addRup 249 #[19, -12, 6, -13] #[237, 223],
  .addRup 250 #[19, -9, 6, -13] #[238, 223],
  .addRup 251 #[-12, -17, -13] #[239, 191],
  .addRup 252 #[-6, -17, -13] #[240, 193],
  .addRup 253 #[-6, 12, -19, -17] #[236, 193],
  .addRup 254 #[12, -19, -17, -13] #[241, 236],
  .addRup 255 #[-12, 13, -17, 6] #[243, 191],
  .addRup 256 #[-12, 19, -17, 6] #[248, 191],
  .addRup 257 #[19, -17, 6, -13] #[250, 248],
  .addRup 258 #[17, -12, -13] #[246, 192],
  .addRup 259 #[19, -12, -13] #[249, 192],
  .addRup 260 #[-12, 13, -17] #[255, 192],
  .addRup 261 #[-12, 19, -17] #[256, 192],
  .addRup 262 #[19, -17, -13] #[257, 252],
  .addRup 263 #[12, -19, -13, 17] #[245, 242],
  .addRup 264 #[12, -19, -17, 13] #[244, 253],
  .addRup 265 #[12, -19, -13] #[254, 263],
  .addRup 266 #[12, -19, -17] #[264, 265],
  .addRup 267 #[-19, -13, -17] #[251, 265],
  .addRup 268 #[-19, -13, 17] #[258, 265],
  .addRup 269 #[-19, -17, -13] #[251, 266],
  .addRup 270 #[-19, -17, 13] #[260, 266],
  .addRup 271 #[-19, -13] #[268, 267],
  .addRup 272 #[-19, -17] #[270, 267],
  .addRup 273 #[17, -19] #[271, 220],
  .addRup 274 #[19, -17] #[262, 222],
  .addRup 275 #[17] #[224, 273],
  .addRup 276 #[-19] #[275, 272],
  .addEmpty 277 #[276, 275, 274]]

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

end CslibFrontierTests.LRATTautoTactic
