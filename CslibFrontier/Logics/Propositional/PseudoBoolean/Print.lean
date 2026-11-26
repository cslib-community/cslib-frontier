/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Dimacs
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Rename
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
-- `import all`: the round-trip proofs read the private lexer of `Text` through its specification
-- (`lines_eq_spec`, `tokens_eq_spec`, `lineTokens`, `lexLine`, `flushToken`), unfold its private
-- parsers (`nat?`, `dropChar?`, `startsWithChar`, `terms`, `constr`, `opbLines`, `objTerms`,
-- `objective`, `presVars`, `dimacsClauses`) and the unexposed bodies of `parseOPB`,
-- `parseOPBWith`, `opbTokenLines`, `parseDIMACS`, `splitChars`, `tokens`, `int?`, `stdVar?`,
-- `Names.var?` and `Names.nameChars`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! # Printing OPB instances, with round-trip theorems

A printer for the OPB instances read by the text front end of the VeriPB checker
(`Cslib.Logic.PL.VeriPB.Text.parseOPB`), and the theorems that the parsers read back what the
printers write, for OPB and for DIMACS (`Cslib.Logic.PL.CNF.toDIMACS`, read by
`Cslib.Logic.PL.VeriPB.Text.parseDIMACS`). With them, the soundness theorems of the checkers give
conclusions about an instance built in Lean from the acceptance of a proof against its printed
text, so that for such instances the parsers drop out of the trusted base. For text from
elsewhere, the parsers are still trusted to read it as intended; compiled code stays outside the
guarantee, trusted through Lean's compiler.

**The text.** `Cslib.Logic.PL.VeriPB.Text.printOPB` writes the header comment
`* #variable= n #constraint= m`, then the objective line `min: w₁ x₁ … [k];` if there is an
objective (its constant `k` only if it is not `0`), the line `preserved: …;` if there is a
preserved set, and one line `a₁ ℓ₁ … >= d;` per constraint, in order. The variable `v` is
written with its name `N.name v` (`Cslib.Logic.PL.VeriPB.Text.Names`), by default its standard
name `x(v + 1)` (`Cslib.Logic.PL.VeriPB.Text.stdNames`), the name the parser reads as `v` (as in
`Cslib.Logic.PL.Literal.ofDIMACS`), and a negative literal as `~x(v + 1)`. The `;` is a word of
its own, and every word is followed by a space. The printers are defined on lists of characters,
with the digits of `Nat.toDecimal` and `Int.toDecimal`, so the kernel evaluates them. Only
`printOPB` is public; the word builders behind it are private, and a client that evaluates it in
the kernel imports this module with `import all`, as
`CslibFrontierTests.Logics.Propositional.VeriPBPrintDecide` does.

**What is read back.** The parser normalizes: it merges the terms of a constraint on the same
variable, drops zero coefficients and moves the constants of negative literals into the degree,
and it merges the weights of an objective on the same variable. So it reads back
`Cslib.Logic.PL.VeriPB.Text.reread I` (`Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB`), which
has the same solutions and objective values as `I`
(`Cslib.Logic.PL.VeriPB.Text.holds_rereadConstr_iff`,
`Cslib.Logic.PL.VeriPB.Text.eval_rereadObj`), and is `I` itself when `I` is in the normal form
the parser produces (`Cslib.Logic.PL.VeriPB.Text.Normal`: in each constraint one term per
variable with a positive coefficient, in each objective one weight per variable;
`Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_normal`). DIMACS needs no hypothesis: every CNF
formula is read back (`Cslib.Logic.PL.VeriPB.Text.parseDIMACS_toDIMACS`).

**Names.** With other names, which must be well formed, name every variable, and give each
variable an OPB name, not a name `$a` of an auxiliary variable
(`Cslib.Logic.PL.VeriPB.Text.Names.Covers`), the parser
numbers the names in order of first appearance in the text. So it reads back the instance
renumbered by a map `π`, injective on its variables, that keeps every name
(`Cslib.Logic.PL.VeriPB.Text.exists_parseOPB_printOPB`); `π` is the identity, and the instance
read back is `reread I`, when the names read each variable as itself, which is decidable
(`Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_var?`), as for the
standard names. Renumbering changes no conclusion (`Cslib.Logic.PL.VeriPB.Instance.valuesVia_eq`),
so the soundness theorems end to end hold for every instance and every covering names; the
assignment of `SAT : ρ` is translated through the names.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Text.printOPB`: an instance as OPB text, with names.
* `Cslib.Logic.PL.VeriPB.Text.stdNames`, `Cslib.Logic.PL.VeriPB.Text.Names.Covers`: the standard
  names, and names that can print an instance.
* `Cslib.Logic.PL.VeriPB.Text.reread`: the instance the parser reads back.
* `Cslib.Logic.PL.VeriPB.Text.Normal`: the normal form of the parser.

## Main statements

* `Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_normal`,
  `Cslib.Logic.PL.VeriPB.Text.exists_parseOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_var?`,
  `Cslib.Logic.PL.VeriPB.Text.parseDIMACS_toDIMACS`: the round trips.
* `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.holds_of_checkOPB_printOPB_sat`,
  `Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.le_encard_of_checkOPB_printOPB_enumPartial`,
  `Cslib.Logic.PL.VeriPB.Text.encard_eq_of_checkOPB_printOPB_enumComplete`,
  `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS_toDIMACS`,
  `Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS_toDIMACS`: the soundness theorems end to
  end, from the acceptance of a proof against the printed text to the semantics of the instance
  or formula built in Lean, for every instance with covering names and every formula.
-/

public section

namespace Cslib.Logic.PL.VeriPB.Text

open PBConstr

/-! ### Printing -/

/-- A literal: the name of its variable, after `~` if it is negative. -/
private def litChars (N : Names) : Literal ℕ → List Char
  | (v, true) => N.nameChars v
  | (v, false) => '~' :: N.nameChars v

/-- The words of a term `a ℓ`. -/
private def termWords (N : Names) (t : ℕ × Literal ℕ) : List (List Char) :=
  [Nat.toDecimal t.1, litChars N t.2]

/-- The words of the constraint line `a₁ ℓ₁ … >= d;`. -/
private def constrWords (N : Names) (c : PBConstr) : List (List Char) :=
  c.terms.flatMap (termWords N) ++ [['>', '='], Nat.toDecimal c.degree, [';']]

/-- The words of the weights `w₁ x₁ …` of an objective, and of its constant if it is not `0`. -/
private def objTermWords (N : Names) (f : Objective) : List (List Char) :=
  f.lin.flatMap (fun e => [Int.toDecimal e.2, N.nameChars e.1]) ++
    if f.const = 0 then [] else [Int.toDecimal f.const]

/-- The words of the objective line `min: w₁ x₁ … [k];`. -/
private def objWords (N : Names) (f : Objective) : List (List Char) :=
  ['m', 'i', 'n', ':'] :: objTermWords N f ++ [[';']]

/-- The words of the line `preserved: x₁ …;`. -/
private def presWords (N : Names) (P : List ℕ) : List (List Char) :=
  ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 'd', ':'] :: P.map N.nameChars ++ [[';']]

/-- One more than the largest variable of an instance, `0` for none. -/
private def opbVars (I : Instance) : ℕ := I.varList.foldr (fun v m => max (v + 1) m) 0

/-- The words of the header comment `* #variable= n #constraint= m`. -/
private def headerWords (I : Instance) : List (List Char) :=
  [['*'], ['#', 'v', 'a', 'r', 'i', 'a', 'b', 'l', 'e', '='], Nat.toDecimal (opbVars I),
    ['#', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '='],
    Nat.toDecimal I.constraints.length]

/-- A line: its words, each followed by a space, and a newline. -/
private def renderLine (ws : List (List Char)) : List Char := ws.flatMap (· ++ [' ']) ++ ['\n']

/-- The lines of an instance after the header: the objective, the preserved set and the
constraints. -/
private def bodyLines (N : Names) (I : Instance) : List (List (List Char)) :=
  (I.objective.map (objWords N)).toList ++ (I.preserved.map (presWords N)).toList ++
    I.constraints.map (constrWords N)

/-- **The standard names of an instance**: every variable `v` of `I` is named `x(v + 1)`. -/
def stdNames (I : Instance) : Names := ⟨[], opbVars I⟩

/-- **An instance as OPB text, with the names `N`**: the header comment, the objective line if
there is an objective, the `preserved:` line if there is a preserved set, and one line per
constraint, the variable `v` written `N.name v`. By default `v` is written `x(v + 1)`
(`Cslib.Logic.PL.VeriPB.Text.stdNames`). -/
def printOPB (I : Instance) (N : Names := stdNames I) : String :=
  String.ofList ((headerWords I :: bodyLines N I).flatMap renderLine)

end Cslib.Logic.PL.VeriPB.Text

end

@[expose] public section

namespace Cslib.Logic.PL.VeriPB.Text

open PBConstr

/-! ### What is read back -/

/-- The linear form the parser reads from terms, after the linear form `L`: one entry per
variable, in order of first appearance. -/
def linOf (L : List (ℕ × ℤ)) (ts : List (ℕ × Literal ℕ)) : List (ℕ × ℤ) :=
  ts.foldl (fun L t => insertCoeff (termVar t) (termCoeff t) L) L

/-- The constant the parser reads from terms, after `k`: the coefficients of the negative
literals. -/
def negOf (k : ℤ) (ts : List (ℕ × Literal ℕ)) : ℤ :=
  ts.foldl (fun k t => k + if termPos t then 0 else (t.1 : ℤ)) k

/-- **The constraint the parser reads back from a printed constraint**: its terms merged on each
variable, zero coefficients dropped, and the constants of negative literals moved into the
degree. -/
def rereadConstr (c : PBConstr) : PBConstr :=
  fromLinear (linOf [] c.terms) (c.degree - negOf 0 c.terms)

/-- **The objective the parser reads back from a printed objective**: its weights merged on each
variable. -/
def rereadObj (f : Objective) : Objective :=
  ⟨f.lin.foldl (fun L e => insertCoeff e.1 e.2 L) [], f.const⟩

/-- **The instance the parser reads back from a printed instance.** -/
def reread (I : Instance) : Instance :=
  ⟨I.constraints.map rereadConstr, I.objective.map rereadObj, I.preserved⟩

/-- **The normal form of the parser**: each constraint has one term per variable, with a positive
coefficient, and each objective one weight per variable. On these instances the parser reads
back exactly what is printed (`Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_normal`). -/
structure Normal (I : Instance) : Prop where
  /-- The terms of each constraint are on distinct variables. -/
  constr_nodup : ∀ c ∈ I.constraints, (c.terms.map termVar).Nodup
  /-- The coefficients of each constraint are positive. -/
  constr_pos : ∀ c ∈ I.constraints, ∀ t ∈ c.terms, 0 < t.1
  /-- The weights of the objective are on distinct variables. -/
  obj_nodup : ∀ f ∈ I.objective, (f.lin.map Prod.fst).Nodup

instance (I : Instance) : Decidable (Normal I) :=
  decidable_of_iff ((∀ c ∈ I.constraints, (c.terms.map termVar).Nodup) ∧
      (∀ c ∈ I.constraints, ∀ t ∈ c.terms, 0 < t.1) ∧
      ∀ f ∈ I.objective, (f.lin.map Prod.fst).Nodup)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end Cslib.Logic.PL.VeriPB.Text

end

/-! ### Proofs -/

public section

namespace Cslib.Logic.PL.VeriPB.Text

open PBConstr Instance

/-! #### Lexing -/

/-- Splitting at the first separator. -/
private theorem splitChars_append {p : Char → Bool} {a : List Char} (b : List Char) {c : Char}
    (ha : ∀ x ∈ a, p x = false) (hc : p c = true) :
    splitChars p (a ++ c :: b) = a :: splitChars p b := by
  induction a with
  | nil => simp [splitChars, hc]
  | cons x a ih =>
    rw [List.cons_append, splitChars, ih fun y hy => ha y (List.mem_cons_of_mem _ hy)]
    simp [ha x List.mem_cons_self]

/-- A word of a printed line: `;`, or a nonempty word without whitespace, `;` and `%`. -/
private def IsWord (w : List Char) : Prop :=
  w = [';'] ∨ (w ≠ [] ∧ w.all (fun c => !c.isWhitespace && c != ';' && c != '%') = true)

private instance (w : List Char) : Decidable (IsWord w) := by unfold IsWord; infer_instance

private theorem isWord_of {w : List Char} (hne : w ≠ [])
    (h : ∀ c ∈ w, c.isWhitespace = false ∧ c ≠ ';' ∧ c ≠ '%') : IsWord w :=
  .inr ⟨hne, List.all_eq_true.2 fun c hc => by simp [(h c hc).1, (h c hc).2.1, (h c hc).2.2]⟩

/-- The characters of a word are not newlines or `%`. -/
private theorem ne_of_mem_isWord {w : List Char} (hw : IsWord w) {c : Char} (hc : c ∈ w) :
    c ≠ '\n' ∧ c ≠ '%' := by
  rcases hw with rfl | ⟨-, hw⟩
  · simp only [List.mem_singleton] at hc
    subst hc
    decide
  · have := List.all_eq_true.1 hw c hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    refine ⟨?_, this.2⟩
    rintro rfl
    exact absurd this.1.1 (by decide)

/-- A run of characters other than whitespace and `;` joins the token in progress. -/
private theorem lexLine_append {w rest cur : List Char}
    (hw : ∀ c ∈ w, c.isWhitespace = false ∧ c ≠ ';') :
    lexLine (w ++ rest) cur = lexLine rest (w.reverse ++ cur) := by
  induction w generalizing cur with
  | nil => rfl
  | cons c w ih =>
    rw [List.cons_append, lexLine]
    simp only [(hw c List.mem_cons_self).1, (hw c List.mem_cons_self).2, Bool.false_eq_true,
      ↓reduceIte, beq_iff_eq, ih fun d hd => hw d (List.mem_cons_of_mem _ hd)]
    simp

/-- **Lexing words each followed by a space.** -/
private theorem lexLine_words {ws : List (List Char)} (rest : List Char)
    (hw : ∀ w ∈ ws, IsWord w) :
    lexLine (ws.flatMap (· ++ [' ']) ++ rest) [] = ws.map String.ofList ++ lexLine rest [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have ih := ih fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc, List.map_cons, List.cons_append]
    rcases hw w List.mem_cons_self with rfl | ⟨hne, hall⟩
    · simp only [List.cons_append, List.nil_append, lexLine]
      simp only [show (';' : Char).isWhitespace = false by decide, Bool.false_eq_true,
        ↓reduceIte, show (';' == ';') = true by decide, show (' ' : Char).isWhitespace = true by
        decide, flushToken, List.isEmpty_nil, List.nil_append, ih]
    · have hc : ∀ c ∈ w, c.isWhitespace = false ∧ c ≠ ';' := fun c hc => by
        have := List.all_eq_true.1 hall c hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
        exact ⟨this.1.1, this.1.2⟩
      rw [lexLine_append hc]
      simp only [List.nil_append, List.append_nil]
      rw [lexLine]
      simp only [show (' ' : Char).isWhitespace = true by decide, ↓reduceIte, ih, flushToken]
      simp [hne]

/-- The tokens of a printed line. -/
private theorem tokens_render {ws : List (List Char)} (hw : ∀ w ∈ ws, IsWord w) :
    tokens (String.ofList (ws.flatMap (· ++ [' ']))) = ws.map String.ofList := by
  have hc : ∀ c ∈ ws.flatMap (· ++ [' ']), c ≠ '\n' ∧ c ≠ '%' := by
    intro c hc
    obtain ⟨w, hw', hc⟩ := List.mem_flatMap.1 hc
    rcases List.mem_append.1 hc with hc | hc
    · exact ne_of_mem_isWord (hw w hw') hc
    · rw [List.mem_singleton.1 hc]
      decide
  have hsplit : splitChars (· == '\n') (ws.flatMap (· ++ [' '])) =
      [ws.flatMap (· ++ [' '])] := by
    generalize ws.flatMap (· ++ [' ']) = l at hc
    induction l with
    | nil => rfl
    | cons x l ih =>
      rw [splitChars, ih fun c hc' => hc c (List.mem_cons_of_mem _ hc')]
      simp [(hc x List.mem_cons_self).1]
  have htw : (ws.flatMap (· ++ [' '])).takeWhile (· != '%') = ws.flatMap (· ++ [' ']) := by
    simpa using List.takeWhile_append_of_pos (l₂ := []) (p := (· != '%'))
      fun c hc' => by simpa using (hc c hc').2
  rw [tokens_eq_spec, lineTokens, String.toList_ofList, hsplit, List.flatMap_singleton, htw]
  simpa [lexLine, flushToken] using lexLine_words [] hw

/-- **The tokens of the lines of a printed text**, with an empty last line. -/
private theorem lines_render {L : List (List (List Char))} (hL : ∀ l ∈ L, ∀ w ∈ l, IsWord w) :
    (lines (String.ofList (L.flatMap renderLine))).map tokens =
      L.map (·.map String.ofList) ++ [[]] := by
  rw [lines_eq_spec, String.toList_ofList]
  induction L with
  | nil => rfl
  | cons l L ih =>
    have hc : ∀ c ∈ l.flatMap (· ++ [' ']), (c == '\n') = false := by
      intro c hc
      obtain ⟨w, hw', hc⟩ := List.mem_flatMap.1 hc
      rcases List.mem_append.1 hc with hc | hc
      · simpa using (ne_of_mem_isWord (hL l List.mem_cons_self w hw') hc).1
      · rw [List.mem_singleton.1 hc]
        decide
    rw [List.flatMap_cons, renderLine, List.append_assoc, List.singleton_append,
      splitChars_append _ hc (by decide), List.map_cons, List.map_cons,
      tokens_render (hL l List.mem_cons_self), ih fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')]
    rfl

/-! #### Numbers and names -/

private theorem nat?_toDecimal (n : ℕ) : nat? (String.ofList (Nat.toDecimal n)) = some n := by
  rw [nat?, String.toList_ofList, Nat.ofDecimal?_toDecimal]

private theorem startsWithChar_ofList (c d : Char) (ds : List Char) :
    startsWithChar c (String.ofList (d :: ds)) = (d == c) := by
  rw [startsWithChar, String.toList_ofList]
  simp

/-- A printed word differs from a keyword with another first character. -/
private theorem ofList_ne {d : Char} {ds : List Char} {s : String} (h : s.toList.head? ≠ some d) :
    String.ofList (d :: ds) ≠ s := by
  rintro rfl
  exact h (by rw [String.toList_ofList]; rfl)

private theorem dropChar?_toDecimal {c : Char} (hc : c.isDigit = false) (n : ℕ) :
    dropChar? c (String.ofList (Nat.toDecimal n)) = none := by
  obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons n
  rw [h, dropChar?_ofList]
  simp [Dimacs.ne_of_isDigit hd hc]

private theorem int?_toDecimal (n : ℕ) : int? (String.ofList (Nat.toDecimal n)) = some (n : ℤ) := by
  rw [int?, dropChar?_toDecimal (by decide), dropChar?_toDecimal (by decide), nat?_toDecimal]
  rfl

private theorem int?_intToDecimal (a : ℤ) : int? (String.ofList (Int.toDecimal a)) = some a := by
  unfold Int.toDecimal
  split
  · rw [int?, dropChar?_ofList, dropChar?_ofList]
    simp only [show ('-' == '+') = false by decide, Bool.false_eq_true, ↓reduceIte,
      show ('-' == '-') = true by decide, nat?_toDecimal]
    rename_i h
    change some (-((a.natAbs : ℕ) : ℤ)) = some a
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt h), neg_neg]
  · rename_i h
    rw [int?_toDecimal, Int.natAbs_of_nonneg (not_lt.1 h)]

private theorem isWord_toDecimal (n : ℕ) : IsWord (Nat.toDecimal n) :=
  isWord_of (Nat.toDecimal_ne_nil n) fun c hc => by
    have hd := Nat.isDigit_of_mem_toDecimal hc
    exact ⟨Dimacs.isWhitespace_eq_false_of_isDigit hd, Dimacs.ne_of_isDigit hd (by decide),
      Dimacs.ne_of_isDigit hd (by decide)⟩

private theorem isWord_cons {c : Char} {ds : List Char} (hds : IsWord ds)
    (hds' : ds ≠ [';']) (hc : c.isWhitespace = false ∧ c ≠ ';' ∧ c ≠ '%') : IsWord (c :: ds) := by
  rcases hds with h | ⟨-, h⟩
  · exact absurd h hds'
  · exact .inr ⟨by simp, by simp [h, hc.1, hc.2.1, hc.2.2]⟩

private theorem toDecimal_ne_semi (n : ℕ) : Nat.toDecimal n ≠ [';'] := by
  obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons n
  rw [h]
  intro h'
  exact Dimacs.ne_of_isDigit hd (by decide) (List.cons.inj h').1

private theorem isWord_intToDecimal (a : ℤ) : IsWord (Int.toDecimal a) := by
  unfold Int.toDecimal
  split
  · exact isWord_cons (isWord_toDecimal _) (toDecimal_ne_semi _) (by decide)
  · exact isWord_toDecimal _

/-- The variable `v` is printed with an OPB name, which the names `M` read as `π v`. -/
private def Reads (M N : Names) (π : ℕ → ℕ) (v : ℕ) : Prop :=
  M.var? (N.name v) = some (π v) ∧ isOPBName (N.name v) = true

/-- No character of a name is whitespace, `;`, `%`, `:` or `~`. -/
private theorem nameChar_ok {c : Char}
    (h : isNameChar c = true ∨ (c.isAlpha || c == '_') = true) :
    c.isWhitespace = false ∧ c ≠ ';' ∧ c ≠ '%' ∧ c ≠ ':' ∧ c ≠ '~' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases hw : c.isWhitespace
    · rfl
    · exfalso
      simp only [Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq] at hw
      rcases hw with ((rfl | rfl) | rfl) | rfl <;> revert h <;> decide
  all_goals rintro rfl; revert h; decide

/-- An OPB name has at least two characters, none of them whitespace, `;`, `%`, `:` or `~`. -/
private theorem name_word {w : List Char} (h : isOPBName (String.ofList w) = true) :
    ∃ c d cs, w = c :: d :: cs ∧
      ∀ x ∈ w, x.isWhitespace = false ∧ x ≠ ';' ∧ x ≠ '%' ∧ x ≠ ':' ∧ x ≠ '~' := by
  rw [isOPBName, String.toList_ofList] at h
  match w, h with
  | c :: d :: cs, h =>
    refine ⟨c, d, cs, rfl, fun x hx => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact nameChar_ok (.inr h.1)
    · exact nameChar_ok (.inl (h.2 x hx))

private theorem isWord_name {w : List Char} (h : isOPBName (String.ofList w) = true) :
    IsWord w := by
  obtain ⟨c, d, cs, rfl, hw⟩ := name_word h
  exact isWord_of (by simp) fun x hx => ⟨(hw x hx).1, (hw x hx).2.1, (hw x hx).2.2.1⟩

private theorem name_ne {w : List Char} (h : isOPBName (String.ofList w) = true) :
    String.ofList w ≠ ";" ∧ String.ofList w ≠ ":" := by
  obtain ⟨c, d, cs, rfl, hw⟩ := name_word h
  have hc := hw c List.mem_cons_self
  exact ⟨ofList_ne (by simpa [show (";" : String).toList = [';'] by decide] using hc.2.1.symm),
    ofList_ne (by simpa [show (":" : String).toList = [':'] by decide] using hc.2.2.2.1.symm)⟩

private theorem dropChar?_name {w : List Char} (h : isOPBName (String.ofList w) = true) :
    dropChar? '~' (String.ofList w) = none := by
  obtain ⟨c, d, cs, rfl, hw⟩ := name_word h
  rw [dropChar?_ofList]
  simp [(hw c List.mem_cons_self).2.2.2.2]

private theorem bareName_litChars {N : Names} {v : ℕ} (h : isOPBName (N.name v) = true)
    (b : Bool) :
    bareName (String.ofList (litChars N (v, b))) = N.name v := by
  cases b
  · rw [litChars, bareName, dropChar?_ofList]
    rfl
  · simp only [litChars, bareName]
    rw [dropChar?_name h]
    rfl

private theorem opbLit?_litChars {M N : Names} {π : ℕ → ℕ} {v : ℕ} (h : Reads M N π v)
    (b : Bool) : M.opbLit? (String.ofList (litChars N (v, b))) = some (π v, b) := by
  rw [Names.opbLit?, bareName_litChars h.2, ite_eq_left h.2]
  cases b
  · rw [litChars, Names.lit?, dropChar?_ofList]
    simp only [beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff]
    exact ⟨_, h.1, rfl⟩
  · rw [litChars, Names.lit?, dropChar?_name h.2]
    exact Option.map_eq_some_iff.2 ⟨_, h.1, rfl⟩

/-- A literal word is neither `;` nor `:`. -/
private theorem litChars_ne {N : Names} {v : ℕ} (h : isOPBName (N.name v) = true) (b : Bool) :
    String.ofList (litChars N (v, b)) ≠ ";" ∧ String.ofList (litChars N (v, b)) ≠ ":" := by
  cases b
  · exact ⟨ofList_ne (by decide), ofList_ne (by decide)⟩
  · exact name_ne h

private theorem isWord_litChars {N : Names} {v : ℕ} (h : isOPBName (N.name v) = true) (b : Bool) :
    IsWord (litChars N (v, b)) := by
  cases b
  · obtain ⟨c, d, cs, hw, -⟩ := name_word h
    exact isWord_cons (isWord_name h) (by rw [hw]; simp) (by decide)
  · exact isWord_name h

/-- A word starting with a digit or `-` is none of the keywords the parser compares it with. -/
private theorem ne_keyword {d : Char} {ds : List Char} (hd : d = '-' ∨ d.isDigit = true)
    {s : String} (hs : s ∈ [">=", "<=", "=", ";", ":", "min:", "preserved:"]) :
    String.ofList (d :: ds) ≠ s := by
  apply ofList_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hd with rfl | hd <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | decide
      | (rintro h
         have := congrArg (fun o => o.map Char.isDigit) h
         simp only [Option.map_some, hd] at this
         revert this
         decide)

/-! #### Constraints and objectives -/

private theorem terms_stop (lit : String → Option (Literal ℕ)) {t : String}
    (rest : List String) (L : List (ℕ × ℤ)) (k : ℤ) (ht : t = ">=" ∨ t = ";") :
    terms lit (t :: rest) L k = some (L, k, t :: rest) := by
  rcases ht with rfl | rfl <;> rfl

/-- The parser reads a coefficient word `ct` of value `a` and a literal word `u`. -/
private theorem terms_step (lit : String → Option (Literal ℕ)) {ct : List Char}
    {a : ℤ} (hct : ∃ d ds, ct = d :: ds ∧ (d = '-' ∨ d.isDigit = true))
    (ha : int? (String.ofList ct) = some a) {u : String} {l : Literal ℕ}
    (hu : lit u = some l) (hne : u ≠ ";" ∧ u ≠ ":") (rest : List String)
    (L : List (ℕ × ℤ)) (k : ℤ) :
    terms lit (String.ofList ct :: u :: rest) L k =
      terms lit rest (insertCoeff l.1 (if l.2 then a else -a) L)
        (k + if l.2 then 0 else a) := by
  obtain ⟨d, ds, rfl, hd⟩ := hct
  have hk : ∀ s ∈ [">=", "<=", "=", ";", ":", "min:", "preserved:"],
      (String.ofList (d :: ds) == s) = false := fun s hs => by
    simpa using ne_keyword hd hs
  have hl1 : (u == ";") = false := by simpa using hne.1
  have hl2 : (u == ":") = false := by simpa using hne.2
  rw [terms]
  simp only [hk ">=" (by simp), hk "<=" (by simp), hk "=" (by simp), hk ";" (by simp),
    hk ":" (by simp), Bool.or_false, Bool.false_eq_true, ↓reduceIte, ha, hl1, hl2, hu]
  obtain ⟨v, _ | _⟩ := l <;> simp

/-- The parser reads the terms of a constraint, renamed. -/
private theorem terms_terms (M N : Names) (π : ℕ → ℕ) (ts : List (ℕ × Literal ℕ))
    (h : ∀ t ∈ ts, Reads M N π (termVar t)) (rest : List String)
    (L : List (ℕ × ℤ)) (k : ℤ) :
    terms M.opbLit? ((ts.flatMap (termWords N)).map String.ofList ++ rest) L k =
      terms M.opbLit? rest (linOf L (ts.map (Instance.renameTerm π)))
        (negOf k (ts.map (Instance.renameTerm π))) := by
  induction ts generalizing L k with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    have hv := h _ List.mem_cons_self
    rw [termVar_mk] at hv
    simp only [List.flatMap_cons, termWords, List.map_cons, List.cons_append, List.nil_append]
    obtain ⟨d, ds, hdd, hd⟩ := Nat.exists_toDecimal_eq_cons a
    rw [terms_step _ ⟨d, ds, hdd, .inr hd⟩ (int?_toDecimal a)
      (opbLit?_litChars hv b) (litChars_ne hv.2 b), ih fun t ht => h t (List.mem_cons_of_mem _ ht)]
    cases b <;> rfl

/-- The parser reads the weights of an objective, renamed. -/
private theorem terms_weights (M N : Names) (π : ℕ → ℕ) (es : List (ℕ × ℤ))
    (h : ∀ e ∈ es, Reads M N π e.1) (rest : List String) (L : List (ℕ × ℤ))
    (k : ℤ) :
    terms M.opbLit?
        ((es.flatMap fun e => [Int.toDecimal e.2, N.nameChars e.1]).map String.ofList ++ rest)
        L k =
      terms M.opbLit? rest
        ((es.map fun e => (π e.1, e.2)).foldl (fun L e => insertCoeff e.1 e.2 L) L) k := by
  induction es generalizing L k with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append]
    rw [show N.nameChars e.1 = litChars N (e.1, true) from rfl,
      terms_step _ (Int.exists_toDecimal_eq_cons e.2) (int?_intToDecimal e.2)
        (opbLit?_litChars he true) (litChars_ne he.2 true),
      ih fun e he => h e (List.mem_cons_of_mem _ he)]
    simp

private theorem constr_constrWords (M N : Names) (π : ℕ → ℕ) (c : PBConstr)
    (h : ∀ t ∈ c.terms, Reads M N π (termVar t)) :
    constr M.opbLit? ((constrWords N c).map String.ofList) =
      some ([rereadConstr (Instance.renameConstr π c)], [";"]) := by
  rw [constr, constrWords, List.map_append, terms_terms M N π _ h]
  simp only [List.map_cons, List.map_nil]
  rw [terms_stop _ _ _ _ (.inl (by decide))]
  simp only [show String.ofList ['>', '='] = ">=" by decide, int?_toDecimal,
    show String.ofList [';'] = ";" by decide]
  simp [rereadConstr, Instance.renameConstr]

private theorem objective_objWords (M N : Names) (π : ℕ → ℕ) (f : Objective)
    (h : ∀ e ∈ f.lin, Reads M N π e.1) :
    objective M ((objTermWords N f ++ [[';']]).map String.ofList) =
      some (rereadObj (Instance.renameObj π f)) := by
  rw [objective, objTerms]
  simp only [objTermWords, List.map_append, List.append_assoc]
  by_cases hc : f.const = 0
  · simp only [hc, ↓reduceIte, List.map_nil, List.nil_append, List.map_cons]
    rw [terms_weights M N π _ h, show String.ofList [';'] = ";" by decide,
      terms_stop _ _ _ _ (.inr rfl)]
    simp [rereadObj, Instance.renameObj, hc]
  · obtain ⟨d, ds, hd, hd'⟩ := Int.exists_toDecimal_eq_cons f.const
    have hk : ∀ s ∈ [">=", "<=", "=", ";", ":", "min:", "preserved:"],
        String.ofList (Int.toDecimal f.const) ≠ s := fun s hs => hd ▸ ne_keyword hd' hs
    simp only [hc, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [terms_weights M N π _ h, terms, show String.ofList [';'] = ";" by decide]
    simp [hk ">=" (by simp), hk "<=" (by simp), hk "=" (by simp), hk ";" (by simp),
      hk ":" (by simp), int?_intToDecimal, rereadObj, Instance.renameObj]

private theorem presVars_presWords (M N : Names) (π : ℕ → ℕ) (P : List ℕ)
    (h : ∀ v ∈ P, Reads M N π v) :
    presVars M ((P.map N.nameChars ++ [[';']]).map String.ofList) = some (P.map π) := by
  induction P with
  | nil => simp only [List.map_nil, List.nil_append, List.map_cons]; rfl
  | cons v P ih =>
    rw [List.map_cons, List.cons_append, List.map_cons, presVars,
      show String.ofList (N.nameChars v) = N.name v from rfl,
      ite_eq_left (h v List.mem_cons_self).2, (h v List.mem_cons_self).1]
    · rw [Option.bind_some, ih fun v hv => h v (List.mem_cons_of_mem _ hv)]
      rfl
    · simp

/-- The first token of a constraint line is not a keyword of the header lines and does not start
with `*`. -/
private theorem head_constrWords (N : Names) (c : PBConstr) :
    ∃ t ts, (constrWords N c).map String.ofList = t :: ts ∧ startsWithChar '*' t = false ∧
      t ≠ "min:" ∧ t ≠ "preserved:" := by
  match hterms : c.terms with
  | [] =>
    have e : (constrWords N c).map String.ofList =
        ">=" :: [Nat.toDecimal c.degree, [';']].map String.ofList := by
      rw [constrWords, hterms, List.flatMap_nil, List.nil_append, List.map_cons,
        show String.ofList ['>', '='] = ">=" by decide]
    exact ⟨_, _, e, by decide, by decide, by decide⟩
  | (a, l) :: rest =>
    obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons a
    have e : (constrWords N c).map String.ofList = String.ofList (d :: ds) ::
        (litChars N l :: (rest.flatMap (termWords N) ++
          [['>', '='], Nat.toDecimal c.degree, [';']])).map String.ofList := by
      rw [constrWords, hterms, List.flatMap_cons, termWords, h]
      rfl
    refine ⟨_, _, e, ?_, ne_keyword (.inr hd) (by simp), ne_keyword (.inr hd) (by simp)⟩
    rw [startsWithChar_ofList]
    simpa using Dimacs.ne_of_isDigit hd (by decide)

private theorem opbLines_constrs (M N : Names) (π : ℕ → ℕ) (cs : List PBConstr)
    (h : ∀ c ∈ cs, ∀ t ∈ c.terms, Reads M N π (termVar t)) :
    opbLines M (cs.map fun c => (constrWords N c).map String.ofList) =
      some (cs.map fun c => rereadConstr (Instance.renameConstr π c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := constr_constrWords M N π c (h c List.mem_cons_self)
    obtain ⟨t, ts, hts, ht, -⟩ := head_constrWords N c
    rw [List.map_cons, hts, opbLines]
    rw [hts] at hc
    simp [ht, hc, ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

/-! #### Instances -/

private theorem mem_varList_constr {I : Instance} {c : PBConstr} (hc : c ∈ I.constraints)
    {t : ℕ × Literal ℕ} (ht : t ∈ c.terms) : termVar t ∈ I.varList :=
  Instance.vars_subset_allVars I (.inl ⟨c, hc, t, ht, rfl⟩)

private theorem mem_varList_obj {I : Instance} {f : Objective} (hf : I.objective = some f)
    {e : ℕ × ℤ} (he : e ∈ f.lin) : e.1 ∈ I.varList :=
  Instance.vars_subset_allVars I (.inr ⟨f, hf, e, he, rfl⟩)

private theorem mem_varList_pres {I : Instance} {P : List ℕ} (hP : I.preserved = some P)
    {v : ℕ} (hv : v ∈ P) : v ∈ I.varList :=
  Instance.mem_allVars_of_preserved hP hv

private theorem isWord_lines (I : Instance) (N : Names)
    (hN : ∀ v ∈ I.varList, isOPBName (N.name v) = true) :
    ∀ l ∈ headerWords I :: bodyLines N I, ∀ w ∈ l, IsWord w := by
  have hsemi : IsWord [';'] := .inl rfl
  have hconstr : ∀ c ∈ I.constraints, ∀ w ∈ constrWords N c, IsWord w := by
    intro c hc w hw
    simp only [constrWords, List.mem_append, List.mem_flatMap, termWords, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with ⟨t, ht, rfl | rfl⟩ | rfl | rfl | rfl
    · exact isWord_toDecimal _
    · obtain ⟨a, v, b⟩ := t
      exact isWord_litChars (hN v (mem_varList_constr hc ht)) b
    · decide
    · exact isWord_toDecimal _
    · exact hsemi
  intro l hl w hw
  simp only [bodyLines, List.mem_cons, List.mem_append, Option.mem_toList,
    Option.map_eq_some_iff, List.mem_map] at hl
  rcases hl with rfl | (⟨f, hf, rfl⟩ | ⟨P, hP, rfl⟩) | ⟨c, hc, rfl⟩
  · simp only [headerWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact isWord_toDecimal _
    · decide
    · exact isWord_toDecimal _
  · simp only [objWords, objTermWords, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | ⟨e, he, rfl | rfl⟩ | hw) | rfl
    · decide
    · exact isWord_intToDecimal _
    · exact isWord_name (hN _ (mem_varList_obj hf he))
    · split at hw
      · simp at hw
      · rw [List.mem_singleton.1 hw]
        exact isWord_intToDecimal _
    · exact hsemi
  · simp only [presWords, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false] at hw
    rcases hw with (rfl | ⟨v, hv, rfl⟩) | rfl
    · decide
    · exact isWord_name (hN _ (mem_varList_pres hP hv))
    · exact hsemi
  · exact hconstr c hc w hw

/-- The token lines of the constraints. -/
private def constrLines (N : Names) (I : Instance) : List (List String) :=
  I.constraints.map fun c => (constrWords N c).map String.ofList

private theorem head_constrLines {N : Names} {I : Instance} {l : List String}
    (hl : l ∈ constrLines N I) :
    ∃ t ts, l = t :: ts ∧ startsWithChar '*' t = false ∧ t ≠ "min:" ∧ t ≠ "preserved:" := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
  exact head_constrWords N c

/-- The token lines of a printed instance, after dropping the comments and empty lines. -/
private theorem filter_lines (I : Instance) (N : Names)
    (hN : ∀ v ∈ I.varList, isOPBName (N.name v) = true) (p : List String → Bool)
    (hnil : p [] = false)
    (hstar : ∀ t ts, startsWithChar '*' t = true → p (t :: ts) = false)
    (hpos : ∀ t ts, startsWithChar '*' t = false → p (t :: ts) = true) :
    ((lines (printOPB I N)).map tokens).filter p =
      (I.objective.map fun f => "min:" :: (objTermWords N f ++ [[';']]).map String.ofList).toList ++
        (I.preserved.map fun P => "preserved:" :: (P.map N.nameChars ++ [[';']]).map
          String.ofList).toList ++ constrLines N I := by
  rw [printOPB, lines_render (isWord_lines I N hN), List.map_cons, List.cons_append,
    List.filter_cons, headerWords, List.map_cons, hstar _ _ (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte, bodyLines, List.map_append, List.filter_append]
  have hc : (constrLines N I).filter p = constrLines N I := by
    refine List.filter_eq_self.2 fun l hl => ?_
    obtain ⟨t, ts, rfl, ht, -⟩ := head_constrLines hl
    exact hpos t ts ht
  have hmin : String.ofList ['m', 'i', 'n', ':'] = "min:" := by decide
  have hpres : String.ofList ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 'd', ':'] = "preserved:" := by
    decide
  rw [show (I.constraints.map (constrWords N)).map (·.map String.ofList) = constrLines N I by
    simp [constrLines, Function.comp_def]]
  rw [hc]
  cases I.objective <;> cases I.preserved <;>
    simp [objWords, presWords, hmin, hpres, hnil, hpos _ _ (show startsWithChar '*' "min:" = false
      by decide), hpos _ _ (show startsWithChar '*' "preserved:" = false by decide)]

/-- **The token lines of a printed instance**, without the comments and empty lines. -/
private theorem opbTokenLines_printOPB (I : Instance) (N : Names)
    (hN : ∀ v ∈ I.varList, isOPBName (N.name v) = true) :
    opbTokenLines (printOPB I N) =
      (I.objective.map fun f => "min:" :: (objTermWords N f ++ [[';']]).map String.ofList).toList ++
        (I.preserved.map fun P => "preserved:" :: (P.map N.nameChars ++ [[';']]).map
          String.ofList).toList ++ constrLines N I :=
  filter_lines I N hN _ rfl (fun t ts h => by simp [h]) (fun t ts h => by simp [h])

/-- No constraint line starts with `min:` or `preserved:`. -/
private theorem constrLines_ne (N : Names) (I : Instance) (ts : List String)
    (ls : List (List String)) :
    constrLines N I ≠ ("min:" :: ts) :: ls ∧ constrLines N I ≠ ("preserved:" :: ts) :: ls := by
  constructor <;> intro h <;>
    obtain ⟨t, ts', ht, -, hmin, hpres⟩ := head_constrLines (h ▸ List.mem_cons_self)
  · exact hmin (List.cons.inj ht).1.symm
  · exact hpres (List.cons.inj ht).1.symm

/-- **The names `M` read a printed instance**, renamed by `π` and normalized, when they read the
name of each variable `v` as `π v`. -/
private theorem parseOPBWith_printOPB {M N : Names} {π : ℕ → ℕ} {I : Instance}
    (h : ∀ v ∈ I.varList, Reads M N π v) :
    parseOPBWith M (printOPB I N) = some (reread (I.rename π)) := by
  have hc : opbLines M (constrLines N I) =
      some (I.constraints.map fun c => rereadConstr (Instance.renameConstr π c)) :=
    opbLines_constrs M N π I.constraints fun c hc t ht => h _ (mem_varList_constr hc ht)
  have hne := constrLines_ne N I
  have hobj : ∀ f, I.objective = some f → objective M ((objTermWords N f).map String.ofList ++
      [";"]) = some (rereadObj (Instance.renameObj π f)) := fun f hf => by
    simpa using objective_objWords M N π f fun e he => h _ (mem_varList_obj hf he)
  have hpres : ∀ P, I.preserved = some P →
      presVars M (P.map (String.ofList ∘ N.nameChars) ++ [";"]) = some (P.map π) :=
    fun P hP => by simpa using presVars_presWords M N π P fun v hv => h _ (mem_varList_pres hP hv)
  unfold parseOPBWith
  rw [opbTokenLines_printOPB I N fun v hv => (h v hv).2]
  obtain ⟨cs, obj, pres⟩ := I
  cases obj <;> cases pres <;>
    simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
      List.nil_append, List.cons_append] at hobj hpres ⊢ <;>
    (try split) <;> simp_all [reread, Instance.rename]

/-! #### The normal form and the semantics -/

private theorem foldl_insertCoeff_of_nodup {es L : List (ℕ × ℤ)}
    (h : (L.map Prod.fst ++ es.map Prod.fst).Nodup) :
    es.foldl (fun L e => insertCoeff e.1 e.2 L) L = L ++ es := by
  induction es generalizing L with
  | nil => simp
  | cons e es ih =>
    have he : e.1 ∉ L.map Prod.fst := fun he =>
      (List.nodup_append.1 h).2.2 _ he _ List.mem_cons_self rfl
    rw [List.foldl_cons, insertCoeff_of_not_mem he, ih (by simpa using h)]
    simp

private theorem linOf_eq_map {ts : List (ℕ × Literal ℕ)} (h : (ts.map termVar).Nodup) :
    linOf [] ts = ts.map fun t => (termVar t, termCoeff t) := by
  have := foldl_insertCoeff_of_nodup (L := []) (es := ts.map fun t => (termVar t, termCoeff t))
    (by simpa [Function.comp_def] using h)
  rw [linOf, ← List.nil_append (ts.map _), ← this, List.foldl_map]

private theorem negOf_eq (k : ℤ) (ts : List (ℕ × Literal ℕ)) : negOf k ts = k + negSum ts := by
  induction ts generalizing k with
  | nil => simp [negOf, negSum]
  | cons t ts ih =>
    rw [negOf, List.foldl_cons, ← negOf, ih]
    simp only [negSum, List.map_cons, List.sum_cons, Nat.cast_add]
    split
    · simp only [Nat.cast_zero, Int.add_zero, Int.zero_add]
    · omega

/-- **On the normal form, a constraint is read back as printed.** -/
theorem rereadConstr_eq {c : PBConstr} (hnd : (c.terms.map termVar).Nodup)
    (hpos : ∀ t ∈ c.terms, 0 < t.1) : rereadConstr c = c := by
  obtain ⟨ts, d⟩ := c
  simp only at hnd hpos
  rw [rereadConstr, linOf_eq_map hnd, negOf_eq, fromLinear]
  have hterms : (ts.map fun t => (termVar t, termCoeff t)).filterMap entryTerm = ts := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      obtain ⟨a, v, b⟩ := t
      have ha := hpos _ List.mem_cons_self
      rw [List.map_cons, List.filterMap_cons,
        ih (List.nodup_cons.1 hnd).2 fun t ht => hpos t (List.mem_cons_of_mem _ ht)]
      have ha' : ¬ ((a : ℤ) < 0) := by omega
      cases b <;> simp [entryTerm, termCoeff, ha, ha']
  have hmass : negMass (ts.map fun t => (termVar t, termCoeff t)) = negSum ts := by
    clear hnd hterms
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      obtain ⟨a, v, b⟩ := t
      simp only [negMass, negSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih fun t ht => hpos t (List.mem_cons_of_mem _ ht)]
      cases b <;> simp [termCoeff]
  rw [hterms, hmass]
  simp

/-- **On the normal form, an objective is read back as printed.** -/
theorem rereadObj_eq {f : Objective} (h : (f.lin.map Prod.fst).Nodup) : rereadObj f = f := by
  rw [rereadObj, foldl_insertCoeff_of_nodup (by simpa using h), List.nil_append]

/-- **On the normal form, an instance is read back as printed.** -/
theorem reread_eq {I : Instance} (h : Normal I) : reread I = I := by
  obtain ⟨cs, obj, pres⟩ := I
  have hcs : cs.map rereadConstr = cs := by
    have := List.map_congr_left (l := cs) (f := rereadConstr) (g := id) fun c hc =>
      rereadConstr_eq (h.constr_nodup c hc) (h.constr_pos c hc)
    simpa using this
  cases obj with
  | none => simp [reread, hcs]
  | some f => simp [reread, hcs, rereadObj_eq (h.obj_nodup f rfl)]

private theorem linVal_foldl_insertCoeff (σ : ℕ → Bool) (es L : List (ℕ × ℤ)) :
    linVal σ (es.foldl (fun L e => insertCoeff e.1 e.2 L) L) = linVal σ L + linVal σ es := by
  induction es generalizing L with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, linVal_insertCoeff, linVal_cons]
    ac_rfl

/-- **The read-back objective has the same values.** -/
theorem eval_rereadObj (f : Objective) (σ : ℕ → Bool) : (rereadObj f).eval σ = f.eval σ := by
  simp [rereadObj, Objective.eval, linVal_foldl_insertCoeff]

/-- The value `∑ cᵥ xᵥ` of the signed coefficients of terms. -/
private def signedVal (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) : ℤ :=
  (ts.map fun t => termCoeff t * ((σ (termVar t)).toNat : ℤ)).sum

private theorem linVal_linOf (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) (L : List (ℕ × ℤ)) :
    linVal σ (linOf L ts) = linVal σ L + signedVal σ ts := by
  induction ts generalizing L with
  | nil => simp [linOf, signedVal]
  | cons t ts ih =>
    rw [linOf, List.foldl_cons, ← linOf, ih, linVal_insertCoeff]
    simp only [signedVal, List.map_cons, List.sum_cons]
    ac_rfl

private theorem linVal_toLinear (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    linVal σ (toLinear ts) = signedVal σ ts := by
  induction ts with
  | nil => simp [toLinear, signedVal]
  | cons t ts ih =>
    rw [show toLinear (t :: ts) = insertCoeff (termVar t) (termCoeff t) (toLinear ts) from rfl,
      linVal_insertCoeff, ih]
    simp [signedVal]

/-- **The read-back constraint has the same solutions.** -/
theorem holds_rereadConstr_iff (c : PBConstr) (σ : ℕ → Bool) :
    (rereadConstr c).Holds σ ↔ c.Holds σ := by
  rw [rereadConstr, holds_fromLinear_iff, linVal_linOf, negOf_eq, Holds,
    ← Nat.cast_le (α := ℤ), lhs_eq_linVal, linVal_toLinear]
  simp only [linVal_nil, zero_add]
  omega

/-- The read-back constraints have the same solutions. -/
theorem forall_holds_reread_iff (I : Instance) (σ : ℕ → Bool) :
    (∀ c ∈ (reread I).constraints, c.Holds σ) ↔ ∀ c ∈ I.constraints, c.Holds σ := by
  simp [reread, holds_rereadConstr_iff]

/-! #### DIMACS -/

private theorem dimacsClauses_lit {V : ℕ} {l : Literal ℕ} (hl : l.1 < V) (ts : List String)
    (cur : List ℤ) :
    dimacsClauses V (String.ofList (Dimacs.litChars l) :: ts) cur =
      dimacsClauses V ts (l.toDIMACS :: cur) := by
  have hne : l.toDIMACS ≠ 0 := by unfold Literal.toDIMACS; split <;> omega
  have habs : l.toDIMACS.natAbs ≤ V := by rw [Literal.natAbs_toDIMACS]; omega
  rw [dimacsClauses, Dimacs.litChars, int?_intToDecimal]
  split
  · rename_i h; simp at h
  · rename_i h; exact absurd (Option.some.inj h) hne
  · rename_i i h; cases Option.some.inj h; simp only [habs, ↓reduceIte]

private theorem dimacsClauses_clause {V : ℕ} {cl : Clause ℕ} (hcl : ∀ l ∈ cl, l.1 < V)
    (ts : List String) (cur : List ℤ) :
    dimacsClauses V ((cl.map Dimacs.litChars).map String.ofList ++ "0" :: ts) cur =
      (dimacsClauses V ts []).map
        (Clause.ofDIMACS (cur.reverse ++ cl.map Literal.toDIMACS) :: ·) := by
  induction cl generalizing cur with
  | nil =>
    rw [List.map_nil, List.map_nil, List.nil_append, dimacsClauses,
      show int? "0" = some 0 by decide]
    simp
  | cons l cl ih =>
    rw [List.map_cons, List.map_cons, List.cons_append,
      dimacsClauses_lit (hcl l List.mem_cons_self),
      ih fun l' hl' => hcl l' (List.mem_cons_of_mem _ hl')]
    simp

private theorem ofDIMACS_map_toDIMACS (cl : Clause ℕ) :
    Clause.ofDIMACS (cl.map Literal.toDIMACS) = cl := by
  simpa [Clause.toDIMACS] using Clause.ofDIMACS_toDIMACS cl

/-- The tokens of a line without newlines and `%` are those of `lexLine`. -/
private theorem tokens_ofList {cs : List Char} (h : ∀ c ∈ cs, c ≠ '\n' ∧ c ≠ '%') :
    tokens (String.ofList cs) = lexLine cs [] := by
  have hsplit : splitChars (· == '\n') cs = [cs] := by
    induction cs with
    | nil => rfl
    | cons x l ih =>
      rw [splitChars, ih fun c hc' => h c (List.mem_cons_of_mem _ hc')]
      simp [(h x List.mem_cons_self).1]
  have htw : cs.takeWhile (· != '%') = cs := by
    simpa using List.takeWhile_append_of_pos (l₂ := []) (p := (· != '%'))
      fun c hc' => by simpa using (h c hc').2
  rw [tokens_eq_spec, lineTokens, String.toList_ofList, hsplit, List.flatMap_singleton, htw]

/-- Lexing words followed by spaces and a last word. -/
private theorem lexLine_last {ws : List (List Char)} {w : List Char} (hws : ∀ u ∈ ws, IsWord u)
    (hw : w ≠ []) (hw' : ∀ c ∈ w, c.isWhitespace = false ∧ c ≠ ';') :
    lexLine (ws.flatMap (· ++ [' ']) ++ w) [] = (ws ++ [w]).map String.ofList := by
  rw [lexLine_words _ hws, ← List.append_nil w, lexLine_append hw', List.append_nil,
    List.append_nil, lexLine, flushToken]
  simp [hw]

private theorem ne_of_isWord {w : List Char} (hw : IsWord w) {c : Char} (hc : c ∈ w) :
    c ≠ '\n' ∧ c ≠ '%' := ne_of_mem_isWord hw hc

private theorem isWord_dimacsLit (l : Literal ℕ) : IsWord (Dimacs.litChars l) := by
  exact isWord_intToDecimal _

private theorem plain_toDecimal (n : ℕ) :
    ∀ c ∈ Nat.toDecimal n, c.isWhitespace = false ∧ c ≠ ';' := fun c hc => by
  have hd := Nat.isDigit_of_mem_toDecimal hc
  exact ⟨Dimacs.isWhitespace_eq_false_of_isDigit hd, Dimacs.ne_of_isDigit hd (by decide)⟩

/-- **The DIMACS parser of the text front end reads back a printed formula**, for every formula:
the text `φ.toDIMACS` parses to `φ`. -/
theorem parseDIMACS_toDIMACS (φ : CNF ℕ) : parseDIMACS φ.toDIMACS = some φ := by
  set V := φ.dimacsVars
  set hdr : List (List Char) := [['p'], ['c', 'n', 'f'], Nat.toDecimal V]
  have hhdr : ∀ u ∈ hdr, IsWord u := by
    simp only [hdr, List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl)
    · decide
    · decide
    · exact isWord_toDecimal _
  have hH : Dimacs.headerChars V φ.length =
      (hdr.flatMap (· ++ [' ']) ++ Nat.toDecimal φ.length) ++ '\n' :: [] := by
    simp [Dimacs.headerChars, hdr]
  have hHc : ∀ c ∈ hdr.flatMap (· ++ [' ']) ++ Nat.toDecimal φ.length, c ≠ '\n' ∧ c ≠ '%' := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨w, hw, hc⟩ := List.mem_flatMap.1 hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ne_of_isWord (hhdr w hw) hc
      · rw [List.mem_singleton.1 hc]; decide
    · exact ne_of_isWord (isWord_toDecimal _) hc
  -- The clause lines.
  set body := fun cl : Clause ℕ => (cl.map Dimacs.litChars).flatMap (· ++ [' ']) ++ ['0']
  have hbody : ∀ cl, ∀ c ∈ body cl, c ≠ '\n' ∧ c ≠ '%' := by
    intro cl c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨w, hw, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
      rcases List.mem_append.1 hc with hc | hc
      · exact ne_of_isWord (isWord_dimacsLit l) hc
      · rw [List.mem_singleton.1 hc]; decide
    · rw [List.mem_singleton.1 hc]; decide
  have hclause : ∀ cl : Clause ℕ, Dimacs.clauseChars cl = body cl ++ ['\n'] := fun cl => by
    simp [Dimacs.clauseChars, body, List.flatMap_map]
  have hsplit : ∀ ψ : CNF ℕ, splitChars (· == '\n') (ψ.flatMap Dimacs.clauseChars) =
      ψ.map body ++ [[]] := by
    intro ψ
    induction ψ with
    | nil => rfl
    | cons cl ψ ih =>
      rw [List.flatMap_cons, hclause, List.append_assoc, List.singleton_append,
        splitChars_append _ (fun c hc => by simpa using (hbody cl c hc).1) (by decide), ih]
      rfl
  have htok : ∀ cl : Clause ℕ, tokens (String.ofList (body cl)) =
      ((cl.map Dimacs.litChars).map String.ofList ++ ["0"]) := fun cl => by
    rw [tokens_ofList (hbody cl), lexLine_last (fun u hu => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hu; exact isWord_dimacsLit l) (by simp)
      (by simp only [List.mem_singleton, forall_eq]; decide)]
    simp only [List.map_append, List.map_cons, List.map_nil]
  have hhead : ∀ cl : Clause ℕ, ((cl.map Dimacs.litChars).map String.ofList ++ ["0"]).head? ≠
      some "c" := fun cl => by
    cases cl with
    | nil => simp only [List.map_nil, List.nil_append, List.head?_cons]; decide
    | cons l cl =>
      simp only [List.map_cons, List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
      rw [Dimacs.litChars]
      obtain ⟨d, ds, h, hd⟩ := Int.exists_toDecimal_eq_cons l.toDIMACS
      rw [h]
      apply ofList_ne
      rcases hd with rfl | hd
      · decide
      · intro h'
        have := congrArg (fun o => o.map Char.isDigit) h'
        simp only [Option.map_some, hd] at this
        revert this
        decide
  -- The clauses read.
  have hcls : ∀ ψ : CNF ℕ, (∀ v ∈ CNF.vars ψ, v < V) →
      dimacsClauses V (ψ.map fun cl => (cl.map Dimacs.litChars).map String.ofList ++ ["0"]).flatten
        [] = some ψ := by
    intro ψ hψ
    induction ψ with
    | nil => rfl
    | cons cl ψ ih =>
      have hcl : ∀ l ∈ cl, l.1 < V := fun l hl =>
        hψ l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨cl, List.mem_cons_self, hl⟩, rfl⟩)
      have hψ' : ∀ v ∈ CNF.vars ψ, v < V := fun v hv => hψ v (by
        simp only [CNF.vars, List.flatten_cons, List.map_append, List.mem_append] at hv ⊢
        exact .inr hv)
      rw [List.map_cons, List.flatten_cons, List.append_assoc, List.singleton_append,
        dimacsClauses_clause hcl, ih hψ']
      simp [ofDIMACS_map_toDIMACS]
  unfold parseDIMACS
  rw [CNF.toDIMACS, lines_eq_spec, String.toList_ofList, hH, List.append_assoc,
    List.singleton_append,
    splitChars_append _ (fun c hc => by simpa using (hHc c hc).1) (by decide), hsplit]
  simp only [List.map_cons, List.map_append, List.map_map, Function.comp_def, htok, List.map_nil]
  rw [tokens_ofList hHc, lexLine_last hhdr (Nat.toDecimal_ne_nil _) (plain_toDecimal _)]
  have hp : String.ofList ['p'] = "p" := by decide
  have hcnf : String.ofList ['c', 'n', 'f'] = "cnf" := by decide
  simp only [hdr, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hp, hcnf,
    List.filter_cons, List.head?_cons]
  have hfilt : ∀ ψ : CNF ℕ, List.filter (fun l => l.head? != some "c")
      (ψ.map fun x => x.map (fun x => String.ofList (Dimacs.litChars x)) ++ ["0"]) =
      ψ.map fun x => x.map (fun x => String.ofList (Dimacs.litChars x)) ++ ["0"] := fun ψ =>
    List.filter_eq_self.2 fun l hl => by
      obtain ⟨cl, -, rfl⟩ := List.mem_map.1 hl
      simpa [List.map_map, Function.comp_def] using hhead cl
  have hcls' : dimacsClauses V
      ((φ.map fun x => x.map (fun x => String.ofList (Dimacs.litChars x)) ++ ["0"]).flatten)
      [] = some φ := by
    simpa [List.map_map, Function.comp_def] using hcls φ fun v hv => CNF.lt_dimacsVars hv
  simp only [show (some "p" != some "c") = true by decide, ↓reduceIte, List.filter_append, hfilt,
    show tokens (String.ofList []) = [] from rfl, List.filter_cons, List.head?_nil,
    show ((none : Option String) != some "c") = true by decide, List.filter_nil, nat?_toDecimal,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, hcls',
    Option.bind_some]

/-! #### The round trips and the soundness theorems end to end -/

/-- **Names for printing an instance**: well formed, naming every variable of the instance
below `next`, and with an OPB name (`Cslib.Logic.PL.VeriPB.Text.isOPBName`) for each of them.
A name `$a` of an auxiliary variable is not one, since an instance has none; names the
instance does not use are not constrained. -/
structure Names.Covers (N : Names) (I : Instance) : Prop where
  /-- The names are well formed. -/
  wf : N.WF
  /-- Every variable of the instance is named. -/
  lt_next : ∀ v ∈ I.varList, v < N.next
  /-- Every variable of the instance has an OPB name. -/
  opb : ∀ v ∈ I.varList, isOPBName (N.name v) = true

instance (N : Names) (I : Instance) : Decidable (N.Covers I) :=
  decidable_of_iff
    (N.WF ∧ (∀ v ∈ I.varList, v < N.next) ∧ ∀ v ∈ I.varList, isOPBName (N.name v) = true)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

private theorem lt_foldr_max {l : List ℕ} {v : ℕ} (h : v ∈ l) :
    v < l.foldr (fun v m => max (v + 1) m) 0 := by
  induction l with
  | nil => cases h
  | cons u l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

/-- The standard names cover the instance. -/
theorem stdNames_covers (I : Instance) : (stdNames I).Covers I :=
  have hlt : ∀ v ∈ I.varList, v < (stdNames I).next := fun _ hv => by
    simp only [Names.next, stdNames, List.length_nil, Nat.add_zero]
    exact lt_foldr_max hv
  ⟨⟨List.nodup_nil, fun _ h => by simp [stdNames] at h, fun _ h => by simp [stdNames] at h⟩,
    hlt, fun v hv => Names.isOPBName_name (fun _ h => by simp [stdNames] at h) (hlt v hv)⟩

/-- **Every variable of a printed instance is named in its text.** -/
private theorem exists_token_name {I : Instance} {N : Names} (hN : N.Covers I) {v : ℕ}
    (hv : v ∈ I.varList) :
    ∃ t ∈ (opbTokenLines (printOPB I N)).flatten, bareName t = N.name v := by
  have hbare : bareName (N.name v) = N.name v := by
    rw [bareName, Names.name, dropChar?_name (hN.opb v hv)]
    rfl
  rw [opbTokenLines_printOPB I N hN.opb]
  simp only [List.flatten_append, List.mem_append, List.mem_flatten]
  simp only [Instance.varList, List.mem_append, List.mem_flatMap, List.mem_map] at hv
  rcases hv with (⟨c, hc, ⟨a, u, b⟩, ht, rfl⟩ | hv) | hv
  · refine ⟨_, .inr ⟨_, List.mem_map_of_mem hc, ?_⟩, bareName_litChars (hN.opb _
      (mem_varList_constr hc ht)) b⟩
    simp only [constrWords, termWords, List.map_append, List.mem_append, List.mem_map,
      List.mem_flatMap, List.mem_cons]
    exact .inl ⟨_, ⟨_, ht, .inr (.inl rfl)⟩, rfl⟩
  · cases hf : I.objective with
    | none => simp [hf] at hv
    | some f =>
      simp only [hf, Option.map_some, Option.getD_some, List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv
      refine ⟨N.name e.1, .inl (.inl ⟨_, List.mem_singleton_self _, ?_⟩),
        hbare⟩
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _
        (List.mem_append_left _ (List.mem_flatMap.2 ⟨e, he, by simp⟩))))
  · cases hP : I.preserved with
    | none => simp [hP] at hv
    | some P =>
      rw [hP, Option.getD_some] at hv
      refine ⟨N.name v, .inl (.inr ⟨_, List.mem_singleton_self _, ?_⟩), hbare⟩
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _
        (List.mem_map_of_mem hv)))

/-- **The parser reads back a printed instance, renumbered**: with names that cover the
instance (`Cslib.Logic.PL.VeriPB.Text.Names.Covers`), the text `printOPB I N` parses to
`reread (I.rename π)` for a map `π` that is injective on the variables of `I` and gives each
variable its name: the variable `v`, printed `N.name v`, is read as `π v`, named
`N.name v` in the names of the text (`Cslib.Logic.PL.VeriPB.Text.opbNames`). So the instance
read back is `I` with the same names, renumbered in their order of first appearance, and
normalized; `Cslib.Logic.PL.VeriPB.Instance.valuesVia_eq` transfers every conclusion about it
to `I`. -/
theorem exists_parseOPB_printOPB {I : Instance} {N : Names} (hN : N.Covers I) :
    ∃ π : ℕ → ℕ, Set.InjOn π I.allVars ∧
      (∀ v ∈ I.varList, (opbNames (printOPB I N)).var? (N.name v) = some (π v)) ∧
      (∀ v ∈ I.varList, (opbNames (printOPB I N)).name (π v) = N.name v) ∧
      parseOPB (printOPB I N) = some (reread (I.rename π)) := by
  set M := opbNames (printOPB I N)
  have hread : ∀ v ∈ I.varList, ∃ w, M.var? (N.name v) = some w := fun v hv => by
    obtain ⟨t, ht, hbt⟩ := exists_token_name hN hv
    obtain ⟨w, hw, -⟩ := opbNames_var? ht (hbt ▸ hN.opb v hv)
    exact ⟨w, hbt ▸ hw⟩
  refine ⟨fun v => (M.var? (N.name v)).getD 0, ?_, fun v hv => ?_, fun v hv => ?_, ?_⟩
  · intro v hv w hw hvw
    obtain ⟨a, ha⟩ := hread v hv
    obtain ⟨b, hb⟩ := hread w hw
    simp only [ha, hb, Option.getD_some] at hvw
    subst hvw
    exact Names.name_injective hN.wf ((Names.name_of_var? ha).symm.trans (Names.name_of_var? hb))
  · obtain ⟨a, ha⟩ := hread v hv
    simp [ha]
  · obtain ⟨a, ha⟩ := hread v hv
    simp only [ha, Option.getD_some]
    exact Names.name_of_var? ha
  · refine parseOPBWith_printOPB fun v hv => ⟨?_, hN.opb v hv⟩
    obtain ⟨a, ha⟩ := hread v hv
    exact (show M.var? (N.name v) = some ((M.var? (N.name v)).getD 0) by simp [ha])

/-- **The parser reads back exactly the printed instance, normalized**, when its names read
each variable as itself, as for names given in their order of first appearance in the text
(decidable). -/
theorem parseOPB_printOPB_of_var? {I : Instance} {N : Names} (hN : N.Covers I)
    (h : ∀ v ∈ I.varList, (opbNames (printOPB I N)).var? (N.name v) = some v) :
    parseOPB (printOPB I N) = some (reread I) := by
  have := parseOPBWith_printOPB (M := opbNames (printOPB I N)) (N := N) (π := id) (I := I)
    fun v hv => ⟨h v hv, hN.opb v hv⟩
  rwa [Instance.rename_id] at this

/-- **The parser reads back a printed instance**, normalized: for every instance `I`, the text
`printOPB I` parses, with the standard names `x(v + 1)`, to `reread I`, which has the same
solutions and objective values as `I`. -/
theorem parseOPB_printOPB (I : Instance) : parseOPB (printOPB I) = some (reread I) := by
  refine parseOPB_printOPB_of_var? (stdNames_covers I) fun v hv => ?_
  have hlt := (stdNames_covers I).lt_next v hv
  have hstd : (stdNames I).name v = String.ofList ('x' :: Nat.toDecimal (v + 1)) := by
    have hb : v < (stdNames I).base := by simpa [Names.next, stdNames] using hlt
    simp only [Names.name, Names.nameChars, hb, ↓reduceIte]
  obtain ⟨t, ht, hbt⟩ := exists_token_name (stdNames_covers I) hv
  obtain ⟨w, hw, hwv⟩ := opbNames_var? ht (hbt ▸ (stdNames_covers I).opb v hv)
  rw [hbt] at hw hwv
  rw [hw, hwv v (by rw [hstd, stdVar?_std])]

/-- **The parser reads back exactly what is printed** from an instance in its normal form
(`Cslib.Logic.PL.VeriPB.Text.Normal`), with the standard names: the variable `v` is printed
`x(v + 1)` and read back as `v`. -/
theorem parseOPB_printOPB_of_normal {I : Instance} (h : Normal I) :
    parseOPB (printOPB I) = some I := by
  rw [parseOPB_printOPB, reread_eq h]

/-! #### The semantics of the instance read back -/

private theorem values_reread (J : Instance) (P : List ℕ) :
    (reread J).values P = J.values P := by
  ext x
  simp only [Instance.mem_values]
  refine exists_congr fun σ => and_congr (forall_holds_reread_iff J σ) ?_
  cases h : J.objective <;> simp [reread, h, objValue, eval_rereadObj]

/-- The instance read back from a printed instance has its values. -/
private theorem values_read {I : Instance} {π : ℕ → ℕ} (hπ : Set.InjOn π I.allVars)
    {P : List ℕ} (hP : ∀ v ∈ P, v ∈ I.allVars) :
    (reread (I.rename π)).values (P.map π) = I.values P := by
  rw [values_reread, Instance.values_rename_eq (hπ.mono (Set.union_subset
    (Instance.vars_subset_allVars I) fun v hv => hP v hv))]

private theorem satisfiable_read {I : Instance} {π : ℕ → ℕ} (hπ : Set.InjOn π I.allVars) :
    (reread (I.rename π)).Satisfiable ↔ I.Satisfiable := by
  rw [Instance.satisfiable_iff, Instance.satisfiable_iff,
    ← values_read hπ (P := []) (by simp), List.map_nil]

/-- **Soundness of `UNSAT` end to end**: an accepted proof of `UNSAT` against the printed text
of an instance `I` built in Lean, with names that cover it, means that the constraints of `I`
have no 0/1 solution. -/
theorem not_satisfiable_of_checkOPB_printOPB {I : Instance} {N : Names} (hN : N.Covers I)
    {pbp : String} {out : Option String} {q : ℕ}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.unsat q)) :
    ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨J, hJ, hσ⟩ := not_satisfiable_of_checkOPB h
  obtain ⟨π, hπ, -, -, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  exact fun σ hs => absurd ((satisfiable_read hπ).2 ⟨σ, hs⟩) fun ⟨σ', h'⟩ => hσ σ' h'

/-- **Soundness of `SAT` end to end**: an accepted proof of `SAT` against the printed text of an
instance `I`, with names that cover it, means that the constraints of `I` have a 0/1 solution. -/
theorem exists_satisfies_of_checkOPB_printOPB {I : Instance} {N : Names} (hN : N.Covers I)
    {pbp : String} {out : Option String} {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.sat asg)) :
    ∃ σ : ℕ → Bool, ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨J, hJ, hσ⟩ := exists_satisfies_of_checkOPB h
  obtain ⟨π, hπ, -, -, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  exact (satisfiable_read hπ).1 hσ

/-- **Soundness of `SAT : ρ` end to end**: the stated assignment `ρ`, its literals translated to
names (`Cslib.Logic.PL.VeriPB.Text.proofNames`), solves the constraints of the instance `I`
whose printed text the proof is checked against: the variable `v` of `I` is true when `ρ` makes
the variable of its name `N.name v` true. -/
theorem holds_of_checkOPB_printOPB_sat {I : Instance} {N : Names} (hN : N.Covers I)
    {pbp : String} {out : Option String} {ρ : List (Literal ℕ)}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.sat (some ρ))) :
    ∀ c ∈ I.constraints, c.Holds fun v =>
      (ρ.map fun l => ((proofNames (printOPB I N) pbp out).name l.1, l.2)).contains
        (N.name v, true) := by
  obtain ⟨J, hJ, hσ⟩ := holds_of_checkOPB_sat h
  obtain ⟨π, -, hvar, hname, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  set P := proofNames (printOPB I N) pbp out
  have hP : P.Extends (opbNames (printOPB I N)) := Names.extends_extend _ _
  intro c hc
  have hc' := (holds_renameConstr π c _).1 ((forall_holds_reread_iff _ _).1 hσ _
    (List.mem_map_of_mem hc))
  refine (holds_congr fun t ht => ?_).1 hc'
  have hv := mem_varList_constr hc ht
  have hlt := Names.lt_next_of_var? (hvar _ hv)
  simp only [Function.comp_apply, assignOf]
  rw [← hname _ hv, ← hP.name_eq hlt]
  have hinj : Function.Injective fun l : Literal ℕ => (P.name l.1, l.2) := fun a b hab =>
    Prod.ext (Names.name_injective (proofNames_wf _ _ _) (Prod.mk.inj hab).1) (Prod.mk.inj hab).2
  have key : ∀ x : Literal ℕ, (x ∈ ρ) ↔ (P.name x.1, x.2) ∈ ρ.map fun l => (P.name l.1, l.2) :=
    fun x => (List.mem_map_of_injective hinj).symm
  exact Bool.eq_iff_iff.2 (List.contains_iff_mem.trans
    ((key (π (termVar t), true)).trans List.contains_iff_mem.symm))

/-- **Soundness of `BOUNDS` end to end**: an accepted proof of `BOUNDS lb : q ub` against the
printed text of an instance `I`, with names that cover it, means that `I` has an objective `f`,
every 0/1 solution `σ` of its constraints has a finite `lb` with `lb ≤ f σ`, and for a finite
`ub` some solution has objective at most `ub`. -/
theorem bounds_of_checkOPB_printOPB {I : Instance} {N : Names} (hN : N.Covers I) {pbp : String}
    {out : Option String} {lb ub : Option ℤ} {q : ℕ} {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.bounds lb q ub asg)) :
    ∃ f, I.objective = some f ∧
      (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → ∃ l, lb = some l ∧ l ≤ f.eval σ) ∧
      ∀ u, ub = some u → ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ u := by
  obtain ⟨J, f', hJ, hf', hlb, hub⟩ := bounds_of_checkOPB h
  obtain ⟨π, hπ, -, -, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hf'
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hg
  have hval := values_read hπ (P := []) (by simp)
  simp only [List.map_nil] at hval
  have hobj : objValue (reread (I.rename π)).objective = (rereadObj (renameObj π f)).eval := by
    funext σ
    simp only [reread, Instance.rename, hf, Option.map_some]
    rfl
  refine ⟨f, hf, fun σ hσ => ?_, fun u hu => ?_⟩
  · have hx : (f.eval σ, proj [] σ) ∈ (reread (I.rename π)).values [] :=
      hval ▸ Instance.mem_values.2 ⟨σ, hσ, by simp [objValue, hf]⟩
    obtain ⟨σ', hσ', hx'⟩ := Instance.mem_values.1 hx
    obtain ⟨l, hl, hle⟩ := hlb σ' hσ'
    exact ⟨l, hl, by rw [hobj] at hx'; rw [(Prod.mk.inj hx').1]; exact hle⟩
  · obtain ⟨σ, hσ, hle⟩ := hub u hu
    refine ⟨σ ∘ π, fun c hc => (holds_renameConstr π c σ).1 ((forall_holds_reread_iff _ σ).1 hσ _
      (List.mem_map_of_mem hc)), ?_⟩
    rwa [eval_rereadObj, eval_renameObj] at hle

/-- The read-back instance has the projections of `I`. -/
private theorem projections_read {I : Instance} {π : ℕ → ℕ} (hπ : Set.InjOn π I.allVars)
    {P : List ℕ} (hP : I.preserved = some P) :
    projections (reread (I.rename π)).constraints (P.map π) = projections I.constraints P := by
  rw [Instance.projections_eq, Instance.projections_eq,
    values_read hπ fun v hv => Instance.mem_allVars_of_preserved hP hv]

/-- **Soundness of a partial enumeration end to end**: an accepted proof of
`ENUMERATION_PARTIAL n` against the printed text of an instance `I`, with names that cover it,
means that `I` has a preserved set `P` and its solutions have at least `n` distinct projections
to `P`. -/
theorem le_encard_of_checkOPB_printOPB_enumPartial {I : Instance} {N : Names} (hN : N.Covers I)
    {pbp : String} {out : Option String} {n : ℕ}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.enumPartial n)) :
    ∃ P, I.preserved = some P ∧ (n : ℕ∞) ≤ (projections I.constraints P).encard := by
  obtain ⟨J, P', hJ, hP', hn⟩ := le_encard_of_checkOPB_enumPartial h
  obtain ⟨π, hπ, -, -, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hP'
  exact ⟨P, hP, projections_read hπ hP ▸ hn⟩

/-- **Soundness of a complete enumeration end to end**: an accepted proof of
`ENUMERATION_COMPLETE n : q` against the printed text of an instance `I`, with names that cover
it, means that `I` has a preserved set `P` and its solutions have exactly `n` distinct
projections to `P`. -/
theorem encard_eq_of_checkOPB_printOPB_enumComplete {I : Instance} {N : Names} (hN : N.Covers I)
    {pbp : String} {out : Option String} {n q : ℕ}
    (h : (checkOPBOutput (printOPB I N) pbp out).map (·.1) = some (.enumComplete n q)) :
    ∃ P, I.preserved = some P ∧ (projections I.constraints P).encard = n := by
  obtain ⟨J, P', hJ, hP', hn⟩ := encard_eq_of_checkOPB_enumComplete h
  obtain ⟨π, hπ, -, -, hp⟩ := exists_parseOPB_printOPB hN
  cases hp.symm.trans hJ
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hP'
  exact ⟨P, hP, projections_read hπ hP ▸ hn⟩

/-- **Soundness of `UNSAT` for DIMACS end to end**: an accepted proof of `UNSAT` against the
printed text `φ.toDIMACS` of a formula `φ` built in Lean means that `φ` is unsatisfiable. -/
theorem not_satisfiable_of_checkDIMACS_toDIMACS {φ : CNF ℕ} {pbp : String} {q : ℕ}
    (h : checkDIMACS φ.toDIMACS pbp = some (.unsat q)) : ¬ φ.Satisfiable := by
  obtain ⟨ψ, hψ, hns⟩ := not_satisfiable_of_checkDIMACS h
  rw [parseDIMACS_toDIMACS, Option.some.injEq] at hψ
  exact hψ ▸ hns

/-- **Soundness of `SAT` for DIMACS end to end**: an accepted proof of `SAT` against the printed
text `φ.toDIMACS` of a formula `φ` means that `φ` is satisfiable. -/
theorem satisfiable_of_checkDIMACS_toDIMACS {φ : CNF ℕ} {pbp : String}
    {asg : Option (List (Literal ℕ))} (h : checkDIMACS φ.toDIMACS pbp = some (.sat asg)) :
    φ.Satisfiable := by
  obtain ⟨ψ, hψ, hs⟩ := satisfiable_of_checkDIMACS h
  rw [parseDIMACS_toDIMACS, Option.some.injEq] at hψ
  exact hψ ▸ hs

end Cslib.Logic.PL.VeriPB.Text

end
