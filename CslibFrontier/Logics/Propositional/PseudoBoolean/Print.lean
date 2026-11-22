/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Dimacs
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
-- `import all`: the round-trip proofs unfold the private lexer and parsers of `Text` (`lines`,
-- `splitChars`, `lexLine`, `flushToken`, `nat?`, `dropChar?`, `startsWithChar`,
-- `terms`, `constr`, `opbLines`, `objTerms`, `objective`, `presVars`, `dimacsClauses`) and the
-- unexposed bodies of `parseOPB`, `parseDIMACS`, `tokens`, `int?`, `stdVar?` and `Names.var?`.
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
written with its standard name `x(v + 1)`, the name the parser reads as `v` (as in
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

## Main definitions

* `Cslib.Logic.PL.VeriPB.Text.printOPB`: an instance as OPB text.
* `Cslib.Logic.PL.VeriPB.Text.reread`: the instance the parser reads back.
* `Cslib.Logic.PL.VeriPB.Text.Normal`: the normal form of the parser.

## Main statements

* `Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.parseOPB_printOPB_of_normal`,
  `Cslib.Logic.PL.VeriPB.Text.parseDIMACS_toDIMACS`: the round trips.
* `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.holds_of_checkOPB_printOPB_sat`,
  `Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB_printOPB`,
  `Cslib.Logic.PL.VeriPB.Text.le_encard_of_checkOPB_printOPB_enumPartial`,
  `Cslib.Logic.PL.VeriPB.Text.encard_eq_of_checkOPB_printOPB_enumComplete`,
  `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS_toDIMACS`,
  `Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS_toDIMACS`: the soundness theorems end to
  end, from the acceptance of a proof against the printed text to the semantics of the instance
  or formula built in Lean, for every instance and formula.
-/

public section

namespace Cslib.Logic.PL.VeriPB.Text

open PBConstr

/-! ### Printing -/

/-- The standard name `x(v + 1)` of the variable `v`. -/
private def varChars (v : ℕ) : List Char := 'x' :: Nat.toDecimal (v + 1)

/-- A literal: `x(v + 1)` or `~x(v + 1)`. -/
private def litChars : Literal ℕ → List Char
  | (v, true) => varChars v
  | (v, false) => '~' :: varChars v

/-- The words of a term `a ℓ`. -/
private def termWords (t : ℕ × Literal ℕ) : List (List Char) :=
  [Nat.toDecimal t.1, litChars t.2]

/-- The words of the constraint line `a₁ ℓ₁ … >= d;`. -/
private def constrWords (c : PBConstr) : List (List Char) :=
  c.terms.flatMap termWords ++ [['>', '='], Nat.toDecimal c.degree, [';']]

/-- The words of the weights `w₁ x₁ …` of an objective, and of its constant if it is not `0`. -/
private def objTermWords (f : Objective) : List (List Char) :=
  f.lin.flatMap (fun e => [Int.toDecimal e.2, varChars e.1]) ++
    if f.const = 0 then [] else [Int.toDecimal f.const]

/-- The words of the objective line `min: w₁ x₁ … [k];`. -/
private def objWords (f : Objective) : List (List Char) :=
  ['m', 'i', 'n', ':'] :: objTermWords f ++ [[';']]

/-- The words of the line `preserved: x₁ …;`. -/
private def presWords (P : List ℕ) : List (List Char) :=
  ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 'd', ':'] :: P.map varChars ++ [[';']]

/-- One more than the largest variable of an instance, `0` for none. -/
private def opbVars (I : Instance) : ℕ :=
  ((I.constraints.flatMap fun c => c.terms.map termVar) ++
    ((I.objective.map fun f => f.lin.map Prod.fst).getD []) ++ I.preserved.getD []).foldr
      (fun v m => max (v + 1) m) 0

/-- The words of the header comment `* #variable= n #constraint= m`. -/
private def headerWords (I : Instance) : List (List Char) :=
  [['*'], ['#', 'v', 'a', 'r', 'i', 'a', 'b', 'l', 'e', '='], Nat.toDecimal (opbVars I),
    ['#', 'c', 'o', 'n', 's', 't', 'r', 'a', 'i', 'n', 't', '='],
    Nat.toDecimal I.constraints.length]

/-- A line: its words, each followed by a space, and a newline. -/
private def renderLine (ws : List (List Char)) : List Char := ws.flatMap (· ++ [' ']) ++ ['\n']

/-- The lines of an instance after the header: the objective, the preserved set and the
constraints. -/
private def bodyLines (I : Instance) : List (List (List Char)) :=
  (I.objective.map objWords).toList ++ (I.preserved.map presWords).toList ++
    I.constraints.map constrWords

/-- **An instance as OPB text**: the header comment, the objective line if there is an
objective, the `preserved:` line if there is a preserved set, and one line per constraint, the
variable `v` written `x(v + 1)`. -/
def printOPB (I : Instance) : String :=
  String.ofList ((headerWords I :: bodyLines I).flatMap renderLine)

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

open PBConstr

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
  rw [tokens, String.toList_ofList, hsplit, List.flatMap_singleton, htw]
  simpa [lexLine, flushToken] using lexLine_words [] hw

/-- **The tokens of the lines of a printed text**, with an empty last line. -/
private theorem lines_render {L : List (List (List Char))} (hL : ∀ l ∈ L, ∀ w ∈ l, IsWord w) :
    (lines (String.ofList (L.flatMap renderLine))).map tokens =
      L.map (·.map String.ofList) ++ [[]] := by
  rw [lines, String.toList_ofList]
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

private theorem dropChar?_ofList (c d : Char) (ds : List Char) :
    dropChar? c (String.ofList (d :: ds)) = if d == c then some (String.ofList ds) else none := by
  rw [dropChar?, String.toList_ofList]

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

private theorem stdVar?_varChars (v : ℕ) : stdVar? (String.ofList (varChars v)) = some v := by
  rw [varChars, stdVar?, dropChar?_ofList]
  simp [nat?_toDecimal]

private theorem var?_varChars (N : Names) (v : ℕ) :
    N.var? (String.ofList (varChars v)) = some v := by
  rw [Names.var?, stdVar?_varChars]

private theorem lit?_litChars (N : Names) (l : Literal ℕ) :
    N.lit? (String.ofList (litChars l)) = some l := by
  obtain ⟨v, _ | _⟩ := l
  · rw [litChars, Names.lit?, dropChar?_ofList]
    simp [var?_varChars]
  · rw [litChars, Names.lit?, varChars, dropChar?_ofList]
    simp only [show ('x' == '~') = false by decide, Bool.false_eq_true, ↓reduceIte]
    rw [← varChars, var?_varChars]
    rfl

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

/-- A literal word is neither `;` nor `:`. -/
private theorem litChars_ne (l : Literal ℕ) {s : String} (hs : s = ";" ∨ s = ":") :
    String.ofList (litChars l) ≠ s := by
  obtain ⟨v, _ | _⟩ := l <;> exact ofList_ne (by rcases hs with rfl | rfl <;> decide)

/-! #### Constraints and objectives -/

private theorem terms_stop (N : Names) (fuel : ℕ) {t : String} (rest : List String)
    (L : List (ℕ × ℤ)) (k : ℤ) (ht : t = ">=" ∨ t = ";") :
    terms N (fuel + 1) (t :: rest) L k = some (L, k, t :: rest) := by
  rcases ht with rfl | rfl <;> rfl

/-- The parser reads a coefficient word `ct` of value `a` and a literal `ℓ`. -/
private theorem terms_step (N : Names) (fuel : ℕ) {ct : List Char} {a : ℤ}
    (hct : ∃ d ds, ct = d :: ds ∧ (d = '-' ∨ d.isDigit = true))
    (ha : int? (String.ofList ct) = some a) (l : Literal ℕ) (rest : List String)
    (L : List (ℕ × ℤ)) (k : ℤ) :
    terms N (fuel + 1) (String.ofList ct :: String.ofList (litChars l) :: rest) L k =
      terms N fuel rest (insertCoeff l.1 (if l.2 then a else -a) L)
        (k + if l.2 then 0 else a) := by
  obtain ⟨d, ds, rfl, hd⟩ := hct
  have hk : ∀ s ∈ [">=", "<=", "=", ";", ":", "min:", "preserved:"],
      (String.ofList (d :: ds) == s) = false := fun s hs => by
    simpa using ne_keyword hd hs
  have hl : ∀ s, s = ";" ∨ s = ":" → (String.ofList (litChars l) == s) = false := fun s hs => by
    simpa using litChars_ne l hs
  rw [terms]
  simp only [hk ">=" (by simp), hk "<=" (by simp), hk "=" (by simp), hk ";" (by simp),
    hk ":" (by simp), Bool.or_false, Bool.false_eq_true, ↓reduceIte, ha, hl ";" (.inl rfl),
    hl ":" (.inr rfl), Option.isSome_some, Bool.and_false, lit?_litChars]
  obtain ⟨v, _ | _⟩ := l <;> simp

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

private theorem isWord_varChars (v : ℕ) : IsWord (varChars v) :=
  isWord_cons (isWord_toDecimal _) (toDecimal_ne_semi _) (by decide)

private theorem isWord_litChars (l : Literal ℕ) : IsWord (litChars l) := by
  obtain ⟨v, _ | _⟩ := l
  · exact isWord_cons (isWord_varChars v) (by simp [varChars]) (by decide)
  · exact isWord_varChars v

private theorem isWord_intToDecimal (a : ℤ) : IsWord (Int.toDecimal a) := by
  unfold Int.toDecimal
  split
  · exact isWord_cons (isWord_toDecimal _) (toDecimal_ne_semi _) (by decide)
  · exact isWord_toDecimal _

/-- The parser reads the terms of a constraint. -/
private theorem terms_terms (N : Names) (ts : List (ℕ × Literal ℕ)) (fuel : ℕ)
    (rest : List String) (L : List (ℕ × ℤ)) (k : ℤ) :
    terms N (fuel + ts.length) ((ts.flatMap termWords).map String.ofList ++ rest) L k =
      terms N fuel rest (linOf L ts) (negOf k ts) := by
  induction ts generalizing L k fuel with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, l⟩ := t
    simp only [List.flatMap_cons, List.length_cons, termWords, List.map_cons, List.cons_append,
      List.nil_append]
    obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons a
    rw [← Nat.add_assoc, terms_step N _ ⟨d, ds, h, .inr hd⟩ (int?_toDecimal a), ih]
    obtain ⟨v, _ | _⟩ := l <;> rfl

/-- The parser reads the weights of an objective. -/
private theorem terms_weights (N : Names) (es : List (ℕ × ℤ)) (fuel : ℕ)
    (rest : List String) (L : List (ℕ × ℤ)) (k : ℤ) :
    terms N (fuel + es.length)
        ((es.flatMap fun e => [Int.toDecimal e.2, varChars e.1]).map String.ofList ++ rest) L k =
      terms N fuel rest (es.foldl (fun L e => insertCoeff e.1 e.2 L) L) k := by
  induction es generalizing L k fuel with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_cons, List.map_cons, List.cons_append,
      List.nil_append]
    rw [← Nat.add_assoc, show varChars e.1 = litChars (e.1, true) from rfl,
      terms_step N _ (Int.exists_toDecimal_eq_cons e.2) (int?_intToDecimal e.2), ih]
    simp

private theorem constr_constrWords (N : Names) (c : PBConstr) :
    constr N ((constrWords c).map String.ofList) = some ([rereadConstr c], [";"]) := by
  have hlen : ((constrWords c).map String.ofList).length + 1 = (3 + 1 + c.terms.length) +
      c.terms.length := by
    simp [constrWords, termWords]
    omega
  rw [constr, hlen, constrWords, List.map_append, terms_terms]
  simp only [List.map_cons, List.map_nil]
  rw [show 3 + 1 + c.terms.length = (3 + c.terms.length) + 1 by omega,
    terms_stop N _ _ _ _ (.inl (by decide))]
  simp only [show String.ofList ['>', '='] = ">=" by decide, int?_toDecimal,
    show String.ofList [';'] = ";" by decide]
  simp [rereadConstr]

private theorem length_weightWords (es : List (ℕ × ℤ)) :
    (es.flatMap fun e => [Int.toDecimal e.2, varChars e.1]).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega

private theorem objective_objWords (N : Names) (f : Objective) :
    objective N ((objTermWords f ++ [[';']]).map String.ofList) = some (rereadObj f) := by
  rw [objective, objTerms]
  simp only [objTermWords, List.map_append, List.append_assoc, List.length_append,
    List.length_map, length_weightWords]
  by_cases h : f.const = 0
  · simp only [h, ↓reduceIte, List.map_nil, List.nil_append, List.length_nil, List.map_cons,
      List.length_cons, Nat.zero_add]
    rw [show 2 * f.lin.length + 1 + 1 = (f.lin.length + 1 + 1) + f.lin.length by omega,
      terms_weights, show String.ofList [';'] = ";" by decide,
      terms_stop N _ _ _ _ (.inr rfl)]
    simp [rereadObj, h]
  · obtain ⟨d, ds, hd, hd'⟩ := Int.exists_toDecimal_eq_cons f.const
    have hk : ∀ s ∈ [">=", "<=", "=", ";", ":", "min:", "preserved:"],
        String.ofList (Int.toDecimal f.const) ≠ s := fun s hs => hd ▸ ne_keyword hd' hs
    simp only [h, ↓reduceIte, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]
    rw [show 2 * f.lin.length + (0 + 1) + (0 + 1) + 1 = (f.lin.length + 2 + 1) + f.lin.length by
      omega, terms_weights, terms, show String.ofList [';'] = ";" by decide]
    simp [hk ">=" (by simp), hk "<=" (by simp), hk "=" (by simp), hk ";" (by simp),
      hk ":" (by simp), int?_intToDecimal, rereadObj]

private theorem presVars_presWords (N : Names) (P : List ℕ) :
    presVars N ((P.map varChars ++ [[';']]).map String.ofList) = some P := by
  induction P with
  | nil => simp only [List.map_nil, List.nil_append, List.map_cons]; rfl
  | cons v P ih =>
    rw [List.map_cons, List.cons_append, List.map_cons, presVars, var?_varChars]
    · rw [Option.bind_some, ih]
      rfl
    · simp

/-- The first token of a constraint line is not a keyword of the header lines and does not start
with `*`. -/
private theorem head_constrWords (c : PBConstr) :
    ∃ t ts, (constrWords c).map String.ofList = t :: ts ∧ startsWithChar '*' t = false ∧
      t ≠ "min:" ∧ t ≠ "preserved:" := by
  match hterms : c.terms with
  | [] =>
    have e : (constrWords c).map String.ofList =
        ">=" :: [Nat.toDecimal c.degree, [';']].map String.ofList := by
      rw [constrWords, hterms, List.flatMap_nil, List.nil_append, List.map_cons,
        show String.ofList ['>', '='] = ">=" by decide]
    exact ⟨_, _, e, by decide, by decide, by decide⟩
  | (a, l) :: rest =>
    obtain ⟨d, ds, h, hd⟩ := Nat.exists_toDecimal_eq_cons a
    have e : (constrWords c).map String.ofList = String.ofList (d :: ds) ::
        (litChars l :: (rest.flatMap termWords ++
          [['>', '='], Nat.toDecimal c.degree, [';']])).map String.ofList := by
      rw [constrWords, hterms, List.flatMap_cons, termWords, h]
      rfl
    refine ⟨_, _, e, ?_, ne_keyword (.inr hd) (by simp), ne_keyword (.inr hd) (by simp)⟩
    rw [startsWithChar_ofList]
    simpa using Dimacs.ne_of_isDigit hd (by decide)

private theorem opbLines_constrs (N : Names) (cs : List PBConstr) :
    opbLines N (cs.map fun c => (constrWords c).map String.ofList) =
      some (cs.map rereadConstr) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := constr_constrWords N c
    obtain ⟨t, ts, hts, ht, -⟩ := head_constrWords c
    rw [List.map_cons, hts, opbLines]
    rw [hts] at hc
    simp [ht, hc, ih]

/-! #### Instances -/

private theorem isWord_lines (I : Instance) :
    ∀ l ∈ headerWords I :: bodyLines I, ∀ w ∈ l, IsWord w := by
  have hsemi : IsWord [';'] := .inl rfl
  have hconstr : ∀ c : PBConstr, ∀ w ∈ constrWords c, IsWord w := by
    intro c w hw
    simp only [constrWords, List.mem_append, List.mem_flatMap, termWords, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with ⟨t, -, rfl | rfl⟩ | rfl | rfl | rfl
    · exact isWord_toDecimal _
    · exact isWord_litChars _
    · decide
    · exact isWord_toDecimal _
    · exact hsemi
  intro l hl w hw
  simp only [bodyLines, List.mem_cons, List.mem_append, Option.mem_toList,
    Option.map_eq_some_iff, List.mem_map] at hl
  rcases hl with rfl | (⟨f, -, rfl⟩ | ⟨P, -, rfl⟩) | ⟨c, -, rfl⟩
  · simp only [headerWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact isWord_toDecimal _
    · decide
    · exact isWord_toDecimal _
  · simp only [objWords, objTermWords, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | ⟨e, -, rfl | rfl⟩ | hw) | rfl
    · decide
    · exact isWord_intToDecimal _
    · exact isWord_varChars _
    · split at hw
      · simp at hw
      · rw [List.mem_singleton.1 hw]
        exact isWord_intToDecimal _
    · exact hsemi
  · simp only [presWords, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false] at hw
    rcases hw with (rfl | ⟨v, -, rfl⟩) | rfl
    · decide
    · exact isWord_varChars _
    · exact hsemi
  · exact hconstr c w hw

/-- The token lines of the constraints. -/
private def constrLines (I : Instance) : List (List String) :=
  I.constraints.map fun c => (constrWords c).map String.ofList

private theorem head_constrLines {I : Instance} {l : List String} (hl : l ∈ constrLines I) :
    ∃ t ts, l = t :: ts ∧ startsWithChar '*' t = false ∧ t ≠ "min:" ∧ t ≠ "preserved:" := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
  exact head_constrWords c

/-- The token lines of a printed instance, after dropping the comments and empty lines. -/
private theorem filter_lines (I : Instance) (p : List String → Bool) (hnil : p [] = false)
    (hstar : ∀ t ts, startsWithChar '*' t = true → p (t :: ts) = false)
    (hpos : ∀ t ts, startsWithChar '*' t = false → p (t :: ts) = true) :
    ((lines (printOPB I)).map tokens).filter p =
      (I.objective.map fun f => "min:" :: (objTermWords f ++ [[';']]).map String.ofList).toList ++
        (I.preserved.map fun P => "preserved:" :: (P.map varChars ++ [[';']]).map
          String.ofList).toList ++ constrLines I := by
  rw [printOPB, lines_render (isWord_lines I), List.map_cons, List.cons_append, List.filter_cons,
    headerWords, List.map_cons, hstar _ _ (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte, bodyLines, List.map_append, List.filter_append]
  have hc : (constrLines I).filter p = constrLines I := by
    refine List.filter_eq_self.2 fun l hl => ?_
    obtain ⟨t, ts, rfl, ht, -⟩ := head_constrLines hl
    exact hpos t ts ht
  have hmin : String.ofList ['m', 'i', 'n', ':'] = "min:" := by decide
  have hpres : String.ofList ['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 'd', ':'] = "preserved:" := by
    decide
  rw [show (I.constraints.map constrWords).map (·.map String.ofList) = constrLines I by
    simp [constrLines, Function.comp_def]]
  rw [hc]
  cases I.objective <;> cases I.preserved <;>
    simp [objWords, presWords, hmin, hpres, hnil, hpos _ _ (show startsWithChar '*' "min:" = false
      by decide), hpos _ _ (show startsWithChar '*' "preserved:" = false by decide)]

/-- No constraint line starts with `min:` or `preserved:`. -/
private theorem constrLines_ne (I : Instance) (ts : List String) (ls : List (List String)) :
    constrLines I ≠ ("min:" :: ts) :: ls ∧ constrLines I ≠ ("preserved:" :: ts) :: ls := by
  constructor <;> intro h <;>
    obtain ⟨t, ts', ht, -, hmin, hpres⟩ := head_constrLines (h ▸ List.mem_cons_self)
  · exact hmin (List.cons.inj ht).1.symm
  · exact hpres (List.cons.inj ht).1.symm

/-- **The parser reads back a printed instance**, normalized: for every instance `I`, the text
`printOPB I` parses, with the standard names `x(v + 1)`, to `reread I`, which has the same
solutions and objective values as `I`. -/
theorem parseOPB_printOPB (I : Instance) : parseOPB (printOPB I) = some (reread I) := by
  have hc : opbLines ⟨[], 0⟩ (constrLines I) = some (I.constraints.map rereadConstr) :=
    opbLines_constrs ⟨[], 0⟩ I.constraints
  have hne := constrLines_ne I
  have hobj : ∀ f, objective ⟨[], 0⟩ ((objTermWords f).map String.ofList ++ [";"]) =
      some (rereadObj f) := fun f => by simpa using objective_objWords ⟨[], 0⟩ f
  have hpres : ∀ P, presVars ⟨[], 0⟩ (P.map (String.ofList ∘ varChars) ++ [";"]) = some P :=
    fun P => by simpa using presVars_presWords ⟨[], 0⟩ P
  unfold parseOPB
  simp only
  rw [filter_lines I _ rfl (fun t ts h => by simp [h]) (fun t ts h => by simp [h])]
  obtain ⟨cs, obj, pres⟩ := I
  cases obj <;> cases pres <;>
    simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
      List.nil_append, List.cons_append] <;>
    (try split) <;> simp_all [reread] <;> obtain ⟨rfl, rfl⟩ := ‹_ ∧ _› <;> simp_all

/-! #### The normal form and the semantics -/

private theorem insertCoeff_of_not_mem {v : ℕ} {L : List (ℕ × ℤ)} (h : v ∉ L.map Prod.fst)
    (a : ℤ) : insertCoeff v a L = L ++ [(v, a)] := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [insertCoeff]
    simp only [Ne.symm h.1, ↓reduceIte, ih h.2]
    rfl

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
  rw [tokens, String.toList_ofList, hsplit, List.flatMap_singleton, htw]

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
  rw [CNF.toDIMACS, lines, String.toList_ofList, hH, List.append_assoc, List.singleton_append,
    splitChars_append _ (fun c hc => by simpa using (hHc c hc).1) (by decide),
    hsplit]
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

/-- **The parser reads back exactly what is printed** from an instance in its normal form
(`Cslib.Logic.PL.VeriPB.Text.Normal`), with the standard names: the variable `v` is printed
`x(v + 1)` and read back as `v`. -/
theorem parseOPB_printOPB_of_normal {I : Instance} (h : Normal I) :
    parseOPB (printOPB I) = some I := by
  rw [parseOPB_printOPB, reread_eq h]

/-- The instance a checker reads from a printed instance. -/
private theorem eq_reread {I J : Instance} (h : parseOPB (printOPB I) = some J) : J = reread I := by
  rw [parseOPB_printOPB] at h
  exact (Option.some.inj h).symm

/-- **Soundness of `UNSAT` end to end**: an accepted proof of `UNSAT` against the printed text
of an instance `I` built in Lean means that the constraints of `I` have no 0/1 solution. -/
theorem not_satisfiable_of_checkOPB_printOPB {I : Instance} {pbp : String} {out : Option String}
    {q : ℕ} (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.unsat q)) :
    ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨J, hJ, hσ⟩ := not_satisfiable_of_checkOPB h
  cases eq_reread hJ
  exact fun σ hs => hσ σ ((forall_holds_reread_iff I σ).2 hs)

/-- **Soundness of `SAT` end to end**: an accepted proof of `SAT` against the printed text of an
instance `I` means that the constraints of `I` have a 0/1 solution. -/
theorem exists_satisfies_of_checkOPB_printOPB {I : Instance} {pbp : String}
    {out : Option String} {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.sat asg)) :
    ∃ σ : ℕ → Bool, ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨J, hJ, σ, hσ⟩ := exists_satisfies_of_checkOPB h
  cases eq_reread hJ
  exact ⟨σ, (forall_holds_reread_iff I σ).1 hσ⟩

/-- **Soundness of `SAT : ρ` end to end**: the stated assignment `ρ` solves the constraints of
the instance `I` whose printed text the proof is checked against. -/
theorem holds_of_checkOPB_printOPB_sat {I : Instance} {pbp : String} {out : Option String}
    {ρ : List (Literal ℕ)}
    (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.sat (some ρ))) :
    ∀ c ∈ I.constraints, c.Holds (assignOf ρ) := by
  obtain ⟨J, hJ, hσ⟩ := holds_of_checkOPB_sat h
  cases eq_reread hJ
  exact (forall_holds_reread_iff I _).1 hσ

/-- **Soundness of `BOUNDS` end to end**: an accepted proof of `BOUNDS lb : q ub` against the
printed text of an instance `I` means that `I` has an objective `f`, every 0/1 solution `σ` of
its constraints has a finite `lb` with `lb ≤ f σ`, and for a finite `ub` some solution has
objective at most `ub`. -/
theorem bounds_of_checkOPB_printOPB {I : Instance} {pbp : String} {out : Option String}
    {lb ub : Option ℤ} {q : ℕ} {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.bounds lb q ub asg)) :
    ∃ f, I.objective = some f ∧
      (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → ∃ l, lb = some l ∧ l ≤ f.eval σ) ∧
      ∀ u, ub = some u → ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ u := by
  obtain ⟨J, f', hJ, hf', hlb, hub⟩ := bounds_of_checkOPB h
  cases eq_reread hJ
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hf'
  refine ⟨f, hf, fun σ hσ => ?_, fun u hu => ?_⟩
  · obtain ⟨l, hl, hle⟩ := hlb σ ((forall_holds_reread_iff I σ).2 hσ)
    exact ⟨l, hl, eval_rereadObj f σ ▸ hle⟩
  · obtain ⟨σ, hσ, hle⟩ := hub u hu
    exact ⟨σ, (forall_holds_reread_iff I σ).1 hσ, eval_rereadObj f σ ▸ hle⟩

/-- The read-back constraints have the same projections. -/
private theorem projections_reread (I : Instance) (P : List ℕ) :
    projections (reread I).constraints P = projections I.constraints P := by
  ext l
  simp only [projections, Set.mem_ofPred_eq, forall_holds_reread_iff]

/-- **Soundness of a partial enumeration end to end**: an accepted proof of
`ENUMERATION_PARTIAL n` against the printed text of an instance `I` means that `I` has a
preserved set `P` and its solutions have at least `n` distinct projections to `P`. -/
theorem le_encard_of_checkOPB_printOPB_enumPartial {I : Instance} {pbp : String}
    {out : Option String} {n : ℕ}
    (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.enumPartial n)) :
    ∃ P, I.preserved = some P ∧ (n : ℕ∞) ≤ (projections I.constraints P).encard := by
  obtain ⟨J, P, hJ, hP, hn⟩ := le_encard_of_checkOPB_enumPartial h
  cases eq_reread hJ
  exact ⟨P, hP, projections_reread I P ▸ hn⟩

/-- **Soundness of a complete enumeration end to end**: an accepted proof of
`ENUMERATION_COMPLETE n : q` against the printed text of an instance `I` means that `I` has a
preserved set `P` and its solutions have exactly `n` distinct projections to `P`. -/
theorem encard_eq_of_checkOPB_printOPB_enumComplete {I : Instance} {pbp : String}
    {out : Option String} {n q : ℕ}
    (h : (checkOPBOutput (printOPB I) pbp out).map (·.1) = some (.enumComplete n q)) :
    ∃ P, I.preserved = some P ∧ (projections I.constraints P).encard = n := by
  obtain ⟨J, P, hJ, hP, hn⟩ := encard_eq_of_checkOPB_enumComplete h
  cases eq_reread hJ
  exact ⟨P, hP, projections_reread I P ▸ hn⟩

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
