/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Foundations.Data.Nat.ToDigits

/-! # Reading and writing DIMACS CNF

The DIMACS CNF format of SAT solvers and benchmarks: a header `p cnf V C` giving the number of
variables and clauses, then the clauses, each a list of nonzero integers ended by `0`, the integer
`i` standing for variable `|i|`, negated if `i < 0`. Lines starting with `c` are comments.

`Cslib.Logic.PL.CNF.ofDIMACS` reads a formula, numbering the variables as the LRAT checker does
(`Cslib.Logic.PL.Literal.ofDIMACS`): the DIMACS variable `v` is the variable `v - 1`, so that a
certificate for the formula read refers to the same variables as the file. It checks the header:
the literals are within its number of variables and the clauses are as many as it says. As in
the SATLIB benchmarks, a line `%` ends the formula. A line is split into words at whitespace
(`Char.isWhitespace`). A number is read as `String.toNat?` and `String.toInt?` read it: a nonempty
string of decimal digits with `_` digit separators, each between two digits (`1_000`), an
integer one with an optional `-`. The digits themselves are read by the decimal reader
`Nat.ofDecimal?` shared with the OPB front end.

`Cslib.Logic.PL.CNF.toDIMACS` writes a formula, the header giving one more variable than the
largest, and one clause per line. It is defined on lists of characters, so the kernel evaluates
it.

**Round trip.** Reading what `Cslib.Logic.PL.CNF.toDIMACS` writes gives the formula back
(`Cslib.Logic.PL.CNF.ofDIMACS_toDIMACS`), for every formula: repeated literals, empty clauses and
the empty formula included. So a theorem about the formula read from `φ.toDIMACS` is a theorem
about `φ`, and for formulas built in Lean the parser is not part of what is trusted. For a file
written by other tools, the parser is still trusted to read it as intended.

## Main definitions

* `Cslib.Logic.PL.CNF.ofDIMACS`: reading a formula.
* `Cslib.Logic.PL.CNF.toDIMACS`: writing a formula.

## Main statements

* `Cslib.Logic.PL.CNF.ofDIMACS_toDIMACS`: reading what is written gives the formula back.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace Dimacs

/-! ### Words and numbers -/

/-- The word in progress, `cur` reversed, if it is not empty. -/
def flushWord (cur : List Char) : List (List Char) := if cur.isEmpty then [] else [cur.reverse]

/-- The words of a line: its maximal runs of characters other than whitespace, `cur` the word
in progress, reversed. -/
def words : List Char → List Char → List (List Char)
  | [], cur => flushWord cur
  | c :: cs, cur => if c.isWhitespace then flushWord cur ++ words cs [] else words cs (c :: cur)

/-- Whether `cs` is a nonempty string of decimal digits with `_` digit separators, each between
two digits, as `String.isNat` checks; `last` tells whether a digit comes before `cs`. -/
def isNatChars : Bool → List Char → Bool
  | last, [] => last
  | last, c :: cs =>
    if c == '_' then last && isNatChars false cs else c.isDigit && isNatChars true cs

/-- A natural number, as `String.toNat?` reads it: decimal digits with `_` digit separators, each
between two digits. The separators are dropped and the digits read by `Nat.ofDecimal?`. -/
def natOfChars? (cs : List Char) : Option ℕ :=
  if isNatChars false cs then Nat.ofDecimal? (cs.filter (· != '_')) else none

/-- An integer: a natural number with an optional `-`. -/
def intOfChars? : List Char → Option ℤ
  | '-' :: cs => (natOfChars? cs).map fun n : ℕ => -(n : ℤ)
  | cs => (natOfChars? cs).map fun n : ℕ => (n : ℤ)

/-! ### Reading -/

/-- Read the literal tokens `toks` of a body over `nvars` variables, with `cls` the clauses read
and `cur` the clause in progress: `0` ends a clause. Fails on a token that is not an integer and
a literal beyond the variables. -/
def readLits (nvars : ℕ) :
    List (List Char) → Array (Clause ℕ) → Array (Literal ℕ) →
      Except String (Array (Clause ℕ) × Array (Literal ℕ))
  | [], cls, cur => .ok (cls, cur)
  | tok :: toks, cls, cur =>
    match intOfChars? tok with
    | none => .error s!"DIMACS: '{String.ofList tok}' is not an integer"
    | some i =>
      match Literal.ofDIMACS i with
      | none => readLits nvars toks (cls.push cur.toList) #[]
      | some l =>
        if nvars ≤ l.1 then .error s!"DIMACS: the literal {i} exceeds the {nvars} variables"
        else readLits nvars toks cls (cur.push l)

/-- The header `p cnf V C`, as words. -/
def header? : List (List Char) → Option (ℕ × ℕ)
  | [['p'], ['c', 'n', 'f'], v, c] =>
    match natOfChars? v, natOfChars? c with
    | some v, some c => some (v, c)
    | _, _ => none
  | _ => none

/-- Read the lines `ls`, with `hd` the header read, `cls` the clauses read and `cur` the clause in
progress. Empty lines and lines starting with `c` are skipped, and a line starting with `%` ends
the formula. -/
def readLines (hd : Option (ℕ × ℕ)) (cls : Array (Clause ℕ)) (cur : Array (Literal ℕ)) :
    List String → Except String (Option (ℕ × ℕ) × Array (Clause ℕ) × Array (Literal ℕ))
  | [] => .ok (hd, cls, cur)
  | line :: ls =>
    match words line.toList [] with
    | [] => readLines hd cls cur ls
    | tok :: toks =>
      if tok.head? = some 'c' then readLines hd cls cur ls
      else if tok.head? = some '%' then .ok (hd, cls, cur)
      else if tok.head? = some 'p' then
        if hd.isSome then .error "DIMACS: a second header"
        else
          match header? (tok :: toks) with
          | some h => readLines (some h) cls cur ls
          | none => .error s!"DIMACS: malformed header '{line}'"
      else
        match hd with
        | none => .error "DIMACS: a clause before the header"
        | some (nvars, nc) =>
          match readLits nvars (tok :: toks) cls cur with
          | .error e => .error e
          | .ok (cls', cur') => readLines (some (nvars, nc)) cls' cur' ls

end Dimacs

open Dimacs in
/-- **Reading a DIMACS CNF formula**, with the DIMACS variable `v` as the variable `v - 1`. Fails
on a missing or malformed header, a token that is not an integer, a literal beyond the number of
variables of the header, an unterminated last clause, or a number of clauses other than the
header's. A line starting with `%` ends the formula, as in the SATLIB benchmarks. -/
def CNF.ofDIMACS (s : String) : Except String (CNF ℕ) := do
  let (header, clauses, cur) ← readLines none #[] #[] ((s.split '\n').toList.map String.Slice.copy)
  let some (_, nclauses) := header | throw "DIMACS: no header"
  unless cur.isEmpty do throw "DIMACS: the last clause is not ended by 0"
  unless clauses.size = nclauses do
    throw s!"DIMACS: {clauses.size} clauses, but the header says {nclauses}"
  return clauses.toList

/-! ### Writing -/

namespace Dimacs

/-- A literal as a DIMACS integer (`Cslib.Logic.PL.Literal.toDIMACS`): the variable `v` as `v + 1`,
negated if the literal is. -/
def litChars (l : Literal ℕ) : List Char := Int.toDecimal l.toDIMACS

/-- A clause as a DIMACS line: its literals, `0` and a newline. -/
def clauseChars (cl : Clause ℕ) : List Char :=
  cl.flatMap (litChars · ++ [' ']) ++ ['0', '\n']

/-- The header line `p cnf V C`. -/
def headerChars (V C : ℕ) : List Char :=
  ['p', ' ', 'c', 'n', 'f', ' '] ++ Nat.toDecimal V ++ ' ' :: Nat.toDecimal C ++ ['\n']

end Dimacs

/-- The number of variables of a formula in DIMACS: one more than the largest, `0` for none. -/
def CNF.dimacsVars (φ : CNF ℕ) : ℕ := φ.vars.foldr (fun v m => max (v + 1) m) 0

open Dimacs in
/-- **Writing a DIMACS CNF formula**: the header `p cnf V C`, with `V` one more than the largest
variable, then one clause per line, the variable `v` as the DIMACS variable `v + 1`. -/
def CNF.toDIMACS (φ : CNF ℕ) : String :=
  String.ofList (headerChars φ.dimacsVars φ.length ++ φ.flatMap clauseChars)

/-! ### Reading what is written -/

namespace Dimacs

/-- A decimal digit is not whitespace. -/
theorem isWhitespace_eq_false_of_isDigit {c : Char} (h : c.isDigit = true) :
    c.isWhitespace = false := by
  simp only [Char.isWhitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> exact absurd h (by decide)

/-- The characters of a literal are not whitespace. -/
theorem isWhitespace_of_mem_litChars {l : Literal ℕ} {c : Char} (h : c ∈ litChars l) :
    c.isWhitespace = false :=
  (Int.mem_toDecimal h).elim (fun h => h ▸ by decide) isWhitespace_eq_false_of_isDigit

/-- A run of characters other than whitespace joins the word in progress. -/
theorem words_append {w rest cur : List Char} (hw : ∀ c ∈ w, c.isWhitespace = false) :
    words (w ++ rest) cur = words rest (w.reverse ++ cur) := by
  induction w generalizing cur with
  | nil => rfl
  | cons c w ih =>
    simp [words, hw c List.mem_cons_self, ih fun d hd => hw d (List.mem_cons_of_mem _ hd)]

/-- The words of words each followed by a space. -/
theorem words_flatMap_space {ws : List (List Char)} (rest : List Char)
    (hw : ∀ w ∈ ws, w ≠ [] ∧ ∀ c ∈ w, c.isWhitespace = false) :
    words (ws.flatMap (· ++ [' ']) ++ rest) [] = ws ++ words rest [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hne, hc⟩ := hw w List.mem_cons_self
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc, words_append hc,
      List.singleton_append, words]
    simp [flushWord, hne, show (' ' : Char).isWhitespace = true by decide,
      ih fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')]

/-- A nonempty run of characters other than whitespace is one word. -/
theorem words_of_forall {w : List Char} (hne : w ≠ []) (hw : ∀ c ∈ w, c.isWhitespace = false) :
    words w [] = [w] := by
  simpa [words, flushWord, hne] using words_append (rest := []) (cur := []) hw

/-- A decimal digit is not the character `c` of `cs`, for the characters that the reader
treats specially. -/
theorem ne_of_isDigit {d c : Char} (hd : d.isDigit = true) (hc : c.isDigit = false) : d ≠ c :=
  fun h => by simp_all

/-- Decimal digits without separators pass the separator check. -/
theorem isNatChars_of_isDigit {cs : List Char} (h : ∀ c ∈ cs, c.isDigit = true) :
    isNatChars true cs = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [isNatChars,
      beq_eq_false_iff_ne.2 (ne_of_isDigit (h c List.mem_cons_self) (c := '_') (by decide)),
      h c List.mem_cons_self, ih fun d hd => h d (List.mem_cons_of_mem _ hd)]

/-- **Reading the digits of a number.** -/
@[simp] theorem natOfChars?_toDecimal (n : ℕ) : natOfChars? (Nat.toDecimal n) = some n := by
  have hd := fun c (hc : c ∈ Nat.toDecimal n) => Nat.isDigit_of_mem_toDecimal hc
  obtain ⟨d, ds, h, hd₀⟩ := Nat.exists_toDecimal_eq_cons n
  have hsep : isNatChars false (Nat.toDecimal n) = true := by
    rw [h, isNatChars]
    simp [beq_eq_false_iff_ne.2 (ne_of_isDigit hd₀ (c := '_') (by decide)), hd₀,
      isNatChars_of_isDigit fun c hc => hd c (h ▸ List.mem_cons_of_mem _ hc)]
  have hf : (Nat.toDecimal n).filter (· != '_') = Nat.toDecimal n :=
    List.filter_eq_self.2 fun c hc => by simpa using ne_of_isDigit (hd c hc) (c := '_') (by decide)
  simp [natOfChars?, hsep, hf]

/-- A word not starting with `-` is read as a natural number. -/
theorem intOfChars?_of_ne {c : Char} {cs : List Char} (h : c ≠ '-') :
    intOfChars? (c :: cs) = (natOfChars? (c :: cs)).map fun n : ℕ => (n : ℤ) := by
  unfold intOfChars?
  split
  · exact absurd (List.cons.inj ‹_›).1 h
  · rfl

/-- **Reading the digits of an integer.** -/
@[simp] theorem intOfChars?_toDecimal (a : ℤ) : intOfChars? a.toDecimal = some a := by
  unfold Int.toDecimal
  split
  · simp [intOfChars?]
    omega
  · obtain ⟨d, ds, hds, hd⟩ := Nat.exists_toDecimal_eq_cons a.natAbs
    rw [hds, intOfChars?_of_ne (ne_of_isDigit hd (by decide)), ← hds]
    simp
    omega

/-- **Reading a literal**: the integer of its word names it. -/
theorem ofDIMACS_intOfChars?_litChars (l : Literal ℕ) :
    ∃ i, intOfChars? (litChars l) = some i ∧ Literal.ofDIMACS i = some l :=
  ⟨_, intOfChars?_toDecimal _, Literal.ofDIMACS_toDIMACS l⟩

/-- Reading the word of a literal adds it to the clause in progress. -/
theorem readLits_litChars {nvars : ℕ} {l : Literal ℕ} (hl : l.1 < nvars)
    (toks : List (List Char)) (cls : Array (Clause ℕ)) (cur : Array (Literal ℕ)) :
    readLits nvars (litChars l :: toks) cls cur = readLits nvars toks cls (cur.push l) := by
  simp [readLits, litChars, Literal.ofDIMACS_toDIMACS, show ¬ nvars ≤ l.1 by omega]

/-- **Reading a clause line.** -/
theorem readLits_clause {nvars : ℕ} {cl : Clause ℕ} (hcl : ∀ l ∈ cl, l.1 < nvars)
    (cls : Array (Clause ℕ)) (cur : Array (Literal ℕ)) :
    readLits nvars (cl.map litChars ++ [['0']]) cls cur =
      .ok (cls.push (cur.toList ++ cl), #[]) := by
  induction cl generalizing cur with
  | nil => simp [readLits, show intOfChars? ['0'] = some 0 by decide, Literal.ofDIMACS]
  | cons l cl ih =>
    simp [readLits_litChars (hcl l List.mem_cons_self),
      ih fun l' hl' => hcl l' (List.mem_cons_of_mem _ hl')]

/-- The word of a literal is not empty. -/
theorem litChars_ne_nil (l : Literal ℕ) : litChars l ≠ [] := Int.toDecimal_ne_nil _

/-- The words of a clause line. -/
theorem words_clause (cl : Clause ℕ) :
    words (cl.flatMap (litChars · ++ [' ']) ++ ['0']) [] = cl.map litChars ++ [['0']] := by
  rw [show cl.flatMap (litChars · ++ [' ']) = (cl.map litChars).flatMap (· ++ [' ']) by
    simp [List.flatMap_map], words_flatMap_space]
  · rfl
  · intro _ hw
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨litChars_ne_nil l, fun _ => isWhitespace_of_mem_litChars⟩

/-- The first word of a clause line starts with a digit or `-`. -/
theorem exists_words_clause_eq_cons (cl : Clause ℕ) :
    ∃ tok toks, cl.map litChars ++ [['0']] = tok :: toks ∧
      ∀ c ∈ tok.head?, c = '-' ∨ c.isDigit = true := by
  match cl with
  | [] => exact ⟨['0'], [], rfl, by simp⟩
  | l :: cl =>
    obtain ⟨d, ds, h, hd⟩ := Int.exists_toDecimal_eq_cons l.toDIMACS
    exact ⟨_, _, rfl, by simpa [litChars, h] using hd⟩

/-- Splitting at the first newline. -/
theorem splitOn_newline {a : List Char} (b : List Char) (h : ∀ c ∈ a, c ≠ '\n') :
    (a ++ '\n' :: b).splitOn '\n' = a :: b.splitOn '\n' := by
  rw [List.splitOn_eq_splitOnP, List.splitOnP_append_cons_of_forall_mem
    (fun x hx => beq_eq_false_iff_ne.2 (h x hx)) _ (by decide)]
  exact congrArg _ List.splitOn_eq_splitOnP.symm

/-- A clause line has no newline before its end. -/
theorem ne_newline_of_mem_clause {cl : Clause ℕ} {c : Char}
    (h : c ∈ cl.flatMap (litChars · ++ [' ']) ++ ['0']) : c ≠ '\n' := by
  rintro rfl
  obtain ⟨l, -, hc⟩ : ∃ l ∈ cl, '\n' ∈ litChars l := by simpa using h
  exact absurd (isWhitespace_of_mem_litChars hc) (by decide)

/-- **Reading the clause lines.** -/
theorem readLines_clauses {V C : ℕ} (φ : CNF ℕ) (hφ : ∀ v ∈ CNF.vars φ, v < V)
    (cls : Array (Clause ℕ)) :
    readLines (some (V, C)) cls #[] (((φ.flatMap clauseChars).splitOn '\n').map String.ofList) =
      .ok (some (V, C), cls ++ φ.toArray, #[]) := by
  induction φ generalizing cls with
  | nil => simp [readLines, words, flushWord]
  | cons cl φ ih =>
    have hcl : ∀ l ∈ cl, l.1 < V := fun l hl =>
      hφ l.1 (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨cl, List.mem_cons_self, hl⟩, rfl⟩)
    have hφ' : ∀ v ∈ CNF.vars φ, v < V := fun v hv => hφ v (by
      simp only [CNF.vars, List.flatten_cons, List.map_append, List.mem_append]; exact .inr hv)
    obtain ⟨tok, toks, htoks, hhead⟩ := exists_words_clause_eq_cons cl
    have hc : ∀ c, c.isDigit = false → c ≠ '-' → tok.head? ≠ some c := fun c _ _ h => by
      rcases hhead c h with rfl | _ <;> simp_all
    rw [List.flatMap_cons, show clauseChars cl ++ φ.flatMap clauseChars =
      (cl.flatMap (litChars · ++ [' ']) ++ ['0']) ++ '\n' :: φ.flatMap clauseChars by
        simp [clauseChars], splitOn_newline _ fun _ hc => ne_newline_of_mem_clause hc,
      List.map_cons, readLines, String.toList_ofList, words_clause, htoks]
    simp only [hc 'c' (by decide) (by decide), hc '%' (by decide) (by decide),
      hc 'p' (by decide) (by decide), ↓reduceIte, ← htoks, readLits_clause hcl,
      List.nil_append, ih hφ']
    simp

end Dimacs

/-- The variables of a formula are below its number of variables. -/
theorem CNF.lt_dimacsVars {φ : CNF ℕ} {v : ℕ} (h : v ∈ φ.vars) : v < φ.dimacsVars := by
  unfold CNF.dimacsVars
  generalize φ.vars = l at h ⊢
  induction l with
  | nil => simp at h
  | cons w ws ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact (ih h).trans_le (le_max_right _ _)

open Dimacs in
/-- **Reading what is written gives the formula back**, for every formula. -/
theorem CNF.ofDIMACS_toDIMACS (φ : CNF ℕ) : CNF.ofDIMACS φ.toDIMACS = .ok φ := by
  have hdec (n : ℕ) : ∀ c ∈ Nat.toDecimal n, c.isWhitespace = false :=
    fun _ hc => isWhitespace_eq_false_of_isDigit (Nat.isDigit_of_mem_toDecimal hc)
  have hnl : ∀ c ∈ ['p', ' ', 'c', 'n', 'f', ' '] ++ Nat.toDecimal φ.dimacsVars ++
      ' ' :: Nat.toDecimal φ.length, c ≠ '\n' := by
    rintro c hc rfl
    rcases (by simpa using hc : '\n' ∈ Nat.toDecimal φ.dimacsVars ∨ '\n' ∈ Nat.toDecimal φ.length)
      with h | h <;> exact absurd (Nat.isDigit_of_mem_toDecimal h) (by decide)
  have hwords : words (['p', ' ', 'c', 'n', 'f', ' '] ++ Nat.toDecimal φ.dimacsVars ++
      ' ' :: Nat.toDecimal φ.length) [] =
      [['p'], ['c', 'n', 'f'], Nat.toDecimal φ.dimacsVars, Nat.toDecimal φ.length] := by
    simp only [List.cons_append, List.nil_append, words,
      show ('p' : Char).isWhitespace = false by decide,
      show ('c' : Char).isWhitespace = false by decide,
      show ('n' : Char).isWhitespace = false by decide,
      show ('f' : Char).isWhitespace = false by decide,
      show (' ' : Char).isWhitespace = true by decide, ↓reduceIte, flushWord]
    rw [words_append (hdec _), words]
    simp [flushWord, Nat.toDecimal_ne_nil, show (' ' : Char).isWhitespace = true by decide,
      words_of_forall (Nat.toDecimal_ne_nil _) (hdec _)]
  rw [CNF.ofDIMACS, CNF.toDIMACS, String.toList_split_char, String.toList_ofList, headerChars,
    List.append_assoc _ ['\n'], List.singleton_append, splitOn_newline _ hnl, List.map_cons,
    readLines, String.toList_ofList, hwords]
  simp [header?, readLines_clauses φ fun _ => CNF.lt_dimacsVars, bind, Except.bind, pure,
    Except.pure]



end Cslib.Logic.PL
