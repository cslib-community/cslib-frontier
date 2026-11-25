/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.ToDigits
public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast

/-!
# A text front end for the VeriPB kernel-proof checker

Parsers for the input formats of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] and for a fragment of the kernel proof format,
extended as described below, producing the abstract syntax checked by
`Cslib.Logic.PL.VeriPB.checkRed`:

* an OPB instance (`Cslib.Logic.PL.VeriPB.Text.parseOPB`, `Cslib.Logic.PL.VeriPB.Instance`): an
  optional objective line `min: ∑ wᵢ ℓᵢ [k];`, with an optional constant `k`, and an optional
  preserved-set line `preserved: x₁ … xₙ;`, in either order, before the constraints
  (`Cslib.Logic.PL.VeriPB.Objective`), then one constraint `∑ aᵢ ℓᵢ ⋈ A;` per line with `⋈` one
  of `>=`, `<=`, `=`, an equality counting as the two constraints `≥` and `≤` in this order; lines
  starting with `*` are comments;
* a DIMACS CNF formula (`Cslib.Logic.PL.VeriPB.Text.parseDIMACS`): the header `p cnf V C`, then
  exactly `C` clauses over the variables `1, …, V`, its clause `1 -2 3 0` read as the constraint
  `x1 + ~x2 + x3 >= 1` (`Cslib.Logic.PL.Clause.toPB`);
* a proof: the header `pseudo-Boolean proof version 3.0`, the line `f N;` checked against the
  number of constraints, the derivation steps, an output section (§4.2), `NONE` (for
  `Cslib.Logic.PL.VeriPB.Text.parseProof`) or a guarantee `DERIVABLE`, `EQUISATISFIABLE`,
  `EQUIOPTIMAL` or `EQUIENUMERABLE` with `FILE` or `IMPLICIT` (CakePB parses only `FILE`), a
  conclusion `UNSAT : id`, `SAT [: ρ]`,
  `BOUNDS lb : id ub [: ρ]` (§4.3, with `INF` for an infinite bound), `ENUMERATION_PARTIAL n`,
  `ENUMERATION_COMPLETE n : id` or `NONE`, and
  `end pseudo-Boolean proof;`.

**Supported fragment and extensions.** The parser accepts a fragment of the kernel format (§6.1 of
the VeriPB/CakePB documentation, 22 June 2026 edition), with extensions from the augmented format.
First, the line `f N;` is optional, as in the general format (§4.1). The kernel format requires it
as the first command after the header (§6.1), but a proof without it is accepted and checked against
the parsed formula. Second, `red`, `dom`, the checked `delc` and `obju` may omit their subproof, and
a goal is also autoproven when it is a constraint of the database up to the order of its terms
(`Cslib.Logic.PL.VeriPB.sameUpToOrder`). `preserved_add` and `preserved_rm` may also omit
`: subproof … qed;`, but then only a goal of degree `0` after normalization is autoproven, not one
that is a constraint up to order. The strict kernel format requires the subproof (§6.1). The `red`
steps of a specification must have their subproof, as in CakePB. Third, in `def_order` the `aux`
line and the `reflexivity` section are optional, a missing reflexivity proof leaving only
trivially true goals; the kernel format requires both (§6.1). The remaining extensions, `del id`
and `rup` without hints, are described under **Steps**. So a proof accepted here need not be a
kernel proof.

**Variables.** Variable names follow VeriPB 3.0.2 (§3.3 of the documentation). An instance and an
output formula have OPB names (`Cslib.Logic.PL.VeriPB.Text.isOPBName`): at least two characters,
an ASCII letter or `_` first, then letters, digits and `_ [ ] { } ^ -`, the rule of
`veripb-parser` 0.1.2, which VeriPB 3.0.2 locks. A proof may also name the auxiliary variables of
an order `$a`, a `$` followed by those characters (§5.3; `Cslib.Logic.PL.VeriPB.Text.isName`), as
VeriPB's proof lexer does; the parser of instances rejects them, as VeriPB does (CakePB accepts
the constraint `1 $a >= 1` in an instance). A standard name `xN`, with `N ≥ 1` written without
leading zeros, is the variable `N - 1`, as in `Cslib.Logic.PL.Literal.ofDIMACS`, so a DIMACS
variable and its name in the proof agree; `x01` is another name, as in VeriPB. The other names of
an instance are numbered after its largest standard name, in order of first appearance
(`Cslib.Logic.PL.VeriPB.Text.opbNames`), so an instance with standard names only has the variables
`N - 1`, and one without them is numbered as VeriPB numbers it. The proof and the output text
share these names: the names they add, the auxiliary variables and the keywords of the proof
included, are the next variables, in order of first appearance
(`Cslib.Logic.PL.VeriPB.Text.proofNames`). So a name the instance does not mention is always a
fresh variable, as in VeriPB, where every rule may introduce one; the checker tests freshness
where the rule requires it (witnesses, `fresh_right`, `fresh_aux_1`, `fresh_aux_2`). How the
variables are numbered does not matter for the conclusions: read through the names, they hold
for every assignment of the names (`Cslib.Logic.PL.VeriPB.Instance.valuesVia_eq`,
`Cslib.Logic.PL.VeriPB.Text.Names.name_injective`).

**Steps.** The kernel steps `pol`, `rup` with hints, `pbc` with its subproof, `red` and `dom` with a
witness and an optional subproof of `proofgoal` blocks (labelled `#k` or by constraint numbers) and
the scopes `scope leq` and `scope geq`, each closed by `end;`, `end scope;` or `end scope leq;`
(`geq`), the orders of `def_order` (a `vars` section with `left`, `right` and an `aux` line, which
the kernel format requires and is optional here, an optional `spec` section of `red` steps with
subproofs, a `def` section, a `transitivity` section with `fresh_right` variables, the `fresh_aux_1`
and `fresh_aux_2` variables if there are auxiliary variables, and a `proof`, an optional
`reflexivity` section; §5.3), `load_order` with and without literals, the order checks `eord_def`
and `eord_loaded` (§5.11.3), the solution-logging steps `sol`, `soli` and `solx` and the bound
`obji` (§5.8), the objective update `obju new` or `obju diff` with an objective in the OPB syntax,
an optional constant included, and an optional subproof of `proofgoal #1` and `#2` (§5.9), the
changes of the preserved set `preserved_add x : C` and `preserved_rm x : C` with an optional
subproof of `proofgoal #1` and `#2`, closed by `qed [preserved_add];` (`rm`) (§5.10), the check
`epreserved` (§5.11.4), `core id` (§5.1), `strengthening_to_core on` and `off` (§5.6), and the
deletions (§5.7.1): `deld` of derived constraints, the unchecked `delc` of core constraints, and the
checked `delc id : ω` of one core constraint, with an optional subproof. Orders, `dom`, deletion,
`core`, strengthening-to-core, solution logging, `obji`, `obju` and the preserved-set rules are
accepted only at top level, as the format requires. Two steps of the augmented format are also
accepted: `del id`, read as the untyped deletion `Cslib.Logic.PL.VeriPB.Step.del` (§5.7.2; a
deletion of a core constraint counts as unchecked), and `rup` without hints, read as
`Cslib.Logic.PL.VeriPB.Step.rupSearch`. The implication `ia C : j;`, which VeriPB's elaborator
writes in kernel proofs and CakePB checks as an implication by the constraint `j`, is read as
`rup C : ~ j;`: unit propagation from the negation of `C` and then `j`. That is sound, and accepts
every `ia` whose constraint `C` is a clause (coefficients and degree `1`), for which an implication
by `j` is exactly a conflict of `j` under the negation of `C`; for other constraints it may reject
an implication that CakePB accepts. Everything else (`pol` operations `c`, `m`, `n` and `-`,
relative constraint numbers, `i`, `ia` without a constraint number, `del spec`, levels, and the
conclusion `UNSAT` without an ID) is rejected.

**Output sections.** `Cslib.Logic.PL.VeriPB.Text.checkOPBOutput` takes the output formula of
`output g FILE;` as a third text, and checks the section with
`Cslib.Logic.PL.VeriPB.checkRedOutput`; `FILE` needs that text and `IMPLICIT` takes none.
`Cslib.Logic.PL.VeriPB.Text.checkOPB` takes no output text, so it accepts `NONE` and `IMPLICIT`
sections only.

**Soundness.** The checkers return the conclusion of an accepted proof. If it is `UNSAT`, the
input parses to a formula with no 0/1 solution
(`Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB`,
`Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS`); if `SAT`, to one with a solution
(`Cslib.Logic.PL.VeriPB.Text.exists_satisfies_of_checkOPB`,
`Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS`), the stated assignment of `SAT : ρ`
being one (`Cslib.Logic.PL.VeriPB.Text.holds_of_checkOPB_sat`); if `BOUNDS lb : q ub`, to an
instance with an objective `f` whose every solution has value at least `lb` and, for a finite
`ub`, some solution has value at most `ub` (`Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB`);
if `ENUMERATION_PARTIAL n` or `ENUMERATION_COMPLETE n : q`, to an instance with a preserved set
whose solutions have at least, or exactly, `n` distinct projections to it
(`Cslib.Logic.PL.VeriPB.Text.le_encard_of_checkOPB_enumPartial`,
`Cslib.Logic.PL.VeriPB.Text.encard_eq_of_checkOPB_enumComplete`). An enumeration needs a
`preserved:` line, even for `n = 0`, which VeriPB 3.0.2 and CakePB accept without one. `NONE`
claims nothing. An accepted output section gives its guarantee between the instance and the
output formula (`Cslib.Logic.PL.VeriPB.Text.semOutput_of_checkOPBOutput`).
This is a guarantee about the text and the formula the parser returns: the parsers are trusted
to read the files as intended, and nothing is said about compiled code. It is smaller than the
end-to-end theorem of CakePB (§6.2 of the VeriPB/CakePB documentation, 22 June 2026 edition),
which also covers the execution of its compiled machine code and the parsing of DIMACS input.
For an instance or formula built in Lean, the parsers drop out: they read back the text that
`Cslib.Logic.PL.VeriPB.Text.printOPB` and `Cslib.Logic.PL.CNF.toDIMACS` print, and the soundness
theorems in `CslibFrontier.Logics.Propositional.PseudoBoolean.Print` conclude about the Lean
value itself (`Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB_printOPB` and others).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Text.parseOPB`, `Cslib.Logic.PL.VeriPB.Text.parseOPBWith`,
  `Cslib.Logic.PL.VeriPB.Text.parseDIMACS`: instances, with their own names or given ones, and
  formulas.
* `Cslib.Logic.PL.VeriPB.Text.parseProof`: proofs in the supported fragment.
* `Cslib.Logic.PL.VeriPB.Text.checkOPB`, `Cslib.Logic.PL.VeriPB.Text.checkOPBOutput`,
  `Cslib.Logic.PL.VeriPB.Text.checkDIMACS`: the checkers.
* `Cslib.Logic.PL.VeriPB.Text.isOPBName`, `Cslib.Logic.PL.VeriPB.Text.isName`: the variable
  names of an instance, and those of a proof, which may also name auxiliary variables `$a`.
* `Cslib.Logic.PL.VeriPB.Text.Names`, `Cslib.Logic.PL.VeriPB.Text.opbNames`,
  `Cslib.Logic.PL.VeriPB.Text.proofNames`: variable names, those of an OPB text, and those of a
  proof and its output text.

## Main results

* `Cslib.Logic.PL.VeriPB.Text.Names.name_injective`, `Cslib.Logic.PL.VeriPB.Text.Names.var?_name`,
  `Cslib.Logic.PL.VeriPB.Text.opbNames_wf`: distinct variables have distinct names, which read
  back as the variables.

* `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB`,
  `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS`: soundness of `UNSAT`.
* `Cslib.Logic.PL.VeriPB.Text.exists_satisfies_of_checkOPB`,
  `Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS`: soundness of `SAT`.
* `Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB`: soundness of `BOUNDS`.
* `Cslib.Logic.PL.VeriPB.Text.le_encard_of_checkOPB_enumPartial`,
  `Cslib.Logic.PL.VeriPB.Text.encard_eq_of_checkOPB_enumComplete`: soundness of `ENUMERATION`.
* `Cslib.Logic.PL.VeriPB.Text.semOutput_of_checkOPBOutput`: soundness of output sections;
  `Cslib.Logic.PL.VeriPB.Text.exists_checkRed_of_checkOPBOutput`: the conclusion of a proof with
  an output section is that of an accepted proof. The soundness theorems of the conclusions take
  `checkOPBOutput` with any output text, `checkOPB` being the case of none.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Text

/-! ### Tokens -/

/-! The lexer works on the characters of a text, without `String.splitOn`, `String.toNat?` and
the other `String` operations that the kernel cannot evaluate, so that `decide` can check concrete
texts. It is one tail-recursive pass over the characters (`lexChars`, `linesAux`), linear in the
text; the structurally recursive specification (`splitChars`, `lexLine`) computes the same tokens
(`tokens_eq_spec`, `lines_eq_spec`). -/

/-- The pieces of a list of characters between the characters satisfying `p`. -/
def splitChars (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if p c then [] :: splitChars p cs
    else
      match splitChars p cs with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- The token in progress, its characters reversed, if any. -/
private def flushToken (cur : List Char) : List String :=
  if cur.isEmpty then [] else [String.ofList cur.reverse]

/-- The tokens of a line without its comment: whitespace-separated, with `;` a token of its own.
`cur` is the token in progress, reversed. -/
private def lexLine : List Char → List Char → List String
  | [], cur => flushToken cur
  | c :: cs, cur =>
    if c.isWhitespace then flushToken cur ++ lexLine cs []
    else if c == ';' then flushToken cur ++ ";" :: lexLine cs []
    else lexLine cs (c :: cur)

/-- The token in progress `cur`, reversed, if any, onto the tokens `acc`, reversed. -/
private def flushTo (cur : List Char) (acc : List String) : List String :=
  if cur.isEmpty then acc else String.ofList cur.reverse :: acc

/-- The tokens of the characters `cs`, in one pass: `cur` is the token in progress, reversed,
`com` says that the rest of the line is a comment, and `acc` holds the tokens so far, reversed. -/
private def lexChars : List Char → List Char → Bool → List String → List String
  | [], cur, _, acc => (flushTo cur acc).reverse
  | c :: cs, cur, com, acc =>
    if c == '\n' then lexChars cs [] false (flushTo cur acc)
    else if com then lexChars cs [] true acc
    else if c == '%' then lexChars cs [] true (flushTo cur acc)
    else if c.isWhitespace then lexChars cs [] false (flushTo cur acc)
    else if c == ';' then lexChars cs [] false (";" :: flushTo cur acc)
    else lexChars cs (c :: cur) false acc

/-- The tokens of a text: whitespace-separated, with `;` a token of its own and everything after
`%` on a line a comment. -/
def tokens (s : String) : List String := lexChars s.toList [] false []

/-- The lines of the characters `cs`, in one pass: `cur` is the line in progress, reversed, and
`acc` holds the lines so far, reversed. -/
private def linesAux : List Char → List Char → List String → List String
  | [], cur, acc => (String.ofList cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
    if c == '\n' then linesAux cs [] (String.ofList cur.reverse :: acc)
    else linesAux cs (c :: cur) acc

/-- The lines of a text. -/
private def lines (s : String) : List String := linesAux s.toList [] []

private theorem splitChars_ne_nil (p : Char → Bool) (cs : List Char) : splitChars p cs ≠ [] := by
  cases cs with
  | nil => simp [splitChars]
  | cons c cs =>
    unfold splitChars
    split
    · simp
    · split <;> simp

private theorem linesAux_eq (cs cur : List Char) (acc : List String) :
    linesAux cs cur acc = acc.reverse ++
      ((splitChars (· == '\n') cs).modifyHead (cur.reverse ++ ·)).map String.ofList := by
  induction cs generalizing cur acc with
  | nil => simp [linesAux, splitChars]
  | cons c cs ih =>
    unfold linesAux splitChars
    by_cases hc : c = '\n'
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte, ih, List.reverse_nil, List.nil_append,
        List.reverse_cons, List.append_assoc, List.cons_append]
      cases splitChars (· == '\n') cs <;> simp
    · have hc' : (c == '\n') = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte, ih]
      have := splitChars_ne_nil (· == '\n') cs
      rcases h : splitChars (· == '\n') cs with _ | ⟨l, ls⟩
      · exact absurd h this
      · simp

private theorem lines_eq_spec (s : String) :
    lines s = (splitChars (· == '\n') s.toList).map String.ofList := by
  rw [lines, linesAux_eq]
  have := splitChars_ne_nil (· == '\n') s.toList
  rcases h : splitChars (· == '\n') s.toList with _ | ⟨l, ls⟩
  · exact absurd h this
  · simp

/-- The tokens of the lines of `ls`, comments removed. -/
private def lineTokens (ls : List (List Char)) : List String :=
  ls.flatMap fun line => lexLine (line.takeWhile (· != '%')) []

private theorem reverse_flushTo (cur : List Char) (acc : List String) :
    (flushTo cur acc).reverse = acc.reverse ++ flushToken cur := by
  unfold flushTo flushToken
  split <;> simp

private theorem lexChars_eq (cs cur : List Char) (acc : List String) :
    lexChars cs cur false acc = acc.reverse ++
        (match splitChars (· == '\n') cs with
          | [] => []
          | l :: ls => lexLine (l.takeWhile (· != '%')) cur ++ lineTokens ls) ∧
      lexChars cs [] true acc = acc.reverse ++
        (match splitChars (· == '\n') cs with
          | [] => []
          | _ :: ls => lineTokens ls) := by
  induction cs generalizing cur acc with
  | nil => simp [lexChars, splitChars, lexLine, reverse_flushTo, lineTokens, flushToken]
  | cons c cs ih =>
    have hne := splitChars_ne_nil (· == '\n') cs
    by_cases hn : c = '\n'
    · subst hn
      have h₀ : ∀ acc, lexChars cs [] false acc = acc.reverse ++ lineTokens
          (splitChars (· == '\n') cs) := fun acc => by
        rw [(ih [] acc).1]
        rcases h : splitChars (· == '\n') cs with _ | ⟨l, ls⟩
        · exact absurd h hne
        · simp [lineTokens]
      refine ⟨?_, ?_⟩
      · simp only [lexChars, splitChars, beq_self_eq_true, ↓reduceIte, h₀, reverse_flushTo,
          List.takeWhile_nil, lexLine]
        simp [lineTokens, List.append_assoc]
      · have := h₀ acc
        simp only [lexChars, splitChars, beq_self_eq_true, ↓reduceIte, flushTo, List.isEmpty_nil]
        simpa [lineTokens] using this
    · have hn' : (c == '\n') = false := by simpa using hn
      rcases h : splitChars (· == '\n') cs with _ | ⟨l, ls⟩
      · exact absurd h hne
      have hsplit : splitChars (· == '\n') (c :: cs) = (c :: l) :: ls := by
        simp [splitChars, hn', h]
      rw [hsplit]
      refine ⟨?_, ?_⟩
      · simp only [lexChars, hn', Bool.false_eq_true, ↓reduceIte]
        by_cases hp : c = '%'
        · subst hp
          simp [(ih [] _).2, h, reverse_flushTo, lexLine]
        · have hp' : (c == '%') = false := by simpa using hp
          have htw : (c :: l).takeWhile (· != '%') = c :: l.takeWhile (· != '%') := by
            simp [hp]
          simp only [hp', Bool.false_eq_true, ↓reduceIte, htw, lexLine]
          by_cases hw : c.isWhitespace
          · simp [hw, (ih [] _).1, h, reverse_flushTo]
          · by_cases hs : c = ';'
            · subst hs
              simp [hw, (ih [] _).1, h, reverse_flushTo]
            · have hs' : (c == ';') = false := by simpa using hs
              simp [hw, hs', (ih _ _).1, h]
      · simp only [lexChars, hn', Bool.false_eq_true, ↓reduceIte, (ih [] acc).2, h]

private theorem tokens_eq_spec (s : String) :
    tokens s = lineTokens (splitChars (· == '\n') s.toList) := by
  rw [tokens, (lexChars_eq _ [] []).1]
  have := splitChars_ne_nil (· == '\n') s.toList
  rcases h : splitChars (· == '\n') s.toList with _ | ⟨l, ls⟩
  · exact absurd h this
  · simp [lineTokens]

/-- A natural number: one or more decimal digits (`Nat.ofDecimal?`). -/
private def nat? (t : String) : Option ℕ := Nat.ofDecimal? t.toList

/-- The rest of `t` after its first character, if that is `c`. -/
private def dropChar? (c : Char) (t : String) : Option String :=
  match t.toList with
  | d :: cs => if d == c then some (String.ofList cs) else none
  | [] => none

/-- `t` starts with the character `c`. -/
private def startsWithChar (c : Char) (t : String) : Bool := t.toList.head? == some c

/-- An integer, with an optional sign `+` or `-`. -/
def int? (t : String) : Option ℤ :=
  match dropChar? '+' t, dropChar? '-' t with
  | some r, _ => (nat? r).map Int.ofNat
  | none, some r => (nat? r).map fun n => -(n : ℤ)
  | none, none => (nat? t).map Int.ofNat

/-- A positive constraint number. -/
def id? (t : String) : Option ℕ :=
  match nat? t with
  | some (n + 1) => some (n + 1)
  | _ => none

/-- The number `N - 1` of a standard variable name `xN`, `N ≥ 1` written without leading zeros. A
name such as `x01` is not standard: VeriPB tells it apart from `x1`. -/
def stdVar? (t : String) : Option ℕ :=
  match dropChar? 'x' t with
  | some r =>
    match nat? r with
    | some (n + 1) => if Nat.toDecimal (n + 1) == r.toList then some n else none
    | _ => none
  | none => none

/-- A character that may follow the first one of a variable name: an ASCII letter or digit, or one
of `_ [ ] { } ^ -`. -/
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '[' || c == ']' || c == '{' || c == '}' || c == '^' || c == '-'

/-- **An OPB variable name** (§3.3 of the documentation, as VeriPB 3.0.2 reads an instance): at
least two characters, the first an ASCII letter or `_`, the others name characters
(`Cslib.Logic.PL.VeriPB.Text.isNameChar`). This is the rule
`[a-zA-Z_][_a-zA-Z0-9\-\^\[\]\{\}]+` of `OPBToken::Var` in `opb_token.rs` of `veripb-parser`
0.1.2, the version VeriPB 3.0.2 locks. VeriPB also allows `-` after the first character, which
the documentation does not list. -/
def isOPBName (t : String) : Bool :=
  match t.toList with
  | c :: d :: cs => (c.isAlpha || c == '_') && (d :: cs).all isNameChar
  | _ => false

/-- **A variable name of a proof**: an OPB name (`Cslib.Logic.PL.VeriPB.Text.isOPBName`), or the
name `$a` of an auxiliary variable of an order (§5.3), a `$` followed by name characters. VeriPB
3.0.2 starts an identifier of a proof so (`is_start_of_identifier_symbol` and
`is_identifier_symbol` in its `src/parser/lexer.rs`); an instance and an output formula have OPB
names only. -/
def isName (t : String) : Bool :=
  match t.toList with
  | c :: d :: cs => (c.isAlpha || c == '_' || c == '$') && (d :: cs).all isNameChar
  | _ => false

/-- An OPB name is a name. -/
theorem isName_of_isOPBName {t : String} (h : isOPBName t = true) : isName t = true := by
  unfold isOPBName at h
  unfold isName
  split at h
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨.inl h.1, h.2⟩
  · cases h

/-- **The variable names of an instance and its proof.** A standard name `xN` with `N - 1` below
`base` is the variable `N - 1`, as in `Cslib.Logic.PL.Literal.ofDIMACS`; the other names are the
variables `base`, `base + 1`, …, in the order of `others`. -/
structure Names where
  /-- The other names, in order of first appearance. -/
  others : List String
  /-- The standard names `xN` with `N - 1` below `base` are the variables below `base`. -/
  base : ℕ
  deriving DecidableEq, Repr

/-- The number of a variable name. -/
def Names.var? (N : Names) (t : String) : Option ℕ :=
  match stdVar? t with
  | some v => if v < N.base then some v else (N.others.idxOf? t).map (N.base + ·)
  | none => (N.others.idxOf? t).map (N.base + ·)

/-- The first variable after the named ones. -/
def Names.next (N : Names) : ℕ := N.base + N.others.length

/-- The characters of the name of the variable `v`: `x(v + 1)` below `base`, the name of `others`
from there, and `#v`, not a name, from `Cslib.Logic.PL.VeriPB.Text.Names.next` on. -/
def Names.nameChars (N : Names) (v : ℕ) : List Char :=
  if v < N.base then 'x' :: Nat.toDecimal (v + 1)
  else
    match N.others[v - N.base]? with
    | some s => s.toList
    | none => '#' :: Nat.toDecimal v

/-- **The name of the variable `v`** (`Cslib.Logic.PL.VeriPB.Text.Names.nameChars`). -/
def Names.name (N : Names) (v : ℕ) : String := String.ofList (N.nameChars v)

/-- **Well-formed names**: the other names are distinct names, and none is a standard name below
`base`. Then distinct variables have distinct names
(`Cslib.Logic.PL.VeriPB.Text.Names.name_injective`), and the name of a variable below
`Cslib.Logic.PL.VeriPB.Text.Names.next` reads back as that variable
(`Cslib.Logic.PL.VeriPB.Text.Names.var?_name`). -/
structure Names.WF (N : Names) : Prop where
  /-- The other names are distinct. -/
  nodup : N.others.Nodup
  /-- The other names are names. -/
  name_ok : ∀ s ∈ N.others, isName s = true
  /-- No other name is a standard name below `base`. -/
  base_le : ∀ s ∈ N.others, ∀ v, stdVar? s = some v → N.base ≤ v

instance (N : Names) : Decidable N.WF :=
  decidable_of_iff (N.others.Nodup ∧ (∀ s ∈ N.others, isName s = true) ∧
      ∀ s ∈ N.others, ∀ v ∈ stdVar? s, N.base ≤ v)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- `N` extends `M`: the same base, and the other names of `M` first. Then the variables named by
`M` have the same names in `N`. -/
def Names.Extends (N M : Names) : Prop := N.base = M.base ∧ M.others <+: N.others

/-- A literal token `x` or `~x`. -/
def Names.lit? (N : Names) (t : String) : Option (Literal ℕ) :=
  match dropChar? '~' t with
  | some r => (N.var? r).map ((·, false))
  | none => (N.var? t).map ((·, true))

/-- A token without the `~` of a negative literal. -/
def bareName (t : String) : String := (dropChar? '~' t).getD t

/-- A literal token `x` or `~x` of an instance, with `x` an OPB name
(`Cslib.Logic.PL.VeriPB.Text.isOPBName`): not the name `$a` of an auxiliary variable. -/
def Names.opbLit? (N : Names) (t : String) : Option (Literal ℕ) :=
  if isOPBName (bareName t) then N.lit? t else none

/-- The elements of `l` not in `acc`, after `acc`, each once, in order of first appearance. -/
private def addNew (acc : List String) : List String → List String
  | [] => acc
  | t :: ts => addNew (if acc.contains t then acc else acc ++ [t]) ts

/-- **The names `N` extended by the tokens `ts`**: the names of `ts` that `N` does not know are
the next variables, in order of first appearance. A standard name `xK` with `K - 1` at least
`N.base` is such a name. So a name of a proof that its formula does not mention is a fresh
variable. -/
def Names.extend (N : Names) (ts : List String) : Names :=
  ⟨addNew N.others ((ts.map bareName).filter fun t => isName t && (N.var? t).isNone), N.base⟩

/-- The token lines of an OPB text, without the comment lines (starting with `*`) and the empty
lines. -/
def opbTokenLines (s : String) : List (List String) :=
  ((lines s).map tokens).filter fun l =>
    match l.head? with
    | none => false
    | some t => !startsWithChar '*' t

/-- **The variable names of an OPB text**: the standard names `xN` are the variables `N - 1`, below
one more than the largest of them, and the other OPB names
(`Cslib.Logic.PL.VeriPB.Text.isOPBName`), in order of first appearance, the variables from there
on. A name `$a` of an auxiliary variable is not one of them. -/
def opbNames (s : String) : Names :=
  let ts := (opbTokenLines s).flatten.filter fun t => isOPBName (bareName t)
  (⟨[], ((ts.map bareName).filterMap stdVar?).foldr (fun v m => max (v + 1) m) 0⟩ : Names).extend
    ts

/-! #### Well-formed names -/

private theorem dropChar?_ofList (c d : Char) (ds : List Char) :
    dropChar? c (String.ofList (d :: ds)) = if d == c then some (String.ofList ds) else none := by
  rw [dropChar?, String.toList_ofList]

/-- The standard name `x(n + 1)` is the variable `n`. -/
theorem stdVar?_std (n : ℕ) : stdVar? (String.ofList ('x' :: Nat.toDecimal (n + 1))) = some n := by
  rw [stdVar?, dropChar?_ofList]
  simp [nat?, String.toList_ofList, Nat.ofDecimal?_toDecimal]

private theorem mem_addNew {acc l : List String} {t : String} :
    t ∈ addNew acc l ↔ t ∈ acc ∨ t ∈ l := by
  induction l generalizing acc with
  | nil => simp [addNew]
  | cons u l ih =>
    rw [addNew, ih]
    split
    · rename_i hu
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl (List.contains_iff_mem.1 hu)
        · exact .inr h
    · simp only [List.mem_append, List.mem_cons]
      tauto

private theorem nodup_addNew {acc : List String} (h : acc.Nodup) (l : List String) :
    (addNew acc l).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons u l ih =>
    rw [addNew]
    split
    · exact ih h
    · rename_i hu
      exact ih (List.nodup_append.2 ⟨h, List.nodup_singleton u, fun a ha b hb hab =>
        hu (List.contains_iff_mem.2 (by simp_all))⟩)

private theorem prefix_addNew (acc l : List String) : acc <+: addNew acc l := by
  induction l generalizing acc with
  | nil => exact List.prefix_refl _
  | cons u l ih =>
    rw [addNew]
    split
    · exact ih acc
    · exact (List.prefix_append _ _).trans (ih _)

/-- Extending well-formed names keeps them well formed. -/
theorem Names.WF.extend {N : Names} (hN : N.WF) (ts : List String) : (N.extend ts).WF where
  nodup := nodup_addNew hN.nodup _
  name_ok s hs := by
    rcases mem_addNew.1 hs with hs | hs
    · exact hN.name_ok s hs
    · exact (Bool.and_eq_true _ _ ▸ (List.mem_filter.1 hs).2).1
  base_le s hs v hv := by
    rcases mem_addNew.1 hs with hs | hs
    · exact hN.base_le s hs v hv
    · have h := (Bool.and_eq_true _ _ ▸ (List.mem_filter.1 hs).2).2
      simp only [Names.var?, hv, Option.isNone_iff_eq_none] at h
      dsimp only [Names.extend]
      by_contra hlt
      simp [not_le.1 hlt] at h

/-- Extended names extend. -/
theorem Names.extends_extend (N : Names) (ts : List String) : (N.extend ts).Extends N :=
  ⟨rfl, prefix_addNew _ _⟩

/-- **The names of an OPB text are well formed.** -/
theorem opbNames_wf (s : String) : (opbNames s).WF :=
  Names.WF.extend ⟨List.nodup_nil, by simp, by simp⟩ _

/-- **The name of a variable below `next` reads back as that variable.** -/
theorem Names.var?_name {N : Names} (hN : N.WF) {v : ℕ} (hv : v < N.next) :
    N.var? (N.name v) = some v := by
  unfold Names.name Names.nameChars
  split
  · rename_i hlt
    obtain ⟨n, rfl⟩ : ∃ n, v = n := ⟨v, rfl⟩
    rw [Names.var?, stdVar?_std]
    simp [hlt]
  · rename_i hle
    have hi : v - N.base < N.others.length := by unfold Names.next at hv; omega
    rw [List.getElem?_eq_getElem hi]
    simp only [String.ofList_toList]
    have hidx : N.others.idxOf? N.others[v - N.base] = some (v - N.base) := by
      rw [List.idxOf?_eq_some_iff]
      exact ⟨hi, rfl, fun j hj h => by
        have := (hN.nodup.getElem_inj_iff (i := j) (j := v - N.base)).1 h
        omega⟩
    have hmap : (N.others.idxOf? N.others[v - N.base]).map (N.base + ·) = some v := by
      rw [hidx]; simp; omega
    unfold Names.var?
    split
    · rename_i u hu
      have := hN.base_le _ (List.getElem_mem hi) u hu
      simp [show ¬ u < N.base by omega, hmap]
    · exact hmap

/-- A standard name is written without leading zeros: it is `x(n + 1)` for its variable `n`. -/
theorem eq_of_stdVar? {t : String} {n : ℕ} (h : stdVar? t = some n) :
    t = String.ofList ('x' :: Nat.toDecimal (n + 1)) := by
  unfold stdVar? at h
  split at h
  · rename_i r hr
    split at h
    · rename_i m _
      split at h
      · rename_i heq
        cases h
        unfold dropChar? at hr
        split at hr
        · rename_i d cs hcs
          split at hr
          · rename_i hd
            cases hr
            rw [beq_iff_eq] at hd heq
            subst hd
            rw [String.toList_ofList] at heq
            rw [← heq] at hcs
            rw [← hcs, String.ofList_toList]
          · cases hr
        · cases hr
      · cases h
    · cases h
  · cases h

/-- **A name read as a variable is the name of that variable.** -/
theorem Names.name_of_var? {N : Names} {t : String} {w : ℕ} (h : N.var? t = some w) :
    N.name w = t := by
  have hlook : ∀ {w}, (N.others.idxOf? t).map (N.base + ·) = some w → N.name w = t := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.1 hi
    simp only [Names.name, Names.nameChars, show ¬ N.base + i < N.base by omega, ↓reduceIte,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt, hget, String.ofList_toList]
  unfold Names.var? at h
  split at h
  · rename_i v hv
    split at h
    · rename_i hlt
      cases h
      simp only [Names.name, Names.nameChars, hlt, ↓reduceIte]
      exact (eq_of_stdVar? hv).symm
    · exact hlook h
  · exact hlook h

/-- Distinct variables below `next` have distinct names. -/
theorem Names.name_injOn {N : Names} (hN : N.WF) : Set.InjOn N.name {v | v < N.next} :=
  fun _ hv _ hw h => Option.some.inj ((var?_name hN hv).symm.trans (h ▸ var?_name hN hw))

private theorem isNameChar_of_isDigit {c : Char} (h : c.isDigit = true) : isNameChar c = true := by
  simp [isNameChar, Char.isAlphanum, h]

/-- A standard name is an OPB name. -/
private theorem isOPBName_std (n : ℕ) :
    isOPBName (String.ofList ('x' :: Nat.toDecimal (n + 1))) = true := by
  obtain ⟨d, ds, h, -⟩ := Nat.exists_toDecimal_eq_cons (n + 1)
  rw [h, isOPBName, String.toList_ofList]
  simp only [show ('x' : Char).isAlpha = true by decide, Bool.true_or, Bool.true_and,
    List.all_eq_true]
  intro c hc
  exact isNameChar_of_isDigit (Nat.isDigit_of_mem_toDecimal (h ▸ hc))

/-- The name of a variable below `next` is its standard name or one of the other names. -/
private theorem Names.name_eq_or_mem {N : Names} {v : ℕ} (hv : v < N.next) :
    N.name v = String.ofList ('x' :: Nat.toDecimal (v + 1)) ∨ N.name v ∈ N.others := by
  unfold Names.name Names.nameChars
  split
  · exact .inl rfl
  · have hi : v - N.base < N.others.length := by unfold Names.next at hv; omega
    rw [List.getElem?_eq_getElem hi]
    simp only [String.ofList_toList]
    exact .inr (List.getElem_mem hi)

/-- **The name of a variable below `next` is a name.** -/
theorem Names.isName_name {N : Names} (hN : N.WF) {v : ℕ} (hv : v < N.next) :
    isName (N.name v) = true := by
  rcases N.name_eq_or_mem hv with h | h
  · exact h ▸ isName_of_isOPBName (isOPBName_std v)
  · exact hN.name_ok _ h

/-- **The name of a variable below `next` is an OPB name** when the other names are. -/
theorem Names.isOPBName_name {N : Names} (hN : ∀ s ∈ N.others, isOPBName s = true) {v : ℕ}
    (hv : v < N.next) : isOPBName (N.name v) = true := by
  rcases N.name_eq_or_mem hv with h | h
  · exact h ▸ isOPBName_std v
  · exact hN _ h

private theorem nameChars_of_le {N : Names} {v : ℕ} (hv : N.next ≤ v) :
    N.nameChars v = '#' :: Nat.toDecimal v := by
  unfold Names.nameChars Names.next at *
  simp only [show ¬ v < N.base by omega, ↓reduceIte]
  rw [List.getElem?_eq_none (by omega)]

/-- **Distinct variables have distinct names**, for well-formed names: from `next` on, the
variable `v` is named `#v`, which is not a name. -/
theorem Names.name_injective {N : Names} (hN : N.WF) : Function.Injective N.name := by
  have hfar : ∀ {v w}, v < N.next → N.next ≤ w → N.name v ≠ N.name w := @fun v w hv hw h => by
    have := Names.isName_name hN hv
    rw [h, Names.name, nameChars_of_le hw, isName, String.toList_ofList] at this
    obtain ⟨d, ds, hd, -⟩ := Nat.exists_toDecimal_eq_cons w
    rw [hd] at this
    simp at this
  intro v w h
  rcases lt_or_ge v N.next with hv | hv <;> rcases lt_or_ge w N.next with hw | hw
  · exact Names.name_injOn hN hv hw h
  · exact absurd h (hfar hv hw)
  · exact absurd h.symm (hfar hw hv)
  · have h' := congrArg String.toList h
    simp only [Names.name, String.toList_ofList, nameChars_of_le hv, nameChars_of_le hw,
      List.cons.injEq, true_and] at h'
    have := congrArg Nat.ofDecimal? h'
    simpa [Nat.ofDecimal?_toDecimal] using this

/-- A name read as a variable is read below `next`. -/
theorem Names.lt_next_of_var? {N : Names} {t : String} {w : ℕ} (h : N.var? t = some w) :
    w < N.next := by
  have hlook : ∀ {w}, (N.others.idxOf? t).map (N.base + ·) = some w → w < N.next := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hw
    have := (List.idxOf?_eq_some_iff.1 hi).1
    unfold Names.next
    omega
  unfold Names.var? at h
  split at h
  · split at h
    · cases h; unfold Names.next; omega
    · exact hlook h
  · exact hlook h

/-- Names that extend `M` name the variables below `M.next` as `M` does. -/
theorem Names.Extends.name_eq {N M : Names} (h : N.Extends M) {v : ℕ} (hv : v < M.next) :
    N.name v = M.name v := by
  obtain ⟨hb, l, hl⟩ := h
  unfold Names.name Names.nameChars
  rw [hb]
  split
  · rfl
  · have hi : v - M.base < M.others.length := by unfold Names.next at hv; omega
    rw [← hl, List.getElem?_append_left hi]

/-! ### Constraints -/

/-- The terms `a ℓ` of a constraint or an objective, up to the relation, `;` or `:`, as an integer
linear form and a constant: that contributed by negative literals (`a ¬x = a - a x`) and, in an
objective, a final constant term, with the literals read by `lit` (`Names.lit?` in a proof,
`Names.opbLit?` in an instance). A constraint never ends in `;` or `:` before its relation, so
`constr` still rejects a constant there. -/
private def terms (lit : String → Option (Literal ℕ)) :
    List String → List (ℕ × ℤ) → ℤ → Option (List (ℕ × ℤ) × ℤ × List String)
  | [], _, _ => none
  | t :: ts, L, k =>
    if t == ">=" || t == "<=" || t == "=" || t == ";" || t == ":" then some (L, k, t :: ts)
    else
      match int? t with
      | some a =>
        -- A coefficient and a literal; a coefficient before `;` or `:` is the constant of an
        -- objective.
        match ts with
        | u :: rest =>
          if u == ";" || u == ":" then some (L, k + a, u :: rest)
          else
            match lit u with
            | some (v, true) => terms lit rest (PBConstr.insertCoeff v a L) k
            | some (v, false) => terms lit rest (PBConstr.insertCoeff v (-a) L) (k + a)
            | none => none
        | [] => none
      | none =>
        -- A literal with coefficient `1`.
        match lit t with
        | some (v, true) => terms lit ts (PBConstr.insertCoeff v 1 L) k
        | some (v, false) => terms lit ts (PBConstr.insertCoeff v (-1) L) (k + 1)
        | none => none

/-- A constraint `∑ aᵢ ℓᵢ ⋈ A`, its literals read by `lit`: one or two constraints `≥` (`=` gives
two), and the rest. -/
private def constr (lit : String → Option (Literal ℕ)) (ts : List String) :
    Option (List PBConstr × List String) :=
  match terms lit ts [] 0 with
  | some (L, k, rel :: d :: rest) =>
    match int? d with
    | none => none
    | some A =>
      let ge := PBConstr.fromLinear L (A - k)
      let le := PBConstr.fromLinear (L.map fun e => (e.1, -e.2)) (k - A)
      if rel == ">=" then some ([ge], rest)
      else if rel == "<=" then some ([le], rest)
      else if rel == "=" then some ([ge, le], rest)
      else none
  | _ => none

/-- A single constraint `∑ aᵢ ℓᵢ >= A`, as in proof steps. -/
private def geq (N : Names) (ts : List String) : Option (PBConstr × List String) :=
  match ts.head? with
  | none => none
  | some _ =>
    match constr N.lit? ts with
    | some ([c], rest) => some (c, rest)
    | _ => none

/-! ### Formulas -/

/-- The constraints of OPB lines, given as token lists, with OPB names. -/
private def opbLines (N : Names) : List (List String) → Option (List PBConstr)
  | [] => some []
  | [] :: ls => opbLines N ls
  | (t :: ts) :: ls =>
    if startsWithChar '*' t then opbLines N ls
    else
      match constr N.opbLit? (t :: ts), opbLines N ls with
      | some (cs, [";"]), some F => some (cs ++ F)
      | _, _ => none

/-- An objective `∑ wᵢ ℓᵢ [k]` with an optional constant `k`, its literals read by `lit`, up to
`;` or `:`, and the rest from there: the OPB objective syntax, which `obju` reuses (§5.9). -/
private def objTerms (lit : String → Option (Literal ℕ)) (ts : List String) :
    Option (Objective × List String) :=
  match terms lit ts [] 0 with
  | some (L, k, t :: rest) => if t == ";" || t == ":" then some (⟨L, k⟩, t :: rest) else none
  | _ => none

/-- An objective line `min: ∑ wᵢ ℓᵢ [k];`, given its tokens after `min:`, with an optional
constant `k` and OPB names. -/
private def objective (N : Names) (ts : List String) : Option Objective :=
  match objTerms N.opbLit? ts with
  | some (f, [";"]) => some f
  | _ => none

/-- The variables of a `preserved:` line, up to `;`, with OPB names. -/
private def presVars (N : Names) : List String → Option (List ℕ)
  | [";"] => some []
  | t :: ts =>
    (if isOPBName t then N.var? t else none).bind fun v => (presVars N ts).map (v :: ·)
  | [] => none

/-- **An OPB instance with the names `N`** (`Cslib.Logic.PL.VeriPB.Instance`): comment lines
starting with `*`, an optional objective line `min: …;` and an optional preserved-set line
`preserved: …;`, in either order, before the constraints, and one constraint per line. Its
variables have OPB names (`Cslib.Logic.PL.VeriPB.Text.isOPBName`, read by
`Cslib.Logic.PL.VeriPB.Text.Names.opbLit?`), so a name `$a` of an auxiliary variable is
rejected even when `N` knows it. An input is read with its own names
(`Cslib.Logic.PL.VeriPB.Text.parseOPB`), an output formula with the names of its proof. -/
def parseOPBWith (N : Names) (s : String) : Option Instance :=
  match opbTokenLines s with
  | ("min:" :: ts) :: ("preserved:" :: ps) :: ls
  | ("preserved:" :: ps) :: ("min:" :: ts) :: ls =>
    (objective N ts).bind fun f => (presVars N ps).bind fun P =>
      (opbLines N ls).map (⟨·, some f, some P⟩)
  | ("min:" :: ts) :: ls =>
    (objective N ts).bind fun f => (opbLines N ls).map (⟨·, some f, none⟩)
  | ("preserved:" :: ps) :: ls =>
    (presVars N ps).bind fun P => (opbLines N ls).map (⟨·, none, some P⟩)
  | ls => (opbLines N ls).map (⟨·, none, none⟩)

/-- **An OPB instance** (`Cslib.Logic.PL.VeriPB.Text.parseOPBWith`), read with its own names
(`Cslib.Logic.PL.VeriPB.Text.opbNames`): the variable `v` is named
`(opbNames s).name v`. An instance with standard names `xN` only has the variables `N - 1`. -/
def parseOPB (s : String) : Option Instance := parseOPBWith (opbNames s) s

/-- An OPB instance is read with the names of its own text. -/
theorem parseOPB_eq_parseOPBWith (s : String) : parseOPB s = parseOPBWith (opbNames s) s := by
  unfold parseOPB; rfl

/-- The clauses of a DIMACS body over the variables `1, …, V`: nonzero integers of magnitude at
most `V`, each clause ended by `0`. -/
private def dimacsClauses (V : ℕ) : List String → List ℤ → Option (CNF ℕ)
  | [], [] => some []
  | [], _ :: _ => none
  | t :: ts, cur =>
    match int? t with
    | none => none
    | some 0 => (dimacsClauses V ts []).map (Clause.ofDIMACS cur.reverse :: ·)
    | some i => if i.natAbs ≤ V then dimacsClauses V ts (i :: cur) else none

/-- **A DIMACS CNF formula**: comment lines starting with `c`, the header `p cnf V C`, then
exactly `C` clauses over the variables `1, …, V`. -/
def parseDIMACS (s : String) : Option (CNF ℕ) :=
  let lines := (lines s).map tokens |>.filter fun l => l.head? != some "c"
  match lines with
  | ["p", "cnf", V, C] :: body =>
    match nat? V, nat? C with
    | some V, some C =>
      (dimacsClauses V body.flatten []).bind fun φ => if φ.length = C then some φ else none
    | _, _ => none
  | _ => none

/-! ### Proofs -/

/-- Constraint numbers and `~` up to `;`, as RUP hints. -/
private def hints : List String → Option (List Hint × List String)
  | ";" :: ts => some ([], ";" :: ts)
  | t :: ts =>
    (if t == "~" then some Hint.neg else (id? t).map Hint.id).bind fun h =>
      (hints ts).map fun (hs, rest) => (h :: hs, rest)
  | [] => none

/-- Constraint numbers up to `;`. -/
private def ids : List String → Option (List ℕ × List String)
  | ";" :: ts => some ([], ";" :: ts)
  | t :: ts => (id? t).bind fun n => (ids ts).map fun (ns, rest) => (n :: ns, rest)
  | [] => none

/-- Prepend an operation to the result of parsing the rest. -/
private def consOp (op : PolOp) :
    Option (List PolOp × List String) → Option (List PolOp × List String) :=
  Option.map fun (ops, rest) => (op :: ops, rest)

/-- The operations of a `pol` step, up to `;`. A number followed by `*` or `d` is the operand of
that operation, and a variable followed by `w` the variable of a weakening. -/
private def polOps (N : Names) : List String → Option (List PolOp × List String)
  | ";" :: ts => some ([], ";" :: ts)
  | "+" :: ts => consOp .add (polOps N ts)
  | "s" :: ts => consOp .sat (polOps N ts)
  | t :: "*" :: ts => (nat? t).bind fun k => consOp (.mul k) (polOps N ts)
  | t :: "d" :: ts => (nat? t).bind fun k => consOp (.div k) (polOps N ts)
  | t :: "w" :: ts =>
    match N.lit? t with
    | some (v, true) => consOp (.weaken v) (polOps N ts)
    | _ => none
  | t :: ts =>
    match id? t with
    | some n => consOp (.id n) (polOps N ts)
    | none => (N.lit? t).bind fun l => consOp (.lit l) (polOps N ts)
  | [] => none

/-- The pairs `x -> b` of a witness, up to `:` or `;`; `b` is `0`, `1` or a literal. -/
private def witness (N : Names) : List String → Option (Witness × List String)
  | x :: "->" :: b :: ts =>
    (N.var? x).bind fun v =>
      (if b == "0" then some WVal.zero else if b == "1" then some WVal.one
        else (N.lit? b).map WVal.lit).bind fun w =>
          (witness N ts).map fun (ω, rest) => ((v, w) :: ω, rest)
  | ts => some ([], ts)

/-- The end `qed [label] : id;` of a subproof, with the number of its contradiction. -/
private def qedId : List String → Option (ℕ × List String)
  | "qed" :: ":" :: n :: ";" :: ts => (id? n).map (·, ts)
  | "qed" :: _ :: ":" :: n :: ";" :: ts => (id? n).map (·, ts)
  | _ => none

/-- The end `qed [label] [: id];` of a `red` subproof. -/
private def qedOpt : List String → Option (Option ℕ × List String)
  | "qed" :: ";" :: ts => some (none, ts)
  | "qed" :: ":" :: n :: ";" :: ts => (id? n).map (some ·, ts)
  | "qed" :: _ :: ";" :: ts => some (none, ts)
  | "qed" :: _ :: ":" :: n :: ";" :: ts => (id? n).map (some ·, ts)
  | _ => none

/-- A proof goal label: `#k` or a constraint number. -/
private def goalId (t : String) : Option GoalId :=
  match dropChar? '#' t with
  | some k => (id? k).map .hash
  | none => (id? t).map .db

/-- The literals of a logged solution, up to `;`. -/
private def lits (N : Names) : List String → Option (List (Literal ℕ) × List String)
  | ";" :: ts => some ([], ";" :: ts)
  | t :: ts => (N.lit? t).bind fun l => (lits N ts).map fun (ls, rest) => (l :: ls, rest)
  | [] => none

mutual

/-- An implicational step: `pol`, `rup`, or `pbc` with its subproof; `fuel` bounds the
nesting. -/
private def step (N : Names) : ℕ → List String → Option (Step × List String)
  | 0, _ => none
  | _ + 1, "pol" :: ts =>
    match polOps N ts with
    | some (ops, ";" :: rest) => some (.pol ops, rest)
    | _ => none
  | _ + 1, "rup" :: ts =>
    match geq N ts with
    | some (c, ";" :: rest) => some (.rupSearch c, rest)
    | some (c, ":" :: rest) =>
      match hints rest with
      | some (hs, ";" :: rest) => some (.rup c hs, rest)
      | _ => none
    | _ => none
  | _ + 1, "ia" :: ts =>
    match geq N ts with
    | some (c, ":" :: n :: ";" :: rest) => (id? n).map fun j => (.rup c [.neg, .id j], rest)
    | _ => none
  | fuel + 1, "pbc" :: ts =>
    match geq N ts with
    | some (c, ":" :: "subproof" :: rest) =>
      match steps N fuel rest with
      | some (sub, rest) => (qedId rest).map fun (q, rest) => (.pbc c sub q, rest)
      | none => none
    | _ => none
  | _, _ => none

/-- Implicational steps, up to a `qed` or a `proofgoal`. -/
private def steps (N : Names) : ℕ → List String → Option (List Step × List String)
  | 0, _ => none
  | fuel + 1, ts =>
    match ts with
    | "qed" :: _ | "proofgoal" :: _ => some ([], ts)
    | _ =>
      match step N fuel ts with
      | some (s, rest) => (steps N fuel rest).map fun (ss, rest) => (s :: ss, rest)
      | none => none

end

/-- The end `end [scope [k]];` of a scope `scope k`, and the rest after it. -/
private def endScope (k : String) : List String → Option (List String)
  | "end" :: ";" :: ts | "end" :: "scope" :: ";" :: ts => some ts
  | "end" :: "scope" :: k' :: ";" :: ts => if k' == k then some ts else none
  | _ => none

/-- The items of a `red` subproof, up to its closing `qed` (or, in a scope, its `end`):
derivation steps, `proofgoal` blocks, and the scopes `scope leq` and `scope geq` (§5.4). -/
private def redItems (N : Names) : ℕ → List String → Option (List RedItem × List String)
  | 0, _ => none
  | fuel + 1, "proofgoal" :: g :: ts =>
    (goalId g).bind fun g =>
      match steps N fuel ts with
      | some (sub, rest) =>
        (qedId rest).bind fun (q, rest) =>
          (redItems N fuel rest).map fun (items, rest) => (.goal g sub q :: items, rest)
      | none => none
  | fuel + 1, "scope" :: k :: ts =>
    (if k == "leq" then some false else if k == "geq" then some true else none).bind fun geq =>
      (redItems N fuel ts).bind fun (inner, rest) =>
        (endScope k rest).bind fun rest =>
          (redItems N fuel rest).map fun (items, rest) => (.scope geq inner :: items, rest)
  | _ + 1, "qed" :: ts => some ([], "qed" :: ts)
  | _ + 1, "end" :: ts => some ([], "end" :: ts)
  | fuel + 1, ts =>
    match step N fuel ts with
    | some (s, rest) => (redItems N fuel rest).map fun (items, rest) => (.step s :: items, rest)
    | none => none

/-- Variables up to `;`, and the rest after it. -/
private def varList (N : Names) : List String → Option (List ℕ × List String)
  | ";" :: ts => some ([], ts)
  | t :: ts => (N.var? t).bind fun v => (varList N ts).map fun (vs, rest) => (v :: vs, rest)
  | [] => none

/-- The end `end [kw];` of a section, and the rest after it. -/
private def endOf (kw : String) : List String → Option (List String)
  | "end" :: ";" :: ts => some ts
  | "end" :: k :: ";" :: ts => if k == kw then some ts else none
  | _ => none

/-- The constraints of a `def` section, each ended by `;`, up to its `end`. -/
private def defConstrs (N : Names) : ℕ → List String → Option (List PBConstr × List String)
  | 0, _ => none
  | _ + 1, "end" :: ts => some ([], "end" :: ts)
  | fuel + 1, ts =>
    match geq N ts with
    | some (c, ";" :: rest) => (defConstrs N fuel rest).map fun (cs, rest) => (c :: cs, rest)
    | _ => none

/-- A `proof … qed [proof] [: id];` block of a transitivity or reflexivity proof. -/
private def orderProof (N : Names) (fuel : ℕ) : List String → Option (OrderProof × List String)
  | "proof" :: ts =>
    (redItems N fuel ts).bind fun (items, rest) =>
      (qedOpt rest).map fun (q, rest) => (⟨items, q⟩, rest)
  | _ => none

/-- The witness and optional subproof after the first `:` of `red`, `dom` and a checked `delc`:
`ω;`, or `ω : subproof … qed [label] [: n];`, with the subproof's items and closing
contradiction. -/
private def witnessTail (N : Names) (fuel : ℕ) (ts : List String) :
    Option ((Witness × Option (List RedItem) × Option ℕ) × List String) :=
  match witness N ts with
  | some (ω, ";" :: rest) => some ((ω, none, none), rest)
  | some (ω, ":" :: "subproof" :: rest) =>
    (redItems N fuel rest).bind fun (items, rest) =>
      (qedOpt rest).map fun (q, rest) => ((ω, some items, q), rest)
  | _ => none

/-- The optional subproof after the constraint or objective of `obju`, `preserved_add` and
`preserved_rm`: `;`, or `: subproof … qed [label];`, with no closing contradiction. -/
private def subproofTail (label : String) (N : Names) (fuel : ℕ) :
    List String → Option (Option (List RedItem) × List String)
  | ";" :: rest => some (none, rest)
  | ":" :: "subproof" :: rest =>
    (redItems N fuel rest).bind fun (items, rest) =>
      match rest with
      | "qed" :: ";" :: rest => some (some items, rest)
      | "qed" :: k :: ";" :: rest => if k == label then some (some items, rest) else none
      | _ => none
  | _ => none

/-- The `vars` section of an order (§5.3): `left u;`, `right v;` and an optional `aux a;`, with
`a` possibly empty, then `end [vars];`. -/
private def orderVars (N : Names) (ts : List String) :
    Option ((List ℕ × List ℕ × List ℕ) × List String) := do
  let ("vars" :: "left" :: ts) := ts | none
  let (u, ts) ← varList N ts
  let ("right" :: ts) := ts | none
  let (v, ts) ← varList N ts
  let (a, ts) ← match ts with
    | "aux" :: ts => varList N ts
    | ts => some ([], ts)
  let ts ← endOf "vars" ts
  pure ((u, v, a), ts)

/-- The lines of a `spec` section of `def_order` (§5.3), up to its `end`:
`red C : ω : subproof … qed [: n];`, the constraint and its justification. As in CakePB's
parser, each line needs its subproof, possibly empty; `red C : ω;` is rejected. -/
private def specLines (N : Names) : ℕ → List String →
    Option (List (PBConstr × SpecStep) × List String)
  | 0, _ => none
  | _ + 1, "end" :: ts => some ([], "end" :: ts)
  | fuel + 1, "red" :: ts =>
    match geq N ts with
    | some (c, ":" :: rest) =>
      (witnessTail N fuel rest).bind fun ((ω, sub, q), rest) =>
        if sub.isSome then
          (specLines N fuel rest).map fun (ls, rest) => ((c, ⟨ω, sub, q⟩) :: ls, rest)
        else none
    | _ => none
  | _ + 1, _ => none

/-- The body of `def_order name`, after its name (§5.3): the `vars` section, an optional `spec`
section, the `def` section, the `transitivity` section with its `fresh_right` variables, the
`fresh_aux_1` and `fresh_aux_2` variables if any, and its proof, an optional `reflexivity`
section, and `end [def_order];`. -/
private def defOrderBody (N : Names) (fuel : ℕ) (ts : List String) :
    Option ((Order × List SpecStep × TransVars × OrderProof × OrderProof) × List String) := do
  let ((u, v, a), ts) ← orderVars N ts
  let (spec, ts) ← match ts with
    | "spec" :: ts => do
      let (ls, ts) ← specLines N fuel ts
      let ts ← endOf "spec" ts
      pure (ls, ts)
    | ts => pure ([], ts)
  let ("def" :: ts) := ts | none
  let (defn, ts) ← defConstrs N fuel ts
  let ts ← endOf "def" ts
  let ("transitivity" :: "vars" :: "fresh_right" :: ts) := ts | none
  let (w, ts) ← varList N ts
  let (b, c, ts) ← match ts with
    | "fresh_aux_1" :: ts => do
      let (b, ts) ← varList N ts
      let ("fresh_aux_2" :: ts) := ts | none
      let (c, ts) ← varList N ts
      pure (b, c, ts)
    | ts => pure ([], [], ts)
  let ts ← endOf "vars" ts
  let (tp, ts) ← orderProof N fuel ts
  let ts ← endOf "transitivity" ts
  let (rp, ts) ← match ts with
    | "reflexivity" :: ts => do
      let (rp, ts) ← orderProof N fuel ts
      let ts ← endOf "reflexivity" ts
      pure (rp, ts)
    | ts => pure (⟨[], none⟩, ts)
  let ts ← endOf "def_order" ts
  pure ((⟨u, v, a, spec.map (·.1), defn⟩, spec.map (·.2), ⟨w, b, c⟩, tp, rp), ts)

/-- The body of `eord_def name`, after its name (§5.11.3): the `vars` section, an optional `spec`
section of constraints, the `def` section, and `end [eord_def];`. -/
private def eordDefBody (N : Names) (fuel : ℕ) (ts : List String) :
    Option (Order × List String) := do
  let ((u, v, a), ts) ← orderVars N ts
  let (spec, ts) ← match ts with
    | "spec" :: ts => do
      let (cs, ts) ← defConstrs N fuel ts
      let ts ← endOf "spec" ts
      pure (cs, ts)
    | ts => pure ([], ts)
  let ("def" :: ts) := ts | none
  let (defn, ts) ← defConstrs N fuel ts
  let ts ← endOf "def" ts
  let ts ← endOf "eord_def" ts
  pure (⟨u, v, a, spec, defn⟩, ts)

/-- A top-level step: a `red` or `dom` step, an order definition or loading, a deletion, `core id`,
`strengthening_to_core`, solution logging, or an implicational step. These steps other than the
implicational ones are top-level only: subproof scopes are specified in §5.5 of the format
documentation, the orders in §5.3, `core id` in §5.1,
strengthening-to-core mode in §5.6, and the kernel deletions in §5.7.1. A checked deletion
`delc id : ω [: subproof … qed [delc] [: n]];` deletes one constraint. -/
private def topStep (N : Names) (fuel : ℕ) : List String → Option (List TopStep × List String)
  | k@"red" :: ts | k@"dom" :: ts =>
    let mk := if k == "red" then TopStep.red else TopStep.dom
    match geq N ts with
    | some (c, ";" :: rest) => some ([mk c [] none none], rest)
    | some (c, ":" :: rest) =>
      (witnessTail N fuel rest).map fun ((ω, sub, q), rest) => ([mk c ω sub q], rest)
    | _ => none
  | "def_order" :: name :: ts =>
    (defOrderBody N fuel ts).map fun ((O, sp, w, tp, rp), rest) =>
      ([.defOrder name O sp w tp rp], rest)
  | "eord_def" :: name :: ts =>
    (eordDefBody N fuel ts).map fun (O, rest) => ([.eordDef name O], rest)
  | "eord_loaded" :: name :: ts =>
    match lits N ts with
    | some (z, ";" :: rest) => some ([.eordLoaded name z], rest)
    | _ => none
  | "load_order" :: ";" :: rest => some ([.unloadOrder], rest)
  | "load_order" :: name :: ts =>
    match lits N ts with
    | some (z, ";" :: rest) => some ([.loadOrder name z], rest)
    | _ => none
  | "deld" :: ts =>
    match ids ts with
    | some (ns, ";" :: rest) => some ([.deld ns], rest)
    | _ => none
  | "delc" :: n :: ":" :: ts =>
    (id? n).bind fun i =>
      (witnessTail N fuel ts).map fun ((ω, sub, q), rest) => ([.delcChecked i ω sub q], rest)
  | "delc" :: ts =>
    match ids ts with
    | some (ns, ";" :: rest) => some ([.delc ns], rest)
    | _ => none
  | "del" :: "id" :: ts =>
    match ids ts with
    | some (ns, ";" :: rest) => some ([.step (.del ns)], rest)
    | _ => none
  | "strengthening_to_core" :: "on" :: ";" :: rest => some ([.strengthenToCore true], rest)
  | "strengthening_to_core" :: "off" :: ";" :: rest => some ([.strengthenToCore false], rest)
  | k@"sol" :: ts | k@"solx" :: ts | k@"soli" :: ts =>
    match lits N ts with
    | some (ρ, ";" :: rest) =>
      some ([if k == "sol" then .sol ρ else if k == "solx" then .solx ρ else .soli ρ], rest)
    | _ => none
  | "obji" :: v :: ";" :: rest => (int? v).map fun v => ([.obji v], rest)
  | "obju" :: kind :: ts =>
    (if kind == "new" then some false else if kind == "diff" then some true else none).bind
      fun diff =>
        (objTerms N.lit? ts).bind fun (g, rest) =>
          (subproofTail "obju" N fuel rest).map fun (sub, rest) => ([.obju diff g sub], rest)
  | k@"preserved_add" :: x :: ":" :: ts | k@"preserved_rm" :: x :: ":" :: ts =>
    (N.var? x).bind fun v =>
      (geq N ts).bind fun (c, rest) =>
        (subproofTail k N fuel rest).map fun (sub, rest) =>
          ([.presChange (k == "preserved_add") v c sub], rest)
  | "epreserved" :: ts => (varList N ts).map fun (vs, rest) => ([.epreserved vs], rest)
  | "core" :: "id" :: ts =>
    match ids ts with
    | some (ns, ";" :: rest) => some ([.core ns], rest)
    | _ => none
  | ts => (step N fuel ts).map fun (s, rest) => ([.step s], rest)

/-- The top-level steps, up to `output`. -/
private def topSteps (N : Names) : ℕ → List String → Option (List TopStep × List String)
  | 0, _ => none
  | _ + 1, "output" :: ts => some ([], "output" :: ts)
  | fuel + 1, ts =>
    (topStep N fuel ts).bind fun (ss, rest) =>
      (topSteps N fuel rest).map fun (ss', rest) => (ss ++ ss', rest)

/-- A bound of `BOUNDS`: an integer, or `INF` as `none`. -/
private def bound? (t : String) : Option (Option ℤ) :=
  if t == "INF" then some none else (int? t).map some

/-- An optional assignment `: ρ` at the end of a conclusion, up to the final `;`. -/
private def asgOpt (N : Names) : List String → Option (Option (List (Literal ℕ)))
  | [";"] => some none
  | ":" :: ts =>
    match lits N ts with
    | some (ρ, [";"]) => some (some ρ)
    | _ => none
  | _ => none

/-- The conclusion section, after `conclusion`: `UNSAT : id`, `SAT [: ρ]`,
`BOUNDS lb : id ub [: ρ]` or `NONE` (§4.3). -/
private def conclusion (N : Names) : List String → Option Conclusion
  | ["UNSAT", ":", q, ";"] => (id? q).map .unsat
  | ["NONE", ";"] => some .noClaim
  | ["ENUMERATION_PARTIAL", n, ";"] => (nat? n).map .enumPartial
  | ["ENUMERATION_COMPLETE", n, ":", q, ";"] =>
    (nat? n).bind fun n => (id? q).map (.enumComplete n)
  | "SAT" :: ts => (asgOpt N ts).map .sat
  | "BOUNDS" :: lb :: ":" :: q :: ub :: ts =>
    (bound? lb).bind fun lb => (id? q).bind fun q => (bound? ub).bind fun ub =>
      (asgOpt N ts).map (.bounds lb q ub ·)
  | _ => none

/-- An output guarantee other than `NONE` (§4.2). -/
private def guarantee? : String → Option Guarantee
  | "DERIVABLE" => some .derivable
  | "EQUISATISFIABLE" => some .equisatisfiable
  | "EQUIOPTIMAL" => some .equioptimal
  | "EQUIENUMERABLE" => some .equienumerable
  | _ => none

/-- An output section after `output`, up to its `;`: `NONE`, or a guarantee with `FILE`
(`true`) or `IMPLICIT` (`false`), and the rest. -/
private def outputSection : List String → Option (Option (Guarantee × Bool) × List String)
  | "NONE" :: ";" :: rest => some (none, rest)
  | g :: k :: ";" :: rest =>
    (guarantee? g).bind fun g =>
      if k == "FILE" then some (some (g, true), rest)
      else if k == "IMPLICIT" then some (some (g, false), rest)
      else none
  | _ => none

/-- A proof given as tokens, read with the names `N`, for a formula with `m` constraints: the
proof and its output section, `none` for `output NONE;`. -/
private def proofIn (m : ℕ) (N : Names) (ts : List String) :
    Option (RedProof × Option (Guarantee × Bool)) :=
  match ts with
  | "pseudo-Boolean" :: "proof" :: "version" :: "3.0" :: rest =>
    let rest := match rest with
      | "f" :: n :: ";" :: rest => if nat? n == some m then some rest else none
      | rest => some rest
    rest.bind fun rest =>
      match topSteps N (ts.length + 1) rest with
      | some (ss, "output" :: rest) =>
        match outputSection rest with
        | some (out, "conclusion" :: rest) =>
          match rest.reverse with
          | ";" :: "proof" :: "pseudo-Boolean" :: "end" :: concl =>
            (conclusion N concl.reverse).map fun c => (⟨ss, c⟩, out)
          | _ => none
        | _ => none
      | _ => none
  | _ => none

/-- **A proof** in the supported fragment (kernel proofs, with `f N;` optional) with the output
section `output NONE;`, for a formula with `m` constraints over the variables below `nvars`, named
by their standard names. -/
def parseProof (m nvars : ℕ) (s : String) : Option RedProof :=
  match proofIn m ((⟨[], nvars⟩ : Names).extend (tokens s)) (tokens s) with
  | some (P, none) => some P
  | _ => none

/-! ### The checkers -/

/-- The number of variables of a formula, an objective and a preserved set: one more than their
largest variable. The names a proof introduces are numbered from there, so they never collide
with a preserved variable absent from the formula and the objective. -/
private def numVars (F : List PBConstr) (obj : Option Objective)
    (pres : Option (List ℕ) := none) : ℕ :=
  (F.flatMap PBConstr.terms).foldr (fun t m => max (PBConstr.termVar t + 1) m)
    ((obj.map (·.lin)).getD [] |>.foldr (fun e m => max (e.1 + 1) m)
      (pres.getD [] |>.foldr (fun v m => max (v + 1) m) 0))

/-- **The names of a proof and its output text** for an OPB text: those of the OPB text
(`Cslib.Logic.PL.VeriPB.Text.opbNames`), then the names the proof and the output text add, in
order of first appearance. -/
def proofNames (opb pbp : String) (out : Option String := none) : Names :=
  (opbNames opb).extend (tokens pbp ++ (out.map tokens).getD [])

/-- The names of a proof and its output text are well formed. -/
theorem proofNames_wf (opb pbp : String) (out : Option String) : (proofNames opb pbp out).WF :=
  (opbNames_wf opb).extend _

/-- **Check a proof with an output section for an OPB instance**, in the supported fragment,
with the output formula `out` for `output g FILE;`: the conclusion and the output, `none` for
`output NONE;`, if the proof is accepted (`Cslib.Logic.PL.VeriPB.checkRedOutput`). The output
formula is read with the names of the proof (`Cslib.Logic.PL.VeriPB.Text.proofNames`). `FILE`
needs an output formula and `IMPLICIT` none; `NONE` ignores it. -/
def checkOPBOutput (opb pbp : String) (out : Option String := none) :
    Option (Conclusion × Option Output) :=
  (parseOPB opb).bind fun I =>
    let N := proofNames opb pbp out
    (proofIn I.constraints.length N (tokens pbp)).bind fun (P, sec) =>
      match sec, out with
      | none, _ =>
        if checkRed I.constraints I.objective P I.preserved then some (P.conclusion, none) else none
      | some (g, true), some t =>
        (parseOPBWith N t).bind fun O =>
          (checkRedOutput I.constraints I.objective P I.preserved ⟨g, some O⟩).map
            fun o => (P.conclusion, some o)
      | some (g, false), none =>
        (checkRedOutput I.constraints I.objective P I.preserved ⟨g, none⟩).map
          fun o => (P.conclusion, some o)
      | some _, _ => none

/-- **Check a proof for an OPB instance**, in the supported fragment: the conclusion, if the
proof is accepted, with an output section `NONE` or `IMPLICIT`. -/
def checkOPB (opb pbp : String) : Option Conclusion :=
  (checkOPBOutput opb pbp).map (·.1)

/-- **Check a proof for a DIMACS CNF formula**, in the supported fragment: the conclusion, if
the proof is accepted. -/
def checkDIMACS (cnf pbp : String) : Option Conclusion :=
  (parseDIMACS cnf).bind fun φ =>
    (parseProof φ.length (numVars (φ.map Clause.toPB) none) pbp).bind fun P =>
      if checkRed (φ.map Clause.toPB) none P then some P.conclusion else none

/-- What an accepted proof with an output section gives: the parsed instance, and a proof of it,
accepted by the checker with the returned conclusion and with the returned output, if any. -/
private theorem of_checkOPBOutput {opb pbp : String} {out : Option String} {c : Conclusion}
    {o : Option Output} (h : checkOPBOutput opb pbp out = some (c, o)) :
    ∃ I P, parseOPB opb = some I ∧ checkRed I.constraints I.objective P I.preserved = true ∧
      P.conclusion = c ∧ ∀ o' ∈ o, ∃ g O, checkRedOutput I.constraints I.objective P I.preserved
        ⟨g, O⟩ = some o' ∧ ∀ t ∈ out, ∃ O', O = some O' ∧
          parseOPBWith (proofNames opb pbp out) t = some O' := by
  simp only [checkOPBOutput, Option.bind_eq_some_iff] at h
  obtain ⟨I, hI, ⟨P, sec⟩, -, h⟩ := h
  split at h
  · split at h
    · cases h
      exact ⟨I, P, hI, ‹_›, rfl, fun _ h => by cases h⟩
    · cases h
  · obtain ⟨O, hO, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨o', ho', h⟩ := Option.map_eq_some_iff.1 h
    cases h
    exact ⟨I, P, hI, checkRed_of_checkRedOutput ho', rfl, fun _ h => by
      cases h; exact ⟨_, some O, ho', fun t' ht' => by cases ht'; exact ⟨O, rfl, hO⟩⟩⟩
  · obtain ⟨o', ho', h⟩ := Option.map_eq_some_iff.1 h
    cases h
    exact ⟨I, P, hI, checkRed_of_checkRedOutput ho', rfl, fun _ h => by
      cases h; exact ⟨_, none, ho', fun t' ht' => by cases ht'⟩⟩
  · cases h

/-- **The conclusion of an accepted proof, with or without an output section**: the instance
parses and a proof of it with that conclusion is accepted by
`Cslib.Logic.PL.VeriPB.checkRed`, so the soundness theorems of the conclusions apply. -/
theorem exists_checkRed_of_checkOPBOutput {opb pbp : String} {out : Option String}
    {concl : Conclusion} (h : (checkOPBOutput opb pbp out).map (·.1) = some concl) :
    ∃ I P, parseOPB opb = some I ∧ checkRed I.constraints I.objective P I.preserved = true ∧
      P.conclusion = concl := by
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨c', o⟩, h', rfl⟩ := h
  obtain ⟨I, P, hI, hP, hc, -⟩ := of_checkOPBOutput h'
  exact ⟨I, P, hI, hP, hc⟩

/-- Bounds from a maximum fold: it is at least its start and each folded value. -/
private theorem le_foldr_max {α : Type} (g : α → ℕ) (b : ℕ) (l : List α) :
    b ≤ l.foldr (fun x m => max (g x) m) b ∧ ∀ x ∈ l, g x ≤ l.foldr (fun x m => max (g x) m) b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨ih.1.trans (le_max_right _ _), le_max_left _ _,
      fun y hy => (ih.2 y hy).trans (le_max_right _ _)⟩

/-- **The names of an OPB text read each of its OPB names**: a standard name as its number. -/
theorem opbNames_var? {s t : String} (ht : t ∈ (opbTokenLines s).flatten)
    (hn : isOPBName (bareName t) = true) :
    ∃ w, (opbNames s).var? (bareName t) = some w ∧ ∀ v, stdVar? (bareName t) = some v → w = v := by
  have hmem : bareName t ∈ ((opbTokenLines s).flatten.filter fun t => isOPBName (bareName t)).map
      bareName := List.mem_map_of_mem (List.mem_filter.2 ⟨ht, hn⟩)
  set ts := ((opbTokenLines s).flatten.filter fun t => isOPBName (bareName t)).map bareName
  set b := (ts.filterMap stdVar?).foldr (fun v m => max (v + 1) m) 0
  have hb : (opbNames s).base = b := rfl
  cases hv : stdVar? (bareName t) with
  | some v =>
    have hlt : v < b :=
      (le_foldr_max (fun v => v + 1) 0 _).2 v (List.mem_filterMap.2 ⟨_, hmem, hv⟩)
    exact ⟨v, by simp [Names.var?, hv, hb, hlt], fun _ h => Option.some.inj h⟩
  | none =>
    have hin : bareName t ∈ (opbNames s).others := by
      refine mem_addNew.2 (.inr (List.mem_filter.2 ⟨hmem, ?_⟩))
      simp [isName_of_isOPBName hn, Names.var?, hv]
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1
      (List.isSome_idxOf?.2 hin : ((opbNames s).others.idxOf? (bareName t)).isSome)
    exact ⟨(opbNames s).base + i, by simp [Names.var?, hv, hi], fun _ h => by cases h⟩

/-- **Soundness of the output section for OPB text**: if a proof with an output section is
accepted, the instance parses, the guarantee holds between it and the output formula for the
returned bound (`Cslib.Logic.PL.VeriPB.semOutput`), and the bound is at least the value of some
solution of the instance. For `FILE` the output formula is the output text, read with
well-formed names that extend those of the instance (`Cslib.Logic.PL.VeriPB.Text.Names.WF`,
`Cslib.Logic.PL.VeriPB.Text.Names.Extends`): a name of the instance is its variable, and every
other name a fresh variable. The conclusion is sound as for
`Cslib.Logic.PL.VeriPB.Text.checkOPB`: the soundness theorems of the conclusions take
`checkOPBOutput` with any output text. -/
theorem semOutput_of_checkOPBOutput {opb pbp : String} {out : Option String} {concl : Conclusion}
    {o : Output} (h : checkOPBOutput opb pbp out = some (concl, some o)) :
    ∃ I, parseOPB opb = some I ∧ semOutput I o.bound o.formula o.guarantee ∧
      (∀ u ∈ o.bound, ∃ σ, (∀ d ∈ I.constraints, d.Holds σ) ∧ objValue I.objective σ ≤ u) ∧
      ∀ t ∈ out, ∃ N : Names, N.WF ∧ N.Extends (opbNames opb) ∧
        parseOPBWith N t = some o.formula := by
  obtain ⟨I, P, hI, -, -, ho⟩ := of_checkOPBOutput h
  obtain ⟨g, O, ho, hO⟩ := ho o rfl
  refine ⟨I, hI, semOutput_of_checkRedOutput ho, exists_le_of_checkRedOutput ho, fun t ht => ?_⟩
  obtain ⟨O', rfl, hN⟩ := hO t ht
  exact ⟨_, (opbNames_wf opb).extend _, Names.extends_extend _ _,
    (output_of_checkRedOutput ho).2 O' rfl ▸ hN⟩

/-- **Soundness of `UNSAT` for OPB text**: an accepted proof of `UNSAT` means the instance parses
and its constraints have no 0/1 solution. -/
theorem not_satisfiable_of_checkOPB {opb pbp : String} {out : Option String} {q : ℕ}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.unsat q)) :
    ∃ I, parseOPB opb = some I ∧ ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨I, P, hI, h, hc⟩ := exists_checkRed_of_checkOPBOutput h
  exact ⟨I, hI, not_satisfiable_of_checkRed h hc⟩

/-- **Soundness of `SAT` for OPB text**: an accepted proof of `SAT` means the instance parses
and its constraints have a 0/1 solution. -/
theorem exists_satisfies_of_checkOPB {opb pbp : String} {out : Option String}
    {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.sat asg)) :
    ∃ I, parseOPB opb = some I ∧ ∃ σ : ℕ → Bool, ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨I, P, hI, h, hc⟩ := exists_checkRed_of_checkOPBOutput h
  exact ⟨I, hI, exists_satisfies_of_checkRed h hc⟩

/-- **Soundness of `SAT : ρ` for OPB text**: an accepted proof of `SAT` with the assignment `ρ`
means the instance parses and `ρ` solves its constraints. -/
theorem holds_of_checkOPB_sat {opb pbp : String} {out : Option String} {ρ : List (Literal ℕ)}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.sat (some ρ))) :
    ∃ I, parseOPB opb = some I ∧ ∀ c ∈ I.constraints, c.Holds (assignOf ρ) := by
  obtain ⟨I, P, hI, h, hc⟩ := exists_checkRed_of_checkOPBOutput h
  exact ⟨I, hI, holds_of_checkRed_sat h hc⟩

/-- **Soundness of `BOUNDS` for OPB text**: an accepted proof of `BOUNDS lb : q ub` means the
instance parses with an objective `f`; every 0/1 solution `σ` of its constraints has a finite
`lb` with `lb ≤ f σ` (so for `lb = INF` there is no solution); and for a finite `ub` some
solution has objective at most `ub`. -/
theorem bounds_of_checkOPB {opb pbp : String} {out : Option String} {lb ub : Option ℤ} {q : ℕ}
    {asg : Option (List (Literal ℕ))}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.bounds lb q ub asg)) :
    ∃ I f, parseOPB opb = some I ∧ I.objective = some f ∧
      (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → ∃ l, lb = some l ∧ l ≤ f.eval σ) ∧
      ∀ u, ub = some u → ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ u := by
  obtain ⟨I, P, hI, hck, hc⟩ := exists_checkRed_of_checkOPBOutput h
  cases hobj : I.objective with
  | none =>
    rw [hobj] at hck
    unfold checkRed at hck
    split at hck
    · simp [hc, checkConclusion] at hck
    · cases hck
  | some f =>
    rw [hobj] at hck
    refine ⟨I, f, hI, hobj, fun σ hσ => ?_, fun u hu => ?_⟩
    · cases lb with
      | none => exact absurd hσ (not_satisfiable_of_checkRed_bounds hck hc σ)
      | some l => exact ⟨l, rfl, le_eval_of_checkRed hck hc σ hσ⟩
    · subst hu
      exact exists_eval_le_of_checkRed hck hc

/-- **Soundness of a partial enumeration for OPB text**: an accepted proof of
`ENUMERATION_PARTIAL n` means the instance parses with a preserved set `P`, and its solutions have
at least `n` distinct projections to `P`. -/
theorem le_encard_of_checkOPB_enumPartial {opb pbp : String} {out : Option String} {n : ℕ}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.enumPartial n)) :
    ∃ I P, parseOPB opb = some I ∧ I.preserved = some P ∧
      (n : ℕ∞) ≤ (projections I.constraints P).encard := by
  obtain ⟨I, Pf, hI, hck, hc⟩ := exists_checkRed_of_checkOPBOutput h
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 (isSome_of_checkRed_enum hck (.inl hc))
  rw [hP] at hck
  exact ⟨I, P, hI, hP, le_encard_of_checkRed_enum hck (.inl hc)⟩

/-- **Soundness of a complete enumeration for OPB text**: an accepted proof of
`ENUMERATION_COMPLETE n : q` means the instance parses with a preserved set `P`, and its
solutions have exactly `n` distinct projections to `P`. -/
theorem encard_eq_of_checkOPB_enumComplete {opb pbp : String} {out : Option String} {n q : ℕ}
    (h : (checkOPBOutput opb pbp out).map (·.1) = some (.enumComplete n q)) :
    ∃ I P, parseOPB opb = some I ∧ I.preserved = some P ∧
      (projections I.constraints P).encard = n := by
  obtain ⟨I, Pf, hI, hck, hc⟩ := exists_checkRed_of_checkOPBOutput h
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 (isSome_of_checkRed_enum hck (.inr ⟨q, hc⟩))
  rw [hP] at hck
  exact ⟨I, P, hI, hP, encard_eq_of_checkRed_enumComplete hck hc⟩

/-- **Soundness of `UNSAT` for DIMACS text**: an accepted proof of `UNSAT` means the CNF parses
and is unsatisfiable. -/
theorem not_satisfiable_of_checkDIMACS {cnf pbp : String} {q : ℕ}
    (h : checkDIMACS cnf pbp = some (.unsat q)) :
    ∃ φ, parseDIMACS cnf = some φ ∧ ¬ φ.Satisfiable := by
  simp only [checkDIMACS, Option.bind_eq_some_iff] at h
  obtain ⟨φ, hφ, P, -, h⟩ := h
  split at h
  · exact ⟨φ, hφ, not_satisfiable_cnf_of_checkRed ‹_› (Option.some.inj h)⟩
  · cases h

/-- **Soundness of `SAT` for DIMACS text**: an accepted proof of `SAT` means the CNF parses and
is satisfiable. -/
theorem satisfiable_of_checkDIMACS {cnf pbp : String} {asg : Option (List (Literal ℕ))}
    (h : checkDIMACS cnf pbp = some (.sat asg)) :
    ∃ φ, parseDIMACS cnf = some φ ∧ φ.Satisfiable := by
  simp only [checkDIMACS, Option.bind_eq_some_iff] at h
  obtain ⟨φ, hφ, P, -, h⟩ := h
  split at h
  · obtain ⟨σ, hσ⟩ := exists_satisfies_of_checkRed ‹_› (Option.some.inj h)
    refine ⟨φ, hφ, σ, (CNF.eval_eq_true_iff σ φ).2 fun cl hcl => ?_⟩
    exact (Clause.holds_toPB_iff σ cl).1 (hσ _ (List.mem_map_of_mem hcl))
  · cases h

end Cslib.Logic.PL.VeriPB.Text

end
