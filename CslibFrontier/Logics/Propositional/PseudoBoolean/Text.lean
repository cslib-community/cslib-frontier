/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Output

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
(`Cslib.Logic.PL.VeriPB.sameUpToOrder`); the strict kernel format requires the subproof (§6.1). The
`red` steps of a specification must have their subproof, as in CakePB. Third, in `def_order` the
`aux` line and the `reflexivity` section are optional, a missing reflexivity proof leaving only
trivially true goals; the kernel format requires both (§6.1). The remaining extensions, `del id` and
`rup` without hints, are described under **Steps**. So a proof accepted here need not be a kernel
proof.

**Variables.** The variable `xN` is `N - 1`, as in `Cslib.Logic.PL.Literal.ofDIMACS`, so a DIMACS
variable and its name in the proof agree. Formulas use only these names, as OPB requires. A proof
may introduce other names; they are numbered after every `xN` of the formula and the proof, in order
of first appearance; so are the auxiliary variables `$a` of orders (§5.3), which are names like any
other here, the checker testing their freshness where it matters. How the proof's own variables are
numbered does not matter for the conclusions, which concern only the parsed formula. An output
formula is read with the names of its proof, the names of the proof and of the output text being
numbered together.

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
an optional constant included, and an optional subproof of `proofgoal #1` and `#2` (§5.9), `core id`
(§5.1), `strengthening_to_core on` and `off` (§5.6), and the deletions (§5.7.1): `deld` of derived
constraints, the unchecked `delc` of core constraints, and the checked `delc id : ω` of one core
constraint, with an optional subproof. Orders, `dom`, deletion, `core`, strengthening-to-core,
solution logging, `obji` and `obju` are accepted only at top level, as the format requires. Two
steps of the augmented format are also accepted: `del id`, read as the untyped deletion
`Cslib.Logic.PL.VeriPB.Step.del` (§5.7.2; a deletion of a core constraint counts as unchecked), and
`rup` without hints, read as `Cslib.Logic.PL.VeriPB.Step.rupSearch`. Everything else (`pol`
operations `c`, `m`, `n` and `-`, relative constraint numbers, `i` and `ia`, the preserved-set
rules, `del spec`, levels, and the conclusion `UNSAT` without an ID) is rejected.

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

## Main definitions

* `Cslib.Logic.PL.VeriPB.Text.parseOPB`, `Cslib.Logic.PL.VeriPB.Text.parseDIMACS`: instances
  and formulas.
* `Cslib.Logic.PL.VeriPB.Text.parseProof`: proofs in the supported fragment.
* `Cslib.Logic.PL.VeriPB.Text.checkOPB`, `Cslib.Logic.PL.VeriPB.Text.checkOPBOutput`,
  `Cslib.Logic.PL.VeriPB.Text.checkDIMACS`: the checkers.
* `Cslib.Logic.PL.VeriPB.Text.Names.Separates`: names that read an output text without aliasing
  the variables of the instance.

## Main results

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

/-! The lexer works on the characters of a text by structural recursion, without `String.splitOn`,
`String.toNat?` and the other `String` operations that the kernel cannot evaluate, so that
`decide` can check concrete texts. -/

/-- The pieces of a list of characters between the characters satisfying `p`. -/
private def splitChars (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if p c then [] :: splitChars p cs
    else
      match splitChars p cs with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- The lines of a text. -/
private def lines (s : String) : List String := (splitChars (· == '\n') s.toList).map String.ofList

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

/-- The tokens of a text: whitespace-separated, with `;` a token of its own and everything after
`%` on a line a comment. -/
def tokens (s : String) : List String :=
  (splitChars (· == '\n') s.toList).flatMap fun line => lexLine (line.takeWhile (· != '%')) []

/-- The value of decimal digits after the value `n` of those before them. -/
private def digits : List Char → ℕ → Option ℕ
  | [], n => some n
  | c :: cs, n => if c.isDigit then digits cs (10 * n + (c.toNat - '0'.toNat)) else none

/-- A natural number: one or more decimal digits. -/
private def nat? (t : String) : Option ℕ :=
  match t.toList with
  | [] => none
  | cs => digits cs 0

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

/-- The number `N - 1` of a standard variable name `xN`, `N ≥ 1`. -/
def stdVar? (t : String) : Option ℕ :=
  match dropChar? 'x' t with
  | some r =>
    match nat? r with
    | some (n + 1) => some n
    | _ => none
  | none => none

/-- A variable name of the extended format: at least two characters, the first a letter, `_`, or
the `$` of an auxiliary variable (§5.3). -/
private def isName (t : String) : Bool :=
  match t.toList with
  | c :: _ :: _ => c.isAlpha || c == '_' || c == '$'
  | _ => false

/-- The variable names of a proof: the standard ones are numbered by their index, the others in
order of first appearance after `base`. -/
structure Names where
  /-- The non-standard names, in order of first appearance. -/
  others : List String
  /-- The first number free for them. -/
  base : ℕ

/-- The number of a variable name. -/
def Names.var? (N : Names) (t : String) : Option ℕ :=
  match stdVar? t with
  | some v => some v
  | none => if isName t then (N.others.idxOf? t).map (N.base + ·) else none

/-- A literal token `x` or `~x`. -/
def Names.lit? (N : Names) (t : String) : Option (Literal ℕ) :=
  match dropChar? '~' t with
  | some r => (N.var? r).map ((·, false))
  | none => (N.var? t).map ((·, true))

/-- A token without the `~` of a negative literal. -/
def bareName (t : String) : String := (dropChar? '~' t).getD t

/-- **The names `N` read the output text `t` of the instance `I` without aliasing.** The
non-standard names are distinct and none is a standard name `xN`; they are numbered from
`N.base`, which is above every variable of `I` and every standard name of `t`. So distinct names
of `t` denote distinct variables, and a variable of `I` is denoted in `t` only by its standard
name. -/
structure Names.Separates (N : Names) (I : Instance) (t : String) : Prop where
  /-- The non-standard names are distinct. -/
  nodup : N.others.Nodup
  /-- No non-standard name is a standard name. -/
  others_std : ∀ s ∈ N.others, stdVar? s = none
  /-- The variables of the constraints of `I` are below `N.base`. -/
  constraints_lt : ∀ c ∈ I.constraints, ∀ x ∈ c.terms, PBConstr.termVar x < N.base
  /-- The variables of the objective of `I` are below `N.base`. -/
  objective_lt : ∀ f ∈ I.objective, ∀ e ∈ f.lin, e.1 < N.base
  /-- The preserved variables of `I` are below `N.base`. -/
  preserved_lt : ∀ P ∈ I.preserved, ∀ v ∈ P, v < N.base
  /-- The standard names of `t` are below `N.base`. -/
  std_lt : ∀ s ∈ tokens t, ∀ v, stdVar? (bareName s) = some v → v < N.base

/-- The names of the proof tokens `ts` over a formula whose variables are below `nvars`. -/
private def Names.ofTokens (nvars : ℕ) (ts : List String) : Names :=
  let bare := ts.map bareName
  ⟨(bare.filter fun t => isName t && (stdVar? t).isNone).dedup,
    (bare.filterMap stdVar?).foldr (fun v m => max (v + 1) m) nvars⟩

/-! ### Constraints -/

/-- The terms `a ℓ` of a constraint or an objective, up to the relation, `;` or `:`, as an integer
linear form and a constant: that contributed by negative literals (`a ¬x = a - a x`) and, in an
objective, a final constant term. A constraint never ends in `;` or `:` before its relation, so
`constr` still rejects a constant there. -/
private def terms (N : Names) :
    ℕ → List String → List (ℕ × ℤ) → ℤ → Option (List (ℕ × ℤ) × ℤ × List String)
  | 0, _, _, _ => none
  | fuel + 1, t :: ts, L, k =>
    if t == ">=" || t == "<=" || t == "=" || t == ";" || t == ":" then some (L, k, t :: ts)
    else
      -- A coefficient and a literal, or a literal with coefficient `1`.
      let (a, rest) := match int? t with
        | some a => (a, ts)
        | none => (1, t :: ts)
      match rest with
      | u :: rest =>
        -- A coefficient before `;` or `:` is the constant of an objective.
        if (int? t).isSome && (u == ";" || u == ":") then some (L, k + a, u :: rest)
        else
          match N.lit? u with
          | some (v, true) => terms N fuel rest (PBConstr.insertCoeff v a L) k
          | some (v, false) => terms N fuel rest (PBConstr.insertCoeff v (-a) L) (k + a)
          | none => none
      | [] => none
  | _ + 1, [], _, _ => none

/-- A constraint `∑ aᵢ ℓᵢ ⋈ A`: one or two constraints `≥` (`=` gives two), and the rest. -/
private def constr (N : Names) (ts : List String) : Option (List PBConstr × List String) :=
  match terms N (ts.length + 1) ts [] 0 with
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
    match constr N ts with
    | some ([c], rest) => some (c, rest)
    | _ => none

/-! ### Formulas -/

/-- The constraints of OPB lines, given as token lists. -/
private def opbLines (N : Names) : List (List String) → Option (List PBConstr)
  | [] => some []
  | [] :: ls => opbLines N ls
  | (t :: ts) :: ls =>
    if startsWithChar '*' t then opbLines N ls
    else
      match constr N (t :: ts), opbLines N ls with
      | some (cs, [";"]), some F => some (cs ++ F)
      | _, _ => none

/-- An objective `∑ wᵢ ℓᵢ [k]` with an optional constant `k`, up to `;` or `:`, and the rest from
there: the OPB objective syntax, which `obju` reuses (§5.9). -/
private def objTerms (N : Names) (ts : List String) : Option (Objective × List String) :=
  match terms N (ts.length + 1) ts [] 0 with
  | some (L, k, t :: rest) => if t == ";" || t == ":" then some (⟨L, k⟩, t :: rest) else none
  | _ => none

/-- An objective line `min: ∑ wᵢ ℓᵢ [k];`, given its tokens after `min:`, with an optional
constant `k`. -/
private def objective (N : Names) (ts : List String) : Option Objective :=
  match objTerms N ts with
  | some (f, [";"]) => some f
  | _ => none

/-- The variables of a `preserved:` line, up to `;`. -/
private def presVars (N : Names) : List String → Option (List ℕ)
  | [";"] => some []
  | t :: ts => (N.var? t).bind fun v => (presVars N ts).map (v :: ·)
  | [] => none

/-- **An OPB instance** (`Cslib.Logic.PL.VeriPB.Instance`): comment lines starting with `*`, an
optional objective line `min: …;` and an optional preserved-set line `preserved: …;`, in either
order, before the constraints, and one constraint per line. Variables are read with the names
`N`: by default only the standard names `xN`, as for an input; an output formula is read with the
names of its proof. -/
def parseOPB (s : String) (N : Names := ⟨[], 0⟩) : Option Instance :=
  let lines := ((lines s).map tokens).filter fun l =>
    match l.head? with
    | none => false
    | some t => !startsWithChar '*' t
  match lines with
  | ("min:" :: ts) :: ("preserved:" :: ps) :: ls
  | ("preserved:" :: ps) :: ("min:" :: ts) :: ls =>
    (objective N ts).bind fun f => (presVars N ps).bind fun P =>
      (opbLines N ls).map (⟨·, some f, some P⟩)
  | ("min:" :: ts) :: ls =>
    (objective N ts).bind fun f => (opbLines N ls).map (⟨·, some f, none⟩)
  | ("preserved:" :: ps) :: ls =>
    (presVars N ps).bind fun P => (opbLines N ls).map (⟨·, none, some P⟩)
  | ls => (opbLines N ls).map (⟨·, none, none⟩)

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
        match objTerms N ts with
        | some (g, ";" :: rest) => some ([.obju diff g none], rest)
        | some (g, ":" :: "subproof" :: rest) =>
          (redItems N fuel rest).bind fun (items, rest) =>
            match rest with
            | "qed" :: ";" :: rest | "qed" :: "obju" :: ";" :: rest =>
              some ([.obju diff g (some items)], rest)
            | _ => none
        | _ => none
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
section `output NONE;`, for a formula with `m` constraints over the variables below `nvars`. -/
def parseProof (m nvars : ℕ) (s : String) : Option RedProof :=
  match proofIn m (Names.ofTokens nvars (tokens s)) (tokens s) with
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

/-- **Check a proof with an output section for an OPB instance**, in the supported fragment,
with the output formula `out` for `output g FILE;`: the conclusion and the output, `none` for
`output NONE;`, if the proof is accepted (`Cslib.Logic.PL.VeriPB.checkRedOutput`). The output
formula is read with the names of the proof, the names of both texts being numbered together.
`FILE` needs an output formula and `IMPLICIT` none; `NONE` ignores it. -/
def checkOPBOutput (opb pbp : String) (out : Option String := none) :
    Option (Conclusion × Option Output) :=
  (parseOPB opb).bind fun I =>
    let N := Names.ofTokens (numVars I.constraints I.objective I.preserved)
      (tokens pbp ++ (out.map tokens).getD [])
    (proofIn I.constraints.length N (tokens pbp)).bind fun (P, sec) =>
      match sec, out with
      | none, _ =>
        if checkRed I.constraints I.objective P I.preserved then some (P.conclusion, none) else none
      | some (g, true), some t =>
        (parseOPB t N).bind fun O =>
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
          parseOPB t (Names.ofTokens (numVars I.constraints I.objective I.preserved)
            (tokens pbp ++ tokens t)) = some O' := by
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

/-- The names of a proof and an output text over an instance separate the two
(`Cslib.Logic.PL.VeriPB.Text.Names.Separates`). -/
private theorem separates_ofTokens (I : Instance) (ts t : List String) (ht : ∀ s ∈ t, s ∈ ts)
    (u : String) (hu : tokens u = t) :
    (Names.ofTokens (numVars I.constraints I.objective I.preserved) ts).Separates I u := by
  have hF := le_foldr_max (fun t => PBConstr.termVar t + 1)
    ((I.objective.map (·.lin)).getD [] |>.foldr (fun e m => max (e.1 + 1) m)
      (I.preserved.getD [] |>.foldr (fun v m => max (v + 1) m) 0))
    (I.constraints.flatMap PBConstr.terms)
  have hO := le_foldr_max (fun e : ℕ × ℤ => e.1 + 1)
    (I.preserved.getD [] |>.foldr (fun v m => max (v + 1) m) 0)
    ((I.objective.map (·.lin)).getD [])
  have hP := le_foldr_max (fun v => v + 1) 0 (I.preserved.getD [])
  have hB := le_foldr_max (fun v => v + 1) (numVars I.constraints I.objective I.preserved)
    ((ts.map bareName).filterMap stdVar?)
  simp only [numVars] at hB
  dsimp only [Names.ofTokens, numVars]
  refine ⟨List.nodup_dedup _, fun s hs => ?_, fun c hc x hx => ?_, fun f hf e he => ?_,
    fun P hP' v hv => ?_, fun s hs v hv => ?_⟩
  · simp only [List.mem_dedup, List.mem_filter, Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
    exact hs.2.2
  · exact lt_of_lt_of_le (hF.2 x (List.mem_flatMap.2 ⟨c, hc, hx⟩)) hB.1
  · exact lt_of_lt_of_le (hO.2 e (by simpa [Option.mem_def.1 hf] using he)) (hF.1.trans hB.1)
  · exact lt_of_lt_of_le (hP.2 v (by simpa [Option.mem_def.1 hP'] using hv))
      (hO.1.trans (hF.1.trans hB.1))
  · exact hB.2 v (List.mem_filterMap.2 ⟨bareName s, List.mem_map_of_mem (ht s (hu ▸ hs)), hv⟩)

/-- **Soundness of the output section for OPB text**: if a proof with an output section is
accepted, the instance parses, the guarantee holds between it and the output formula for the
returned bound (`Cslib.Logic.PL.VeriPB.semOutput`), and the bound is at least the value of some
solution of the instance. For `FILE` the output formula is the output text, read with names that
separate it from the instance (`Cslib.Logic.PL.VeriPB.Text.Names.Separates`): a standard name
`xN` is the variable `N - 1` of the instance, and every other name is a fresh variable. The
conclusion is sound as for `Cslib.Logic.PL.VeriPB.Text.checkOPB`: the soundness theorems of the
conclusions take `checkOPBOutput` with any output text. -/
theorem semOutput_of_checkOPBOutput {opb pbp : String} {out : Option String} {concl : Conclusion}
    {o : Output} (h : checkOPBOutput opb pbp out = some (concl, some o)) :
    ∃ I, parseOPB opb = some I ∧ semOutput I o.bound o.formula o.guarantee ∧
      (∀ u ∈ o.bound, ∃ σ, (∀ d ∈ I.constraints, d.Holds σ) ∧ objValue I.objective σ ≤ u) ∧
      ∀ t ∈ out, ∃ N, N.Separates I t ∧ parseOPB t N = some o.formula := by
  obtain ⟨I, P, hI, -, -, ho⟩ := of_checkOPBOutput h
  obtain ⟨g, O, ho, hO⟩ := ho o rfl
  refine ⟨I, hI, semOutput_of_checkRedOutput ho, exists_le_of_checkRedOutput ho, fun t ht => ?_⟩
  obtain ⟨O', rfl, hN⟩ := hO t ht
  exact ⟨_, separates_ofTokens I _ _ (fun s hs => List.mem_append_right _ hs) t rfl,
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
