/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-!
# A text front end for the VeriPB kernel-proof checker

Parsers for the input formats of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023] and for a fragment of the kernel proof format,
extended as described below, producing the abstract syntax checked by
`Cslib.Logic.PL.VeriPB.checkRed`:

* an OPB instance (`Cslib.Logic.PL.VeriPB.Text.parseOPB`): an optional objective line
  `min: ∑ wᵢ ℓᵢ;` before the constraints (`Cslib.Logic.PL.VeriPB.Objective`), then one
  constraint `∑ aᵢ ℓᵢ ⋈ A;` per line with `⋈` one of `>=`, `<=`, `=`, an equality counting as the
  two constraints `≥` and `≤` in this order; lines starting with `*` are comments;
* a DIMACS CNF formula (`Cslib.Logic.PL.VeriPB.Text.parseDIMACS`): the header `p cnf V C`, then
  exactly `C` clauses over the variables `1, …, V`, its clause `1 -2 3 0` read as the constraint
  `x1 + ~x2 + x3 >= 1` (`Cslib.Logic.PL.Clause.toPB`);
* a proof (`Cslib.Logic.PL.VeriPB.Text.parseProof`): the header
  `pseudo-Boolean proof version 3.0`, the line `f N;` checked against the number of
  constraints, the derivation steps, `output NONE;`, a conclusion `UNSAT : id`, `SAT` or
  `BOUNDS lb : id ub` (§4.3, with `INF` for an infinite bound), and
  `end pseudo-Boolean proof;`.

**Supported fragment and extensions.** The parser accepts a fragment of the kernel format (§6.1
of the VeriPB/CakePB documentation, 22 June 2026 edition), with three extensions. First, the
line `f N;` is optional, as in the general format (§4.1). The kernel format requires it as the
first command after the header (§6.1), but a proof without it is accepted and checked against
the parsed formula. The other two extensions, `del id` and `rup` without hints, are described
under **Steps**. So a proof accepted here need not be a kernel proof.

**Variables.** The variable `xN` is `N - 1`, as in `Cslib.Logic.PL.Literal.ofDIMACS`, so a DIMACS
variable and its name in the proof agree. Formulas use only these names, as OPB requires. A proof
may introduce other names; they are numbered after every `xN` of the formula and the proof, in
order of first appearance. How the proof's own variables are numbered does not matter for
soundness, which concerns only the parsed formula.

**Steps.** The kernel steps `pol`, `rup` with hints, `pbc` with its subproof, `red` with a
witness and an optional subproof of `proofgoal` blocks (`#1`, `#2` for the objective, and
constraint numbers), the solution-logging steps `sol` and `soli` and the bound `obji` (§5.8),
`core id` (§5.1), `strengthening_to_core on` and `off` (§5.6), and the deletions (§5.7.1):
`deld` of derived constraints, the unchecked `delc` of core constraints, and the checked
`delc id : ω` of one core constraint, with an optional subproof. Deletion, `core`,
strengthening-to-core, solution logging and `obji` are accepted only at top level, as the format
requires. Two steps of the augmented
format are also accepted: `del id`, read as the untyped deletion
`Cslib.Logic.PL.VeriPB.Step.del` (§5.7.2; a deletion of a core constraint counts as unchecked),
and `rup` without hints, read as `Cslib.Logic.PL.VeriPB.Step.rupSearch`. Everything else (`pol`
operations `c`, `m`, `n` and `-`, relative constraint numbers, `i` and `ia`, orders, `dom`,
`solx`, `obju`, `del spec`, levels, other outputs and conclusions, and the optional
assignments of `SAT` and `BOUNDS`) is rejected.

**Soundness.** The checkers return the conclusion of an accepted proof. If it is `UNSAT`, the
input parses to a formula with no 0/1 solution
(`Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB`,
`Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS`); if `SAT`, to one with a solution
(`Cslib.Logic.PL.VeriPB.Text.exists_satisfies_of_checkOPB`,
`Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS`); if `BOUNDS lb : q ub`, to an
instance with an objective `f` whose every solution has value at least `lb` and, for a finite
`ub`, some solution has value at most `ub` (`Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB`).
This is a guarantee about the text and the formula the parser returns: the parsers are trusted
to read the files as intended, and nothing is said about compiled code. It is smaller than the
end-to-end theorem of CakePB (§6.2 of the VeriPB/CakePB documentation, 22 June 2026 edition),
which also covers the execution of its compiled machine code and the parsing of DIMACS input.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Text.OPB`, `Cslib.Logic.PL.VeriPB.Text.parseOPB`,
  `Cslib.Logic.PL.VeriPB.Text.parseDIMACS`: instances and formulas.
* `Cslib.Logic.PL.VeriPB.Text.parseProof`: proofs in the supported fragment.
* `Cslib.Logic.PL.VeriPB.Text.checkOPB`, `Cslib.Logic.PL.VeriPB.Text.checkDIMACS`: the checkers.

## Main results

* `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkOPB`,
  `Cslib.Logic.PL.VeriPB.Text.not_satisfiable_of_checkDIMACS`: soundness of `UNSAT`.
* `Cslib.Logic.PL.VeriPB.Text.exists_satisfies_of_checkOPB`,
  `Cslib.Logic.PL.VeriPB.Text.satisfiable_of_checkDIMACS`: soundness of `SAT`.
* `Cslib.Logic.PL.VeriPB.Text.bounds_of_checkOPB`: soundness of `BOUNDS`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Text

/-! ### Tokens -/

/-- The tokens of a text: whitespace-separated, with `;` a token of its own and everything after
`%` on a line a comment. -/
private def tokens (s : String) : List String :=
  (s.splitOn "\n").flatMap fun line =>
    ((((line.splitOn "%").headD "").replace ";" " ; ").split Char.isWhitespace).toList.map
      (·.toString) |>.filter (· ≠ "")

/-- An integer, with an optional sign `+` or `-`. -/
def int? (t : String) : Option ℤ :=
  if t.startsWith "+" then ((t.drop 1).toString.toNat?).map Int.ofNat else t.toInt?

/-- A positive constraint number. -/
def id? (t : String) : Option ℕ :=
  match t.toNat? with
  | some (n + 1) => some (n + 1)
  | _ => none

/-- The number `N - 1` of a standard variable name `xN`, `N ≥ 1`. -/
def stdVar? (t : String) : Option ℕ :=
  if t.startsWith "x" then
    match (t.drop 1).toString.toNat? with
    | some (n + 1) => some n
    | _ => none
  else none

/-- A variable name of the extended format: at least two characters, the first a letter or `_`. -/
private def isName (t : String) : Bool :=
  2 ≤ t.length && (t.front.isAlpha || t.front == '_')

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
  if t.startsWith "~" then (N.var? (t.drop 1).toString).map ((·, false))
  else (N.var? t).map ((·, true))

/-- The names of the proof tokens `ts` over a formula whose variables are below `nvars`. -/
private def Names.ofTokens (nvars : ℕ) (ts : List String) : Names :=
  let bare := ts.map fun t => if t.startsWith "~" then (t.drop 1).toString else t
  ⟨(bare.filter fun t => isName t && (stdVar? t).isNone).dedup,
    (bare.filterMap stdVar?).foldr (fun v m => max (v + 1) m) nvars⟩

/-! ### Constraints -/

/-- The terms `a ℓ` of a constraint or an objective, up to the relation or `;`, as an integer
linear form and the constant contributed by negative literals (`a ¬x = a - a x`). -/
private def terms (N : Names) :
    ℕ → List String → List (ℕ × ℤ) → ℤ → Option (List (ℕ × ℤ) × ℤ × List String)
  | 0, _, _, _ => none
  | fuel + 1, t :: ts, L, k =>
    if t == ">=" || t == "<=" || t == "=" || t == ";" then some (L, k, t :: ts)
    else
      -- A coefficient and a literal, or a literal with coefficient `1`.
      let (a, rest) := match int? t with
        | some a => (a, ts)
        | none => (1, t :: ts)
      match rest with
      | u :: rest =>
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

/-- The standard names, for formulas. -/
private def stdNames : Names := ⟨[], 0⟩

/-- The constraints of OPB lines, given as token lists. -/
private def opbLines : List (List String) → Option (List PBConstr)
  | [] => some []
  | [] :: ls => opbLines ls
  | (t :: ts) :: ls =>
    if t.startsWith "*" then opbLines ls
    else
      match constr stdNames (t :: ts), opbLines ls with
      | some (cs, [";"]), some F => some (cs ++ F)
      | _, _ => none

/-- An objective line `min: ∑ wᵢ ℓᵢ;`, given its tokens after `min:`. -/
private def objective (ts : List String) : Option Objective :=
  match terms stdNames (ts.length + 1) ts [] 0 with
  | some (L, k, [";"]) => some ⟨L, k⟩
  | _ => none

/-- An OPB instance: its constraints and its objective, if any. -/
structure OPB where
  /-- The constraints, an equality counting as two. -/
  constraints : List PBConstr
  /-- The objective to minimize, from the line `min: …;`. -/
  objective : Option Objective

/-- **An OPB instance**: comment lines starting with `*`, an optional objective line
`min: …;` before the constraints, and one constraint per line. -/
def parseOPB (s : String) : Option OPB :=
  let lines := ((s.splitOn "\n").map tokens).filter fun l =>
    match l.head? with
    | none => false
    | some t => !t.startsWith "*"
  match lines with
  | ("min:" :: ts) :: ls =>
    (objective ts).bind fun f => (opbLines ls).map (⟨·, some f⟩)
  | ls => (opbLines ls).map (⟨·, none⟩)

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
  let lines := (s.splitOn "\n").map tokens |>.filter fun l => l.head? != some "c"
  match lines with
  | ["p", "cnf", V, C] :: body =>
    match V.toNat?, C.toNat? with
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
  | t :: "*" :: ts => (t.toNat?).bind fun k => consOp (.mul k) (polOps N ts)
  | t :: "d" :: ts => (t.toNat?).bind fun k => consOp (.div k) (polOps N ts)
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

/-- A proof goal label: `#1`, `#2` (the objective) or a constraint number. -/
private def goalId (t : String) : Option GoalId :=
  if t == "#1" then some .self else if t == "#2" then some .obj else (id? t).map .db

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

/-- The items of a `red` subproof, up to its closing `qed`. -/
private def redItems (N : Names) : ℕ → List String → Option (List RedItem × List String)
  | 0, _ => none
  | fuel + 1, "proofgoal" :: g :: ts =>
    (goalId g).bind fun g =>
      match steps N fuel ts with
      | some (sub, rest) =>
        (qedId rest).bind fun (q, rest) =>
          (redItems N fuel rest).map fun (items, rest) => (.goal g sub q :: items, rest)
      | none => none
  | _ + 1, "qed" :: ts => some ([], "qed" :: ts)
  | fuel + 1, ts =>
    match step N fuel ts with
    | some (s, rest) => (redItems N fuel rest).map fun (items, rest) => (.step s :: items, rest)
    | none => none

/-- A top-level step: a `red` step, a deletion, `core id`, `strengthening_to_core`, solution
logging, or an implicational step. These steps other than the implicational ones are top-level
only: subproof scopes are specified in §5.5 of the format documentation, `core id` in §5.1,
strengthening-to-core mode in §5.6, and the kernel deletions in §5.7.1. A checked deletion
`delc id : ω [: subproof … qed [delc] [: n]];` deletes one constraint. -/
private def topStep (N : Names) (fuel : ℕ) : List String → Option (List TopStep × List String)
  | "red" :: ts =>
    match geq N ts with
    | some (c, ";" :: rest) => some ([.red c [] none none], rest)
    | some (c, ":" :: rest) =>
      match witness N rest with
      | some (ω, ";" :: rest) => some ([.red c ω none none], rest)
      | some (ω, ":" :: "subproof" :: rest) =>
        (redItems N fuel rest).bind fun (items, rest) =>
          (qedOpt rest).map fun (q, rest) => ([.red c ω (some items) q], rest)
      | _ => none
    | _ => none
  | "deld" :: ts =>
    match ids ts with
    | some (ns, ";" :: rest) => some ([.deld ns], rest)
    | _ => none
  | "delc" :: n :: ":" :: ts =>
    (id? n).bind fun i =>
      match witness N ts with
      | some (ω, ";" :: rest) => some ([.delcChecked i ω none none], rest)
      | some (ω, ":" :: "subproof" :: rest) =>
        (redItems N fuel rest).bind fun (items, rest) =>
          (qedOpt rest).map fun (q, rest) => ([.delcChecked i ω (some items) q], rest)
      | _ => none
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
  | "sol" :: ts =>
    match lits N ts with
    | some (ρ, ";" :: rest) => some ([.sol ρ], rest)
    | _ => none
  | "soli" :: ts =>
    match lits N ts with
    | some (ρ, ";" :: rest) => some ([.soli ρ], rest)
    | _ => none
  | "obji" :: v :: ";" :: rest => (int? v).map fun v => ([.obji v], rest)
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

/-- The conclusion section, after `conclusion`: `UNSAT : id`, `SAT`, or `BOUNDS lb : id ub`. -/
private def conclusion : List String → Option Conclusion
  | ["UNSAT", ":", q, ";"] => (id? q).map .unsat
  | ["SAT", ";"] => some .sat
  | ["BOUNDS", lb, ":", q, ub, ";"] =>
    (bound? lb).bind fun lb => (id? q).bind fun q => (bound? ub).map (.bounds lb q ·)
  | _ => none

/-- **A proof** in the supported fragment (kernel proofs, with `f N;` optional) for a formula
with `m` constraints over the variables below `nvars`. -/
def parseProof (m nvars : ℕ) (s : String) : Option RedProof :=
  let ts := tokens s
  let N := Names.ofTokens nvars ts
  let fuel := ts.length + 1
  match ts with
  | "pseudo-Boolean" :: "proof" :: "version" :: "3.0" :: rest =>
    let rest := match rest with
      | "f" :: n :: ";" :: rest => if n.toNat? == some m then some rest else none
      | rest => some rest
    rest.bind fun rest =>
      match topSteps N fuel rest with
      | some (ss, "output" :: "NONE" :: ";" :: "conclusion" :: rest) =>
        match rest.reverse with
        | ";" :: "proof" :: "pseudo-Boolean" :: "end" :: concl =>
          (conclusion concl.reverse).map (⟨ss, ·⟩)
        | _ => none
      | _ => none
  | _ => none

/-! ### The checkers -/

/-- The number of variables of a formula and an objective: one more than their largest
variable. -/
private def numVars (F : List PBConstr) (obj : Option Objective) : ℕ :=
  (F.flatMap PBConstr.terms).foldr (fun t m => max (PBConstr.termVar t + 1) m)
    ((obj.map (·.lin)).getD [] |>.foldr (fun e m => max (e.1 + 1) m) 0)

/-- **Check a proof for an OPB instance**, in the supported fragment: the conclusion, if the
proof is accepted. -/
def checkOPB (opb pbp : String) : Option Conclusion :=
  (parseOPB opb).bind fun I =>
    (parseProof I.constraints.length (numVars I.constraints I.objective) pbp).bind fun P =>
      if checkRed I.constraints I.objective P then some P.conclusion else none

/-- **Check a proof for a DIMACS CNF formula**, in the supported fragment: the conclusion, if
the proof is accepted. -/
def checkDIMACS (cnf pbp : String) : Option Conclusion :=
  (parseDIMACS cnf).bind fun φ =>
    (parseProof φ.length (numVars (φ.map Clause.toPB) none) pbp).bind fun P =>
      if checkRed (φ.map Clause.toPB) none P then some P.conclusion else none

private theorem exists_checkRed_of_checkOPB {opb pbp : String} {c : Conclusion}
    (h : checkOPB opb pbp = some c) :
    ∃ I P, parseOPB opb = some I ∧ checkRed I.constraints I.objective P = true ∧
      P.conclusion = c := by
  simp only [checkOPB, Option.bind_eq_some_iff] at h
  obtain ⟨I, hI, P, -, h⟩ := h
  split at h
  · cases h
    exact ⟨I, P, hI, ‹_›, rfl⟩
  · cases h

/-- **Soundness of `UNSAT` for OPB text**: an accepted proof of `UNSAT` means the instance parses
and its constraints have no 0/1 solution. -/
theorem not_satisfiable_of_checkOPB {opb pbp : String} {q : ℕ}
    (h : checkOPB opb pbp = some (.unsat q)) :
    ∃ I, parseOPB opb = some I ∧ ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨I, P, hI, h, hc⟩ := exists_checkRed_of_checkOPB h
  exact ⟨I, hI, not_satisfiable_of_checkRed h hc⟩

/-- **Soundness of `SAT` for OPB text**: an accepted proof of `SAT` means the instance parses
and its constraints have a 0/1 solution. -/
theorem exists_satisfies_of_checkOPB {opb pbp : String} (h : checkOPB opb pbp = some .sat) :
    ∃ I, parseOPB opb = some I ∧ ∃ σ : ℕ → Bool, ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨I, P, hI, h, hc⟩ := exists_checkRed_of_checkOPB h
  exact ⟨I, hI, exists_satisfies_of_checkRed h hc⟩

/-- **Soundness of `BOUNDS` for OPB text**: an accepted proof of `BOUNDS lb : q ub` means the
instance parses with an objective `f`; every 0/1 solution `σ` of its constraints has a finite
`lb` with `lb ≤ f σ` (so for `lb = INF` there is no solution); and for a finite `ub` some
solution has objective at most `ub`. -/
theorem bounds_of_checkOPB {opb pbp : String} {lb ub : Option ℤ} {q : ℕ}
    (h : checkOPB opb pbp = some (.bounds lb q ub)) :
    ∃ I f, parseOPB opb = some I ∧ I.objective = some f ∧
      (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → ∃ l, lb = some l ∧ l ≤ f.eval σ) ∧
      ∀ u, ub = some u → ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ u := by
  obtain ⟨I, P, hI, hck, hc⟩ := exists_checkRed_of_checkOPB h
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
theorem satisfiable_of_checkDIMACS {cnf pbp : String} (h : checkDIMACS cnf pbp = some .sat) :
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
