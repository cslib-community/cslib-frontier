/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Output
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public import Std.Data.HashMap

/-!
# The augmented VeriPB proof format: syntax and parser

The abstract syntax of the augmented proof format of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023], version 3.0
(`Cslib.Logic.PL.VeriPB.Elab.AStep`), and a parser for it, for the elaborator
(`Cslib.Logic.PL.VeriPB.Elab`). Beyond the kernel format (§6.1 of the VeriPB/CakePB
documentation, 22 June 2026 edition), the syntax has the conveniences of the augmented format:
* constraint references that are relative (`-k`, the `k`-th most recent constraint) or labels
  (`@name`, defined by a label before a rule) (§5);
* the `pol` operations `c` (division in variable form), `m` and `n` (mixed integer rounding in
  variable and normalized form) and `-` (lowering the degree) (§5.2.1);
* `rup` without hints, or with hints read as a set (§5.2.1); `i` and `ia` with an optional
  premise (§5.2.2); `pbc` and `proofgoal` without a closing constraint (§5.2.1, §5.5);
* deletion by reference without a type (`del id`), by specification (`del spec`), by range
  (`del range`) and by level (`setlvl`, `wiplvl`) (§5.7.2); `core range` (§5.1);
* the debugging rules `e`, `eobj`, `eord_def`, `eord_loaded`, `epreserved` and `is_deleted`
  (§5.11), and the conclusion `UNSAT` without a constraint.

The parser is untrusted: the elaborator's output is checked by the kernel checker, so no property
of the parser is needed. It reads the bytes of the proof with a lexer modelled on that of
VeriPB 3.0.2: identifiers start with a letter, `_`, `@` or `$` and continue with letters,
digits and `_ [ ] { } ^ -`; `~`, `:`, `;` and `*` are tokens of their own; `%` starts a comment.

**Variables.** Names are read with the names of the instance (`Cslib.Logic.PL.VeriPB.Text.Names`,
for an OPB text `Cslib.Logic.PL.VeriPB.Text.opbNames`), as `Cslib.Logic.PL.VeriPB.Text.Names.var?`
reads them: a standard name `xN` (`Cslib.Logic.PL.VeriPB.Text.stdVar?`, so `x01` is not `x1`) below
the base is the variable `N - 1`, and a known other name has its number. Every other name of the
proof (`Cslib.Logic.PL.VeriPB.Text.isName`), a standard name from the base on included, is a new
variable, numbered from `Cslib.Logic.PL.VeriPB.Text.Names.next` in order of first appearance. The
names of the proof thus extend those of the instance (`Cslib.Logic.PL.VeriPB.Text.Names.Extends`),
and distinct names get distinct numbers.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Elab

/-- A constraint reference of the augmented format. -/
inductive Ref where
  /-- The constraint with this number. -/
  | abs (n : ℕ)
  /-- `-k`: the `k`-th most recent constraint, number `maxId + 1 - k`. -/
  | rel (k : ℕ)
  /-- A label `@name`. -/
  | label (s : String)
  deriving Inhabited, Repr

/-- A hint of an augmented `rup`: a constraint, or `~` for the negated constraint. -/
inductive AHint where
  /-- `~`. -/
  | neg
  /-- A constraint. -/
  | ref (r : Ref)
  deriving Repr

/-- An operation of an augmented `pol` step. -/
inductive AOp where
  /-- Push a constraint. -/
  | ref (r : Ref)
  /-- Push the literal axiom `ℓ ≥ 0`. -/
  | lit (l : Literal ℕ)
  /-- `+`. -/
  | add
  /-- `k *`. -/
  | mul (k : ℕ)
  /-- `k d`: division in normalized form. -/
  | div (k : ℕ)
  /-- `k c`: division in variable form. -/
  | vdiv (k : ℕ)
  /-- `k n`: mixed integer rounding in normalized form. -/
  | nmir (k : ℕ)
  /-- `k m`: mixed integer rounding in variable form. -/
  | vmir (k : ℕ)
  /-- `s`. -/
  | sat
  /-- `x w`. -/
  | weaken (v : ℕ)
  /-- `k -`: lower the degree by `k`. -/
  | minus (k : ℕ)
  deriving Repr

/-- A proof goal label of the augmented format. -/
inductive AGoal where
  /-- `#k`. -/
  | hash (k : ℕ)
  /-- A constraint of the database. -/
  | ref (r : Ref)
  deriving Repr

/-- A rule of the augmented format, with its subproofs. -/
inductive AStep where
  /-- `pol ops;` -/
  | pol (ops : List AOp)
  /-- `rup C [: hints];` -/
  | rup (c : PBConstr) (hints : Option (List AHint))
  /-- `pbc C [: subproof … qed [: id]];` -/
  | pbc (c : PBConstr) (sub : Option (List AStep)) (qed : Option Ref)
  /-- `i C [: id];` (`add = false`) or `ia C [: id];` (`add = true`). -/
  | imp (c : PBConstr) (add : Bool) (hint : Option Ref)
  /-- `e C [: id];` -/
  | equal (c : PBConstr) (hint : Option Ref)
  /-- `is_deleted C;` -/
  | isDeleted (c : PBConstr)
  /-- `proofgoal g … qed [: id];` -/
  | goal (g : AGoal) (sub : List AStep) (qed : Option Ref)
  /-- `scope leq … end;` (`geq = false`) or `scope geq … end;`. -/
  | scope (geq : Bool) (items : List AStep)
  /-- `red C [: ω [: subproof … qed [: id]]];` (`dom = false`) or `dom …`. -/
  | red (dom : Bool) (c : PBConstr) (ω : Witness) (sub : Option (List AStep)) (qed : Option Ref)
  /-- `del id ids;` -/
  | delId (ids : List Ref)
  /-- `del spec C;` -/
  | delSpec (c : PBConstr)
  /-- `del range a b;` -/
  | delRange (a b : Ref)
  /-- `deld ids;` -/
  | deld (ids : List Ref)
  /-- `delc ids;` -/
  | delc (ids : List Ref)
  /-- `delc id : ω [: subproof … qed [: id]];` -/
  | delcChecked (id : Ref) (ω : Witness) (sub : Option (List AStep)) (qed : Option Ref)
  /-- `core id ids;` -/
  | coreId (ids : List Ref)
  /-- `core range a b;` -/
  | coreRange (a b : Ref)
  /-- `setlvl l;` -/
  | setlvl (l : ℤ)
  /-- `wiplvl l;` -/
  | wiplvl (l : ℤ)
  /-- `sol ρ;` (`0`), `soli ρ;` (`1`) or `solx ρ;` (`2`). -/
  | sol (kind : ℕ) (ρ : List (Literal ℕ))
  /-- `obji v;` -/
  | obji (v : ℤ)
  /-- `obju new g` (`diff = false`) or `obju diff g`, with an optional subproof. -/
  | obju (diff : Bool) (g : Objective) (sub : Option (List AStep))
  /-- `strengthening_to_core on;` or `off;` -/
  | stc (on : Bool)
  /-- `def_order name … end;`, in the kernel syntax. -/
  | defOrder (name : String) (O : Order) (spec : List SpecStep) (w : TransVars)
      (trans refl : OrderProof)
  /-- `load_order name z;` -/
  | loadOrder (name : String) (z : List (Literal ℕ))
  /-- `load_order;` -/
  | unloadOrder
  /-- `eord_def name …;` -/
  | eordDef (name : String) (O : Order)
  /-- `eord_loaded name z;` -/
  | eordLoaded (name : String) (z : List (Literal ℕ))
  /-- `preserved_add x : C` (`add = true`) or `preserved_rm x : C`, with an optional subproof. -/
  | presChange (add : Bool) (x : ℕ) (c : PBConstr) (sub : Option (List AStep))
  /-- `epreserved vars;` -/
  | epreserved (vs : List ℕ)
  /-- `eobj f;` -/
  | eobj (f : Objective)
  /-- A rule with a label before it. -/
  | labeled (l : String) (s : AStep)
  /-- A rule without effect (`f N;` checked, `start_time`, `end_time`). -/
  | noop
  deriving Repr, Inhabited

/-- The conclusion section of the augmented format: the kernel conclusions, with references,
and the constraint of `UNSAT` or of the lower bound of `BOUNDS` optional. -/
inductive AConclusion where
  /-- `UNSAT [: id]`. -/
  | unsat (q : Option Ref)
  /-- `SAT [: ρ]`. -/
  | sat (asg : Option (List (Literal ℕ)))
  /-- `BOUNDS lb [: id] ub [: ρ]`. -/
  | bounds (lb : Option ℤ) (q : Option Ref) (ub : Option ℤ) (asg : Option (List (Literal ℕ)))
  /-- `NONE`. -/
  | noClaim
  /-- `ENUMERATION_PARTIAL n`. -/
  | enumPartial (n : ℕ)
  /-- `ENUMERATION_COMPLETE n [: id]`. -/
  | enumComplete (n : ℕ) (q : Option Ref)
  deriving Repr

/-! ### The lexer -/

/-- The lexer and the variable names, as mutable references. -/
structure Lexer (σ : Type) where
  /-- The text. -/
  bytes : ByteArray
  /-- The standard names `xN` with `N - 1` below `base` are the variables below `base`
  (`Cslib.Logic.PL.VeriPB.Text.Names.base`). -/
  base : ℕ
  /-- The position of the next byte. -/
  pos : ST.Ref σ ℕ
  /-- Tokens read ahead. -/
  ahead : ST.Ref σ (Array String)
  /-- The start of the token read last, whose line error messages name. -/
  last : ST.Ref σ ℕ
  /-- The numbers of the other names (`Cslib.Logic.PL.VeriPB.Text.Names.others`). -/
  names : ST.Ref σ (Std.HashMap String ℕ)
  /-- The other names, those of the instance first, then those of the proof in order of first
  appearance; the `i`-th is the variable `base + i`. -/
  others : ST.Ref σ (Array String)

/-- The parser monad. -/
abbrev PM (σ : Type) := ExceptT String (ST σ)

namespace Lexer

variable {σ : Type}

private def isIdStart (c : UInt8) : Bool :=
  (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95 || c == 64 || c == 36

private def isIdChar (c : UInt8) : Bool :=
  (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || (c ≥ 48 && c ≤ 57) || c == 95 || c == 91 ||
    c == 93 || c == 123 || c == 125 || c == 94 || c == 45

private def isDigit (c : UInt8) : Bool := c ≥ 48 && c ≤ 57

/-- A new lexer for the text `s` of a proof, with the names `N` of its instance. -/
def new (s : String) (N : Text.Names) : ST σ (Lexer σ) := do
  let others := N.others.toArray
  let names := others.zipIdx.foldl (fun m (t, i) => m.insert t (N.base + i)) {}
  return ⟨s.toUTF8, N.base, ← ST.mkRef 0, ← ST.mkRef #[], ← ST.mkRef 0, ← ST.mkRef names,
    ← ST.mkRef others⟩

/-- The names read so far: those of the instance, extended by those of the proof. -/
def namesOf (L : Lexer σ) : ST σ Text.Names := return ⟨(← L.others.get).toList, L.base⟩

/-- The first variable without a name yet (`Cslib.Logic.PL.VeriPB.Text.Names.next`). -/
def nextVar (L : Lexer σ) : ST σ ℕ := return L.base + (← L.others.get).size

/-- A new variable, with a new name `_elabK`, for a variable the elaborator introduces. The
variables it introduces occur in no constraint (the `pol` operation `-` adds `k x` and `k ¬x`),
so a later name of the proof equal to it may share the variable. -/
def fresh (L : Lexer σ) : ST σ ℕ := do
  let m ← L.names.get
  let mut k := 0
  while m.contains s!"_elab{k}" do k := k + 1
  let v ← L.nextVar
  L.names.modify (·.insert s!"_elab{k}" v)
  L.others.modify (·.push s!"_elab{k}")
  return v

/-- The position of the first byte from `p` on that is not whitespace or in a comment. -/
private partial def skipWs (b : ByteArray) (p : ℕ) : ℕ :=
  if p < b.size then
    let c := b.get! p
    if c == 10 || c == 32 || c == 9 || c == 13 then skipWs b (p + 1)
    else if c == 37 then skipWs b (skipLine b p) else p
  else p
where
  /-- The position of the end of the line from `p`. -/
  skipLine (b : ByteArray) (p : ℕ) : ℕ :=
    if p < b.size && b.get! p != 10 then skipLine b (p + 1) else p

/-- The end of the run of bytes from `p` that satisfy `f`. -/
private partial def runEnd (b : ByteArray) (f : UInt8 → Bool) (p : ℕ) : ℕ :=
  if p < b.size && f (b.get! p) then runEnd b f (p + 1) else p

/-- The value of the decimal digits at `[p, e)`, from `acc`. -/
private partial def digitsVal (b : ByteArray) (p e acc : ℕ) : ℕ :=
  if p < e then digitsVal b (p + 1) e (10 * acc + (b.get! p - 48).toNat) else acc

/-- Read the next token from the text, or `""` at its end. -/
private def scan (L : Lexer σ) : ST σ String := do
  let b := L.bytes
  let mut p := skipWs b (← L.pos.get)
  L.last.set p
  if p ≥ b.size then L.pos.set p; return ""
  let start := p
  let c := b.get! p
  let single (n : ℕ) : ST σ String := do
    L.pos.set (start + n)
    return String.fromUTF8! (b.extract start (start + n))
  if isIdStart c then
    p := p + 1
    while p < b.size && isIdChar (b.get! p) do p := p + 1
    single (p - start)
  else if isDigit c || ((c == 43 || c == 45) && p + 1 < b.size && isDigit (b.get! (p + 1))) then
    p := p + 1
    while p < b.size && (isDigit (b.get! p) || b.get! p == 46) do p := p + 1
    single (p - start)
  else if c == 45 && p + 1 < b.size && b.get! (p + 1) == 62 then single 2
  else if c == 35 then
    p := p + 1
    while p < b.size && isDigit (b.get! p) do p := p + 1
    single (p - start)
  else if c == 60 || c == 61 || c == 62 then
    p := p + 1
    while p < b.size && (b.get! p == 60 || b.get! p == 61 || b.get! p == 62) do p := p + 1
    single (p - start)
  else single 1

/-- The next token, without consuming it. -/
private def peek (L : Lexer σ) : ST σ String := do
  let a ← L.ahead.get
  if h : 0 < a.size then return a[0]
  let t ← L.scan
  L.ahead.set #[t]
  return t

/-- The token after the next one, without consuming either. -/
private def peek2 (L : Lexer σ) : ST σ String := do
  let _ ← L.peek
  let a ← L.ahead.get
  if h : 1 < a.size then return a[1]
  let t ← L.scan
  L.ahead.set (a.push t)
  return t

/-- Consume the next token. -/
private def next (L : Lexer σ) : ST σ String := do
  let t ← L.peek
  L.ahead.modify (·.eraseIdx! 0)
  return t

/-- The current line, for error messages: that of the token read last. -/
private def lineNo (L : Lexer σ) : ST σ ℕ := do
  let p ← L.last.get
  return (L.bytes.extract 0 p).foldl (fun n c => if c == 10 then n + 1 else n) 1

end Lexer

/-! ### The parser -/

namespace Parse

variable {σ : Type}

/-- Fail with a message naming the current line. -/
def fail {α : Type} (L : Lexer σ) (msg : String) : PM σ α := do
  throw s!"line {← L.lineNo}: {msg}"

/-- Consume the token `t`, or fail. -/
private def expect (L : Lexer σ) (t : String) : PM σ Unit := do
  let u ← L.next
  if u != t then fail L s!"expected `{t}`, found `{u}`"

/-- A natural number. -/
private def nat? (t : String) : Option ℕ :=
  if t.isEmpty || !t.all Char.isDigit then none else t.toNat?

/-- An integer with an optional sign. -/
private def int? (t : String) : Option ℤ :=
  if t.startsWith "+" then nat? (t.drop 1).toString |>.map Int.ofNat
  else if t.startsWith "-" then nat? (t.drop 1).toString |>.map fun n => -(n : ℤ)
  else nat? t |>.map Int.ofNat

/-- The number of a variable name, as `Cslib.Logic.PL.VeriPB.Text.Names.var?` reads it with the
names read so far; a new name is the next variable. -/
private def var (L : Lexer σ) (t : String) : PM σ ℕ := do
  if let some v := Text.stdVar? t then
    if v < L.base then return v
  let m ← L.names.get
  match m[t]? with
  | some v => return v
  | none =>
    if !Text.isName t then fail L s!"expected a variable, found `{t}`"
    let v ← L.nextVar
    L.names.modify (·.insert t v)
    L.others.modify (·.push t)
    return v

/-- A literal `x` or `~ x`. -/
private def lit (L : Lexer σ) : PM σ (Literal ℕ) := do
  let t ← L.next
  if t == "~" then return (← var L (← L.next), false)
  return (← var L t, true)

/-- A constraint reference: a number, a relative number `-k`, or a label. -/
private def ref? (t : String) : Option Ref :=
  if t.startsWith "@" then some (.label t)
  else match int? t with
    | some (.ofNat (n + 1)) => some (.abs (n + 1))
    | some (.negSucc k) => some (.rel (k + 1))
    | _ => none

/-- A constraint reference, or fail. -/
private def ref (L : Lexer σ) : PM σ Ref := do
  let t ← L.next
  match ref? t with
  | some r => return r
  | none => fail L s!"expected a constraint reference, found `{t}`"

/-- References up to `;`, which is consumed. -/
private partial def refs (L : Lexer σ) : PM σ (List Ref) := do
  let t ← L.peek
  if t == ";" then let _ ← L.next; return []
  let r ← ref L
  return r :: (← refs L)

/-- References up to `;` or `:`, not consumed. -/
private partial def refsTo (L : Lexer σ) : PM σ (List Ref) := do
  let t ← L.peek
  if t == ";" || t == ":" then return []
  let r ← ref L
  return r :: (← refsTo L)

/-- Add `c x_v` to the linear form `lin`, whose entry for each variable `idx` gives. -/
@[inline] private def addEntry (lin : Array (ℕ × ℤ)) (idx : Std.HashMap ℕ ℕ) (v : ℕ) (c : ℤ) :
    Array (ℕ × ℤ) × Std.HashMap ℕ ℕ :=
  match idx[v]? with
  | some i => (lin.modify i fun e => (e.1, e.2 + c), idx)
  | none => (lin.push (v, c), idx.insert v lin.size)

/-- The literal whose `~` or name starts at `q`, read from the bytes: the variable, its sign and
the end of the literal; `none` if it is not a `~` followed by a name, or a name (the slow path
then reads it, or fails). A standard name below the base is read without making a string. -/
private def litAt (L : Lexer σ) (q : ℕ) : PM σ (Option (ℕ × Bool × ℕ)) := do
  let b := L.bytes
  let neg := q < b.size && b.get! q == 126
  let r := if neg then Lexer.skipWs b (q + 1) else q
  if !(r < b.size && Lexer.isIdStart (b.get! r) && b.get! r != 64) then return none
  let e := Lexer.runEnd b Lexer.isIdChar (r + 1)
  let d := Lexer.runEnd b Lexer.isDigit (r + 1)
  if b.get! r == 120 && d == e && r + 1 < e && b.get! (r + 1) != 48 then
    let n := Lexer.digitsVal b (r + 1) e 0
    if n - 1 < L.base then return some (n - 1, !neg, e)
  return some (← var L (String.fromUTF8! (b.extract r e)), !neg, e)

/-- The fast path of `terms`: read terms straight from the bytes from `p` on, while no token has
been read ahead, a coefficient being a plain integer followed by a literal. It stops before the
first token it does not read this way, which the slow path then reads. -/
private partial def termsFast (L : Lexer σ) (p : ℕ) (lin : Array (ℕ × ℤ)) (idx : Std.HashMap ℕ ℕ)
    (k : ℤ) : PM σ (ℕ × Array (ℕ × ℤ) × Std.HashMap ℕ ℕ × ℤ) := do
  let b := L.bytes
  let p := Lexer.skipWs b p
  if p ≥ b.size then return (p, lin, idx, k)
  let c := b.get! p
  let signed := (c == 43 || c == 45) && p + 1 < b.size && Lexer.isDigit (b.get! (p + 1))
  if Lexer.isDigit c || signed then
    let d := if signed then p + 1 else p
    let e := Lexer.runEnd b Lexer.isDigit d
    -- A number with a `.`, or followed by `;` or `:`, is left to the slow path.
    if e < b.size && b.get! e == 46 then return (p, lin, idx, k)
    let q := Lexer.skipWs b e
    if q < b.size && (b.get! q == 59 || b.get! q == 58) then return (p, lin, idx, k)
    let a : ℤ := if c == 45 then -(Lexer.digitsVal b d e 0 : ℤ) else Lexer.digitsVal b d e 0
    match ← litAt L q with
    | some (v, pos, e) =>
      let (lin, idx) := addEntry lin idx v (if pos then a else -a)
      termsFast L e lin idx (if pos then k else k + a)
    | none => return (p, lin, idx, k)
  else if c == 126 || (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95 || c == 36 then
    match ← litAt L p with
    | some (v, pos, e) =>
      let (lin, idx) := addEntry lin idx v (if pos then 1 else -1)
      termsFast L e lin idx (if pos then k else k + 1)
    | none => return (p, lin, idx, k)
  else return (p, lin, idx, k)

/-- The terms `a ℓ` of a constraint or objective up to a non-term token: the linear form, merged
by variable, and the constant moved out of negative literals. -/
private partial def terms (L : Lexer σ) : PM σ (Array (ℕ × ℤ) × ℤ) := do
  let (lin₀, idx₀, k₀) ← if (← L.ahead.get).isEmpty then do
      let (p, r) ← termsFast L (← L.pos.get) #[] {} 0
      L.pos.set p
      pure r
    else pure (#[], {}, 0)
  let mut lin := lin₀
  let mut idx := idx₀
  let mut k := k₀
  let mut go := true
  while go do
    let t ← L.peek
    let isLit := t == "~" || (!t.isEmpty && (t.front.isAlpha || t.front == '_' ||
      t.front == '$'))
    let a? := int? t
    if a?.isNone && !isLit then go := false
    else
      -- An integer followed by `;` or `:` is the constant of an objective.
      if a?.isSome then
        let u ← L.peek2
        if u == ";" || u == ":" then go := false; continue
        let _ ← L.next
      let a := a?.getD 1
      let l ← lit L
      let c : ℤ := if l.2 then a else -a
      if !l.2 then k := k + a
      (lin, idx) := addEntry lin idx l.1 c
  return (lin, k)

/-- A constraint `∑ aᵢ ℓᵢ ⋈ A` with `⋈` one of `>=`, `<=`: as `fromLinear` does in the kernel text
front end. -/
private def constr (L : Lexer σ) : PM σ PBConstr := do
  let (lin, k) ← terms L
  let rel ← L.next
  let d ← L.next
  let some A := int? d | fail L s!"expected a degree, found `{d}`"
  if rel == ">=" then return PBConstr.fromLinear lin.toList (A - k)
  else if rel == "<=" then return PBConstr.fromLinear (lin.toList.map fun e => (e.1, -e.2)) (k - A)
  else fail L s!"expected `>=` or `<=`, found `{rel}`"

/-- An objective `∑ wᵢ ℓᵢ [k]` up to `;` or `:`. -/
private def objective (L : Lexer σ) : PM σ Objective := do
  let (lin, k) ← terms L
  let t ← L.peek
  let c ← match int? t with
    | some c => do let _ ← L.next; pure c
    | none => pure 0
  return ⟨lin.toList.filter (·.2 != 0), k + c⟩

/-- Literals up to `;`, which is consumed, or up to `: v;`, the value `v` being ignored. -/
private partial def lits (L : Lexer σ) : PM σ (List (Literal ℕ)) := do
  let t ← L.peek
  if t == ";" then let _ ← L.next; return []
  if t == ":" then
    while (← L.next) != ";" do pure ()
    return []
  if t == "*" then fail L "solutions with shrunk variables are not supported"
  let l ← lit L
  return l :: (← lits L)

/-- Variables up to `;`, which is consumed. -/
private partial def vars (L : Lexer σ) : PM σ (List ℕ) := do
  let t ← L.next
  if t == ";" then return []
  let v ← var L t
  return v :: (← vars L)

/-- The pairs `x -> b` of a witness, up to `:` or `;`, not consumed. -/
private partial def witness (L : Lexer σ) : PM σ Witness := do
  let t ← L.peek
  if t == ":" || t == ";" then return []
  let x ← var L (← L.next)
  if (← L.peek) == "->" then let _ ← L.next
  let b ← L.peek
  let w ← if b == "0" then do let _ ← L.next; pure WVal.zero
    else if b == "1" then do let _ ← L.next; pure WVal.one
    else pure (WVal.lit (← lit L))
  return (x, w) :: (← witness L)

/-- The operations of a `pol` step, up to `;`, which is consumed, read token by token. -/
private partial def polOpsSlow (L : Lexer σ) : PM σ (List AOp) := do
  let t ← L.next
  if t == ";" then return []
  let op ← do
    if t == "+" then pure AOp.add
    else if t == "s" then pure AOp.sat
    else
      let u ← L.peek
      match nat? t, u with
      | some k, "*" => do let _ ← L.next; pure (AOp.mul k)
      | some k, "d" => do let _ ← L.next; pure (AOp.div k)
      | some k, "c" => do let _ ← L.next; pure (AOp.vdiv k)
      | some k, "n" => do let _ ← L.next; pure (AOp.nmir k)
      | some k, "m" => do let _ ← L.next; pure (AOp.vmir k)
      | some k, "-" => do let _ ← L.next; pure (AOp.minus k)
      | _, _ =>
        match ref? t with
        | some r => pure (AOp.ref r)
        | none =>
          if t == "~" then pure (AOp.lit (← var L (← L.next), false))
          else
            let v ← var L t
            if (← L.peek) == "w" then let _ ← L.next; pure (AOp.weaken v)
            else pure (AOp.lit (v, true))
  return op :: (← polOpsSlow L)

/-- The fast path of `polOps`: read operations straight from the bytes from `p` on, while no token
has been read ahead: `+`, `s`, `k *`, `k d`, `k c`, `k n`, `k m`, `k -`, and the references
`k` and `-k`, `k > 0`; whether the closing `;` was read. It stops before the first other token,
which the slow path then reads. -/
private partial def polFast (L : Lexer σ) (p : ℕ) (ops : Array AOp) :
    ST σ (ℕ × Array AOp × Bool) := do
  let b := L.bytes
  let p := Lexer.skipWs b p
  if p ≥ b.size then return (p, ops, false)
  let c := b.get! p
  let at? (q : ℕ) : UInt8 := if q < b.size then b.get! q else 0
  if c == 59 then
    L.last.set p
    return (p + 1, ops, true)
  if c == 43 && !Lexer.isDigit (at? (p + 1)) then return ← polFast L (p + 1) (ops.push .add)
  if c == 115 && !Lexer.isIdChar (at? (p + 1)) then return ← polFast L (p + 1) (ops.push .sat)
  let neg := c == 45 && Lexer.isDigit (at? (p + 1))
  if !(Lexer.isDigit c || neg) then return (p, ops, false)
  let d := if neg then p + 1 else p
  let e := Lexer.runEnd b Lexer.isDigit d
  if at? e == 46 then return (p, ops, false)
  let k := Lexer.digitsVal b d e 0
  if k == 0 then return (p, ops, false)
  if neg then return ← polFast L e (ops.push (.ref (.rel k)))
  let q := Lexer.skipWs b e
  let o := at? q
  let single := !Lexer.isIdChar (at? (q + 1))
  let op? : Option AOp :=
    if o == 42 then some (.mul k)
    else if o == 100 && single then some (.div k)
    else if o == 99 && single then some (.vdiv k)
    else if o == 110 && single then some (.nmir k)
    else if o == 109 && single then some (.vmir k)
    else if o == 45 && !Lexer.isDigit (at? (q + 1)) && at? (q + 1) != 62 then some (.minus k)
    else none
  match op? with
  | some op => polFast L (q + 1) (ops.push op)
  | none => polFast L e (ops.push (.ref (.abs k)))

/-- The operations of a `pol` step up to `;`, which is consumed. -/
private partial def polOps (L : Lexer σ) : PM σ (List AOp) := do
  if (← L.ahead.get).isEmpty then
    let (p, ops, done) ← polFast L (← L.pos.get) #[]
    L.pos.set p
    if done then return ops.toList
    return ops.toList ++ (← polOpsSlow L)
  polOpsSlow L

/-- RUP hints up to `;`, which is consumed. -/
private partial def hints (L : Lexer σ) : PM σ (List AHint) := do
  let t ← L.peek
  if t == ";" then let _ ← L.next; return []
  if t == "~" then let _ ← L.next; return .neg :: (← hints L)
  let r ← ref L
  return .ref r :: (← hints L)

/-- An optional `: id` before `;`, both consumed. -/
private def optRef (L : Lexer σ) : PM σ (Option Ref) := do
  let t ← L.next
  if t == ";" then return none
  if t != ":" then fail L s!"expected `:` or `;`, found `{t}`"
  let r ← ref L
  expect L ";"
  return some r

/-- The end `qed [label] [: id];` of a subproof. -/
private def qed (L : Lexer σ) : PM σ (Option Ref) := do
  expect L "qed"
  let t ← L.peek
  if t != ":" && t != ";" then let _ ← L.next
  optRef L

/-- The end `end [words];` of a section. -/
private partial def endSection (L : Lexer σ) : PM σ Unit := do
  expect L "end"
  while (← L.next) != ";" do pure ()

/-! #### The kernel syntax inside `def_order` -/

mutual

/-- An absolute reference of the specification step whose negation has the augmented number `a`,
sent to its kernel number: `map` sends the earlier steps, and the constraints of this step (its
negation and those of its subproof) are numbered `off` higher in the kernel syntax. -/
private partial def remapRef (map : Std.HashMap ℕ ℕ) (a off : ℕ) : Ref → Ref
  | .abs n => .abs (if a ≤ n then n + off else (map[n]?).getD n)
  | r => r

/-- The constraint references of a step in a specification, whose negation has the augmented
number `a`, sent to kernel numbers (`remapRef`); relative references are kept. -/
private partial def remap (map : Std.HashMap ℕ ℕ) (a off : ℕ) : AStep → AStep
  | .pol ops => .pol (ops.map fun (o : AOp) => match o with
    | .ref r => .ref (remapRef map a off r)
    | o => o)
  | .rup c (some hs) => .rup c (some (hs.map fun (h : AHint) => match h with
    | .ref r => .ref (remapRef map a off r)
    | h => h))
  | .pbc c sub q => .pbc c (sub.map (·.map (remap map a off))) (q.map (remapRef map a off))
  | .goal g sub q =>
    let g := match g with
      | .ref r => AGoal.ref (remapRef map a off r)
      | g => g
    .goal g (sub.map (remap map a off)) (q.map (remapRef map a off))
  | .labeled l s => .labeled l (remap map a off s)
  | s => s

/-- The local number of a reference inside `def_order`, the next number being `next` and the
labels of the section being `lbl`; an unknown label gets `0`, which numbers no constraint. -/
private partial def refNum (lbl : Std.HashMap String ℕ) (next : ℕ) : Ref → ℕ
  | .abs n => n
  | .rel k => next - k
  | .label l => lbl.getD l 0

/-- A step inside `def_order`, in the kernel syntax, numbered from `next`, with the labels `lbl`;
with the next number after it and the labels after it. The step derives the constraint before
that next number, which a label before the step names: the labels of a section are local to it
and visible after a subproof, as in `proof_lines` of VeriPB 3.0.2's parser. -/
private partial def toKernelStep (lbl : Std.HashMap String ℕ) (s : AStep) (next : ℕ) :
    Option (Step × ℕ × Std.HashMap String ℕ) :=
  match s with
  | .pol ops => (ops.mapM fun (o : AOp) => match o with
      | .ref r => some (PolOp.id (refNum lbl next r)) | .lit l => some (.lit l)
      | .add => some .add | .mul k => some (.mul k) | .div k => some (.div k)
      | .sat => some .sat | .weaken v => some (.weaken v) | _ => none).map
        fun ops => (.pol ops, next + 1, lbl)
  | .rup c none => some (.rupSearch c, next + 1, lbl)
  | .rup c (some hs) =>
    some (.rup c (hs.map fun (h : AHint) => match h with
      | .neg => .neg
      | .ref r => .id (refNum lbl next r)), next + 1, lbl)
  | .pbc c (some sub) q =>
    let (ks, n', lbl) := toKernelSteps lbl sub (next + 1)
    some (.pbc c ks ((q.map (refNum lbl n')).getD (n' - 1)), n' + 1, lbl)
  | .labeled l s => (toKernelStep lbl s next).map fun (k, n', lbl) => (k, n', lbl.insert l (n' - 1))
  | _ => none

/-- Steps inside `def_order`, numbered from `next`, with the labels `lbl`. -/
private partial def toKernelSteps (lbl : Std.HashMap String ℕ) (ss : List AStep) (next : ℕ) :
    List Step × ℕ × Std.HashMap String ℕ :=
  ss.foldl (fun (acc, n, lbl) s => match toKernelStep lbl s n with
    | some (k, n', lbl') => (acc ++ [k], n', lbl')
    | none => (acc, n, lbl)) ([], next, lbl)

/-- The items of a subproof inside `def_order`, in the kernel syntax, numbered from `next`, with
the labels `lbl`: a `proofgoal` block's negated goal takes the next number. -/
private partial def toKernelItems (lbl : Std.HashMap String ℕ) (items : List AStep) (next : ℕ) :
    List RedItem × ℕ × Std.HashMap String ℕ :=
  items.foldl (fun (acc, n, lbl) s => match s with
    | .goal g sub q =>
      -- The goal is resolved before the subproof, whose labels name the closing constraint.
      let g := match g with
        | .hash k => GoalId.hash k
        | .ref r => GoalId.db (refNum lbl n r)
      let (ks, n', lbl') := toKernelSteps lbl sub (n + 1)
      (acc ++ [.goal g ks ((q.map (refNum lbl' n')).getD (n' - 1))], n', lbl')
    | s => match toKernelStep lbl s n with
      | some (k, n', lbl') => (acc ++ [.step k], n', lbl')
      | none => (acc, n, lbl)) ([], next, lbl)

end

mutual

/-- A rule, with a label before it, if any; `none` at `output`, `qed` and `end`, which are not
consumed. -/
partial def step (L : Lexer σ) : PM σ (Option AStep) := do
  let t ← L.peek
  if t.startsWith "@" && t.length > 1 then
    let _ ← L.next
    match ← step L with
    | some s => return some (.labeled t s)
    | none => fail L "a label must precede a rule"
  if t == "output" || t == "qed" || t == "end" || t == "" || t == "conclusion" then return none
  let _ ← L.next
  match t with
  | "pol" => return some (.pol (← polOps L))
  | "rup" =>
    let c ← constr L
    let u ← L.next
    if u == ";" then return some (.rup c none)
    if u != ":" then fail L s!"expected `:` or `;`, found `{u}`"
    return some (.rup c (some (← hints L)))
  | "pbc" =>
    let c ← constr L
    let u ← L.next
    if u == ";" then return some (.pbc c none none)
    expect L "subproof"
    let sub ← steps L
    return some (.pbc c (some sub) (← qed L))
  | "i" | "ia" => return some (.imp (← constr L) (t == "ia") (← optRef L))
  | "e" => return some (.equal (← constr L) (← optRef L))
  | "is_deleted" =>
    let c ← constr L
    expect L ";"
    return some (.isDeleted c)
  | "proofgoal" =>
    let g ← L.next
    let g ← if g.startsWith "#" then
        match nat? (g.drop 1).toString with
        | some k => pure (AGoal.hash k)
        | none => fail L s!"bad proof goal `{g}`"
      else match ref? g with
        | some r => pure (AGoal.ref r)
        | none => fail L s!"bad proof goal `{g}`"
    let sub ← steps L
    return some (.goal g sub (← qed L))
  | "scope" =>
    let k ← L.next
    let items ← steps L
    endSection L
    return some (.scope (k == "geq") items)
  | "red" | "dom" =>
    let c ← constr L
    let u ← L.next
    if u == ";" then return some (.red (t == "dom") c [] none none)
    if u != ":" then fail L s!"expected `:` or `;`, found `{u}`"
    let ω ← witness L
    let u ← L.next
    if u == ";" then return some (.red (t == "dom") c ω none none)
    expect L "subproof"
    let sub ← steps L
    return some (.red (t == "dom") c ω (some sub) (← qed L))
  | "del" =>
    let k ← L.next
    if k == "id" then
      let ids ← refsTo L
      if (← L.next) == ";" then return some (.delId ids)
      let [i] := ids | fail L "a checked deletion deletes one constraint"
      let ω ← witness L
      let u ← L.next
      if u == ";" then return some (.delcChecked i ω none none)
      expect L "subproof"
      let sub ← steps L
      return some (.delcChecked i ω (some sub) (← qed L))
    if k == "spec" then
      let c ← constr L
      expect L ";"
      return some (.delSpec c)
    if k == "range" then
      let a ← ref L
      let b ← ref L
      expect L ";"
      return some (.delRange a b)
    fail L s!"unknown deletion `del {k}`"
  | "deld" => return some (.deld (← refs L))
  | "delc" =>
    if (← L.peek2) == ":" then
      let i ← ref L
      expect L ":"
      let ω ← witness L
      let u ← L.next
      if u == ";" then return some (.delcChecked i ω none none)
      expect L "subproof"
      let sub ← steps L
      return some (.delcChecked i ω (some sub) (← qed L))
    return some (.delc (← refs L))
  | "core" =>
    let k ← L.next
    if k == "id" then return some (.coreId (← refs L))
    if k == "range" then
      let a ← ref L
      let b ← ref L
      expect L ";"
      return some (.coreRange a b)
    fail L s!"unknown rule `core {k}`"
  | "setlvl" | "wiplvl" =>
    let n ← L.next
    let some l := int? n | fail L s!"expected a level, found `{n}`"
    expect L ";"
    return some (if t == "setlvl" then .setlvl l else .wiplvl l)
  | "sol" | "soli" | "solx" =>
    return some (.sol (if t == "sol" then 0 else if t == "soli" then 1 else 2) (← lits L))
  | "obji" =>
    let n ← L.next
    let some v := int? n | fail L s!"expected a value, found `{n}`"
    expect L ";"
    return some (.obji v)
  | "obju" =>
    let k ← L.next
    let g ← objective L
    let u ← L.next
    if u == ";" then return some (.obju (k == "diff") g none)
    expect L "subproof"
    let sub ← steps L
    let _ ← qed L
    return some (.obju (k == "diff") g (some sub))
  | "strengthening_to_core" =>
    let k ← L.next
    expect L ";"
    return some (.stc (k == "on"))
  | "load_order" =>
    if (← L.peek) == ";" then let _ ← L.next; return some .unloadOrder
    let name ← L.next
    return some (.loadOrder name (← lits L))
  | "eord_loaded" =>
    let name ← L.next
    return some (.eordLoaded name (← lits L))
  | "def_order" => defOrder L
  | "eord_def" =>
    let name ← L.next
    let (O, _, _, _, _) ← orderBody L false
    return some (.eordDef name O)
  | "preserved_add" | "preserved_rm" =>
    let x ← var L (← L.next)
    expect L ":"
    let c ← constr L
    let u ← L.next
    if u == ";" then return some (.presChange (t == "preserved_add") x c none)
    expect L "subproof"
    let sub ← steps L
    let _ ← qed L
    return some (.presChange (t == "preserved_add") x c (some sub))
  | "epreserved" => return some (.epreserved (← vars L))
  | "eobj" =>
    let f ← objective L
    expect L ";"
    return some (.eobj f)
  | "f" =>
    while (← L.next) != ";" do pure ()
    return some .noop
  | "start_time" | "end_time" =>
    while (← L.next) != ";" do pure ()
    return some .noop
  | _ => fail L s!"unsupported rule `{t}`"

/-- Rules up to `output`, `qed`, `end` or `conclusion`. -/
private partial def steps (L : Lexer σ) : PM σ (List AStep) := do
  let mut acc : Array AStep := #[]
  repeat
    match ← step L with
    | some s => acc := acc.push s
    | none => break
  return acc.toList

/-- `def_order name …`, after the keyword. -/
private partial def defOrder (L : Lexer σ) : PM σ (Option AStep) := do
  let name ← L.next
  let (O, sp, w, tp, rp) ← orderBody L true
  return some (.defOrder name O sp w tp rp)

/-- The body of `def_order` (`full = true`) or `eord_def` after the name, up to and including
its `end`. The subproofs are in the kernel syntax, with local numbers: the specification is
numbered from `1`, the transitivity proof after its premises, and the reflexivity proof after the
transitivity proof and its premises (`Cslib.Logic.PL.VeriPB.Order.defCheck`). -/
private partial def orderBody (L : Lexer σ) (full : Bool) :
    PM σ (Order × List SpecStep × TransVars × OrderProof × OrderProof) := do
  expect L "vars"
  expect L "left"
  let u ← vars L
  expect L "right"
  let v ← vars L
  let a ← if (← L.peek) == "aux" then do let _ ← L.next; vars L else pure []
  endSection L
  let mut spec : Array PBConstr := #[]
  let mut sps : Array (Option String × Witness × Option (List AStep) × Option Ref) := #[]
  if (← L.peek) == "spec" then
    let _ ← L.next
    while (← L.peek) != "end" do
      if full then
        let t ← L.peek
        let lab ← if t.startsWith "@" && t.length > 1 then do let _ ← L.next; pure (some t)
          else pure none
        expect L "red"
        let c ← constr L
        expect L ":"
        let ω ← witness L
        let u ← L.next
        if u == ";" then sps := sps.push (lab, ω, none, none)
        else
          expect L "subproof"
          let sub ← steps L
          let q ← qed L
          sps := sps.push (lab, ω, some sub, q)
        spec := spec.push c
      else
        spec := spec.push (← constr L)
        expect L ";"
    endSection L
  expect L "def"
  let mut defn : Array PBConstr := #[]
  while (← L.peek) != "end" do
    defn := defn.push (← constr L)
    expect L ";"
  endSection L
  let O : Order := ⟨u, v, a, spec.toList, defn.toList⟩
  if !full then
    endSection L
    return (O, [], ⟨[], [], []⟩, ⟨[], none⟩, ⟨[], none⟩)
  expect L "transitivity"
  expect L "vars"
  expect L "fresh_right"
  let w ← vars L
  let (b, c) ← if (← L.peek) == "fresh_aux_1" then do
      let _ ← L.next
      let b ← vars L
      expect L "fresh_aux_2"
      pure (b, ← vars L)
    else pure ([], [])
  endSection L
  let (tItems, tq) ← orderProof L
  endSection L
  let (rItems, rq) ← if (← L.peek) == "reflexivity" then do
      let _ ← L.next
      let rp ← orderProof L
      endSection L
      pure rp
    else pure ([], none)
  endSection L
  -- Convert to the kernel syntax with the local numbering. Every specification step gets a
  -- subproof, as CakePB requires, so its negation takes a kernel number but no augmented one:
  -- `map` sends augmented numbers in the specification to kernel numbers. The specification, the
  -- transitivity proof and the reflexivity proof each have their own labels, which name kernel
  -- numbers, as in `order_spec` and `order_proof` of VeriPB 3.0.2's parser.
  let mut a := 1
  let mut n := 1
  let mut map : Std.HashMap ℕ ℕ := {}
  let mut lbl : Std.HashMap String ℕ := {}
  let mut ksp : Array SpecStep := #[]
  for (lab, ω, sub, q) in sps do
    match sub with
    | none =>
      ksp := ksp.push ⟨ω, some [], none⟩
      map := map.insert a (n + 1)
      if let some l := lab then lbl := lbl.insert l (n + 1)
      a := a + 1
      n := n + 2
    | some sub =>
      let sub := sub.map (remap map a (n - a))
      let (items, n', lbl') := toKernelItems lbl sub (n + 1)
      ksp := ksp.push ⟨ω, some items, q.map (fun r => refNum lbl' n' (remapRef map a (n - a) r))⟩
      map := map.insert (a + (n' - n)) n'
      lbl := lbl'
      if let some l := lab then lbl := lbl.insert l n'
      a := a + (n' - n) + 1
      n := n' + 1
  let (ti, tn, tl) := toKernelItems {} tItems (3 * spec.size + 2 * defn.size + 1)
  let tp : OrderProof := ⟨ti, tq.map (refNum tl tn)⟩
  let (ri, rn, rl) := toKernelItems {} rItems (tn + spec.size)
  let rp : OrderProof := ⟨ri, rq.map (refNum rl rn)⟩
  return (O, ksp.toList, ⟨w, b, c⟩, tp, rp)

/-- A `proof … qed [: id];` block of an order. -/
private partial def orderProof (L : Lexer σ) : PM σ (List AStep × Option Ref) := do
  expect L "proof"
  let items ← steps L
  let q ← qed L
  return (items, q)

end

/-- A bound of `BOUNDS`: an integer, or `INF`. -/
private def bound (L : Lexer σ) : PM σ (Option ℤ) := do
  let t ← L.next
  if t == "INF" then return none
  match int? t with
  | some v => return some v
  | none => fail L s!"expected a bound, found `{t}`"

/-- A natural number, the count of an `ENUMERATION` conclusion. -/
private def count (L : Lexer σ) : PM σ ℕ := do
  let t ← L.next
  match nat? t with
  | some n => return n
  | none => fail L s!"expected a number, found `{t}`"

/-- An optional assignment `: ρ` before `;`, both consumed. -/
private def asgOpt (L : Lexer σ) : PM σ (Option (List (Literal ℕ))) := do
  let t ← L.next
  if t == ";" then return none
  if t != ":" then fail L s!"expected `:` or `;`, found `{t}`"
  return some (← lits L)

/-- The output section (`none` for `NONE`, else the guarantee and `FILE` (`true`) or `IMPLICIT`),
the conclusion and the end of the proof. -/
def tail (L : Lexer σ) : PM σ (Option (Guarantee × Bool) × AConclusion) := do
  expect L "output"
  let g ← L.next
  let sec ← if g == "NONE" then pure none else do
    let k ← L.next
    let g ← match g with
      | "DERIVABLE" => pure Guarantee.derivable
      | "EQUISATISFIABLE" => pure .equisatisfiable
      | "EQUIOPTIMAL" => pure .equioptimal
      | "EQUIENUMERABLE" => pure .equienumerable
      | _ => fail L s!"unknown guarantee `{g}`"
    pure (some (g, k == "FILE"))
  if (← L.peek) != ";" then let _ ← L.next
  expect L ";"
  expect L "conclusion"
  let k ← L.next
  let concl ← match k with
    | "NONE" => do expect L ";"; pure AConclusion.noClaim
    | "UNSAT" => pure (.unsat (← optRef L))
    | "SAT" => pure (.sat (← asgOpt L))
    | "BOUNDS" => do
      let lb ← bound L
      let q ← if (← L.peek) == ":" then do let _ ← L.next; pure (some (← ref L)) else pure none
      let ub ← bound L
      pure (.bounds lb q ub (← asgOpt L))
    | "ENUMERATION_PARTIAL" => do
      let n ← count L
      expect L ";"
      pure (.enumPartial n)
    | "ENUMERATION_COMPLETE" => do
      let n ← count L
      pure (.enumComplete n (← optRef L))
    | _ => fail L s!"unknown conclusion `{k}`"
  expect L "end"
  expect L "pseudo-Boolean"
  expect L "proof"
  if (← L.peek) == ";" then let _ ← L.next
  return (sec, concl)

/-- The header `pseudo-Boolean proof version 3.0`, and `f N;` if present: `N`. -/
def header (L : Lexer σ) : PM σ (Option ℕ) := do
  expect L "pseudo-Boolean"
  expect L "proof"
  expect L "version"
  let v ← L.next
  if v != "3.0" then fail L s!"unsupported version `{v}`"
  if (← L.peek) == "f" then
    let _ ← L.next
    let t ← L.peek
    let n := nat? t
    if n.isSome then let _ ← L.next
    expect L ";"
    return n
  return none

end Parse

end Cslib.Logic.PL.VeriPB.Elab

end
