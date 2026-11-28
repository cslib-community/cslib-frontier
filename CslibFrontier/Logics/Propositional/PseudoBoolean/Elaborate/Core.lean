/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Propagate
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Syntax
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Print

/-!
# An elaborator from the augmented to the kernel VeriPB format

`Cslib.Logic.PL.VeriPB.Elab.elaborate` reads a proof in the augmented format of VeriPB
[Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023], version 3.0
(`Cslib.Logic.PL.VeriPB.Elab.AStep`), and produces a kernel proof
(`Cslib.Logic.PL.VeriPB.RedProof`) for the checker `Cslib.Logic.PL.VeriPB.checkRed`, as the
elaborator of the VeriPB tool does (`veripb --elaborate`, version 3.0.2, crate `veripb-rules`,
module `elaboration`). It is untrusted: its output is checked by the kernel checker, and of its
parts only the propagation engine is proved sound so far
(`Cslib.Logic.PL.VeriPB.Elab.Engine.Built.rupHints_sound`). It keeps its own database, with the
number each constraint has in the augmented proof and the number it gets in the kernel proof,
which differ once a rule elaborates into several kernel steps; references are translated through
it. Section numbers below are those of the VeriPB/CakePB documentation, 22 June 2026 edition.

**Elaboration of the augmented rules.**
* `pol` (§5.2.1). The kernel operations are kept. `k -` lowers the degree by adding `k x` and
  `k ¬x` for a variable `x` not in the constraint. `k c` (division in variable form) first adds
  `(a mod k) x` for each term `a ¬x`, which makes the coefficients of negative literals multiples
  of `k`, and then divides in normalized form. A mixed-integer-rounding cut `k n` or `k m`
  becomes a `pbc` step for the cut `M`, whose subproof adds the constraint, weakened up to
  multiples of `k` on the terms whose remainder is at least that `r` of the degree, to `¬M`,
  divides by `k - r`, and adds `r` times the result to `¬M`, a contradiction.
* `rup` without hints (§5.2.1): the hints come from the propagation engine
  (`Cslib.Logic.PL.VeriPB.Elab.Engine.rupHints`); with hints, read as a set, they are propagated
  to a fixpoint and replayed as an ordered list.
* `i` and `ia` (§5.2.2): strong syntactic implication, as VeriPB 3.0.2 checks it; `ia` becomes a
  `pol` step that weakens the premise, lowers its degree, saturates and adds literal axioms.
  `i` adds nothing.
* `del id`, `del spec`, `del range`, `setlvl` and `wiplvl` (§5.7.2, §5.7.3): the multiset
  semantics with kill counters of §5.7.3, each deletion becoming `deld` or the unchecked `delc`
  by the type of the constraint. `core range` (§5.1) becomes `core id`.
* The debugging rules `e`, `eobj` and `is_deleted` (§5.11) are checked here and dropped;
  `eord_def`, `eord_loaded` and `epreserved` are kernel rules and are kept. `ea C : j`, VeriPB 2's
  `e` that adds the constraint found, becomes the `pol` step `j`, a copy of it.
* Relative references and labels (§5) are resolved, the labels of the instance included, and
  those inside `def_order` local to its specification, transitivity proof and reflexivity proof,
  as in VeriPB 3.0.2; `pbc`, `proofgoal` and `UNSAT` without a closing constraint get the most
  recent contradiction in scope, and a `proofgoal` without one a hinted `rup` of the
  contradiction `0 ≥ 1` if propagation finds it.
* A logged solution is extended by propagation and completed with the remaining variables of the
  database false (§5.8).

The other rules are kernel rules; their subproofs are elaborated in turn. The goals of `red`,
`dom`, a checked deletion, `obju` and the changes of the preserved set that the kernel format does
not autoprove (§5.5.1) but the augmented format does (§5.5.2) get `proofgoal` blocks closed by a
hinted `rup`, or by the sum of the negated goal and a constraint of the database equal to it, or
by syntactic implication, as in VeriPB 3.0.2: from the additional premise, from `D` for the goal
`D|ω`, or from a constraint of the database once the assignment that the database propagates is
substituted into it and into the goal, the block then deriving that assignment by a hinted
`rup`. The goals that must be derived from the core set alone (§5.7.1, §5.9, §5.10) use a
propagation engine holding only the core set. Every `red`, `dom`, checked deletion, `obju` and
change of the preserved set gets a subproof, possibly empty, as CakePB's parser requires.

**Trimming.** As VeriPB's elaborator does, the kernel proof keeps only the top-level `pol` and
`rup` steps that the rest of the proof uses (by a private pass, `trim`), except when
the core set is compared with a formula (an output section) or receives every constraint
(`strengthening_to_core on`, `load_order`). Constraints are computed in canonical form in linear
time (by private functions, `fadd`, …), with the results of the kernel's rules up to the
order of terms. On the parser's constraints, whose coefficients are positive and on distinct
variables, `Cslib.Logic.PL.VeriPB.Elab.normalizeParsed` and
`Cslib.Logic.PL.VeriPB.Elab.negateParsed` are the kernel's normalization and negation
(`Cslib.Logic.PL.VeriPB.Elab.normalizeParsed_eq`, `Cslib.Logic.PL.VeriPB.Elab.negateParsed_eq`).

**Totality.** Every function of the elaborator, its parser and its propagation engine is total,
by structural or well-founded recursion. The loops over the proof text and over the trail of the
engine take fuel, chosen above the number of bytes of the text and the number of literal codes:
each round consumes a token or a trail entry, so the fuel does not run out. Its state, that of
the lexer and of the propagation engine included, is a value threaded through a state monad and
updated in place while it is uniquely referenced, not a mutable reference in `ST`, whose
operations are opaque to proofs. So `Cslib.Logic.PL.VeriPB.Elab.elaborate` is a function with
equations, as proofs of its faithfulness and completeness against the declarative semantics of
the augmented format (`Cslib.Logic.PL.VeriPB.Elab.AugValid`, for the clausal and `pol` fragment)
need; both remain open (#8782).

**Not elaborated**: `rup` without hints inside `def_order` (the kernel checker accepts it, as
`Cslib.Logic.PL.VeriPB.Step.rupSearch`; CakePB does not), solutions with shrunk variables
(`solx *x`), the unchecked assertion `a`, reified constraints in proofs, and output sections
given as a file.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Elab

open PBConstr

/-- A term of a canonical form: a variable, the sign of its literal, and a coefficient. -/
private structure KTerm where
  /-- The variable. -/
  var : ℕ
  /-- The literal is positive. -/
  pos : Bool
  /-- The coefficient. -/
  coeff : ℕ
  deriving DecidableEq, Hashable, Repr

/-- A canonical form of a constraint, for comparison up to the order of terms: its normalized
terms, sorted by variable, and its degree. -/
private abbrev Key := Array KTerm × ℕ

/-- The canonical form of a constraint: the normal form of `Cslib.Logic.PL.PBConstr.normalize`,
computed with a hash map, its terms sorted by variable. -/
private def keyOf (c : PBConstr) : Key := Id.run do
  let mut idx : Std.HashMap ℕ ℕ := {}
  let mut lin : Array (ℕ × ℤ) := #[]
  let mut d : ℤ := c.degree
  for t in c.terms do
    let a : ℤ := if termPos t then t.1 else -(t.1 : ℤ)
    if !termPos t then d := d - t.1
    match idx[termVar t]? with
    | some i => lin := lin.modify i fun e => (e.1, e.2 + a)
    | none => idx := idx.insert (termVar t) lin.size; lin := lin.push (termVar t, a)
  let mut ts : Array KTerm := #[]
  for e in lin do
    if e.2 > 0 then ts := ts.push ⟨e.1, true, e.2.toNat⟩
    else if e.2 < 0 then
      ts := ts.push ⟨e.1, false, (-e.2).toNat⟩
      d := d - e.2
  return (ts.qsort fun a b => a.var < b.var, d.toNat)

/-- `Cslib.Logic.PL.VeriPB.Elab.keyOf` of a constraint of the parser (`Parse.constr`), whose terms
have positive coefficients on distinct variables: its terms sorted by variable. -/
private def keyOfParsed (c : PBConstr) : Key :=
  ((c.terms.toArray.map fun t => (⟨termVar t, termPos t, t.1⟩ : KTerm)).qsort
    fun a b => a.var < b.var, c.degree)

/-- The constraint of a canonical form. -/
private def ofKey (k : Key) : PBConstr := ⟨k.1.toList.map fun t => (t.coeff, t.var, t.pos), k.2⟩

/-- A constraint of the elaborator's database. -/
private structure Entry where
  /-- The constraint, as the kernel stores it. -/
  c : PBConstr
  /-- Its kernel number. -/
  kid : ℕ
  /-- Its engine index. -/
  eidx : ℕ
  /-- It is in the database. -/
  alive : Bool
  /-- It is a core constraint. -/
  core : Bool
  /-- Its canonical form. -/
  key : Key

private instance : Inhabited Entry := ⟨⟨⟨[], 0⟩, 0, 0, false, false, (#[], 0)⟩⟩

/-- The state of the elaborator: a value, updated in place while it is uniquely referenced. -/
private structure Ext where
  /-- The state of the lexer. -/
  lex : LexState
  /-- The propagation engine. -/
  eng : Engine
  /-- The database, by augmented number; index `0` is unused. -/
  db : Array Entry
  /-- The next kernel number. -/
  kerNext : ℕ
  /-- The labels. -/
  labels : Std.HashMap String ℕ
  /-- For each canonical form, the live constraints with it and the kill counter of `del spec`
  (§5.7.3). -/
  specs : Std.HashMap Key (Array ℕ × ℕ)
  /-- The constraints tagged with each level (§5.7.2). -/
  levels : Std.HashMap ℤ (Array ℕ)
  /-- The current level. -/
  level : Option ℤ
  /-- The current objective. -/
  obj : Option Objective
  /-- The current preserved set. -/
  pres : Option (List ℕ)
  /-- The defined orders. -/
  orders : Std.HashMap String Order
  /-- The loaded order. -/
  order : Option LoadedOrder
  /-- Strengthening-to-core mode. -/
  tcb : Bool
  /-- The constraints containing each variable, live or not, for the goals of a witness. -/
  varOcc : Std.HashMap ℕ (Array ℕ)

/-- The elaborator monad. -/
private abbrev EM := EStateM String Ext

/-- Run a step of the parser, on the state of the lexer taken out of the state, so that it is
updated in place. -/
@[inline] private def liftPM {α : Type} (x : PM α) : EM α := fun
  | ⟨lex, eng, db, kerNext, labels, specs, levels, level, obj, pres, orders, order, tcb, varOcc⟩ =>
    match x lex with
    | .ok a lex =>
      .ok a ⟨lex, eng, db, kerNext, labels, specs, levels, level, obj, pres, orders, order, tcb,
        varOcc⟩
    | .error e lex =>
      .error e ⟨lex, eng, db, kerNext, labels, specs, levels, level, obj, pres, orders, order, tcb,
        varOcc⟩

private instance : MonadLift PM EM := ⟨liftPM⟩

/-- The elaborator's handle on the proof text, whose state is that of `EM`. -/
private structure St where
  /-- The lexer. -/
  L : Lexer

/-- A field of the elaborator's state. -/
private structure Field (α : Type) where
  /-- Read the field. -/
  read : Ext → α
  /-- Write the field. -/
  write : α → Ext → Ext

namespace Field

variable {α : Type}

/-- The value of the field. -/
@[inline] private def get (f : Field α) : EM α := fun e => .ok (f.read e) e

/-- Set the field. -/
@[inline] private def set (f : Field α) (a : α) : EM Unit := fun e => .ok () (f.write a e)

/-- Change the field. -/
@[inline] private def modify (f : Field α) (g : α → α) : EM Unit :=
  fun e => .ok () (f.write (g (f.read e)) e)

end Field

namespace St

/-- The field `db` of the state. -/
@[inline] private def db (_ : St) : Field (Array Entry) := ⟨(·.db), fun a e => { e with db := a }⟩

/-- The field `kerNext` of the state. -/
@[inline] private def kerNext (_ : St) : Field (ℕ) :=
    ⟨(·.kerNext), fun a e => { e with kerNext := a }⟩

/-- The field `labels` of the state. -/
@[inline] private def labels (_ : St) : Field (Std.HashMap String ℕ) :=
    ⟨(·.labels), fun a e => { e with labels := a }⟩

/-- The field `specs` of the state. -/
@[inline] private def specs (_ : St) : Field (Std.HashMap Key (Array ℕ × ℕ)) :=
    ⟨(·.specs), fun a e => { e with specs := a }⟩

/-- The field `levels` of the state. -/
@[inline] private def levels (_ : St) : Field (Std.HashMap ℤ (Array ℕ)) :=
    ⟨(·.levels), fun a e => { e with levels := a }⟩

/-- The field `level` of the state. -/
@[inline] private def level (_ : St) : Field (Option ℤ) :=
    ⟨(·.level), fun a e => { e with level := a }⟩

/-- The field `obj` of the state. -/
@[inline] private def obj (_ : St) : Field (Option Objective) :=
    ⟨(·.obj), fun a e => { e with obj := a }⟩

/-- The field `pres` of the state. -/
@[inline] private def pres (_ : St) : Field (Option (List ℕ)) :=
    ⟨(·.pres), fun a e => { e with pres := a }⟩

/-- The field `orders` of the state. -/
@[inline] private def orders (_ : St) : Field (Std.HashMap String Order) :=
    ⟨(·.orders), fun a e => { e with orders := a }⟩

/-- The field `order` of the state. -/
@[inline] private def order (_ : St) : Field (Option LoadedOrder) :=
    ⟨(·.order), fun a e => { e with order := a }⟩

/-- The field `tcb` of the state. -/
@[inline] private def tcb (_ : St) : Field (Bool) := ⟨(·.tcb), fun a e => { e with tcb := a }⟩

/-- The field `varOcc` of the state. -/
@[inline] private def varOcc (_ : St) : Field (Std.HashMap ℕ (Array ℕ)) :=
    ⟨(·.varOcc), fun a e => { e with varOcc := a }⟩

/-- Apply `f` to the propagation engine, taken out of the state, so that it is updated in place. -/
@[inline] private def withEng {α : Type} (_ : St) (f : Engine → Engine × α) : EM α := fun
  | ⟨lex, eng, db, kerNext, labels, specs, levels, level, obj, pres, orders, order, tcb, varOcc⟩ =>
    let (eng, a) := f eng
    .ok a ⟨lex, eng, db, kerNext, labels, specs, levels, level, obj, pres, orders, order, tcb,
      varOcc⟩

/-- Add a constraint to the engine (`Cslib.Logic.PL.VeriPB.Elab.Engine.add`). -/
@[inline] private def engAdd (S : St) (c : PBConstr) (h : Hint) : EM ℕ :=
  S.withEng (·.add c h)

/-- Delete a constraint from the engine (`Cslib.Logic.PL.VeriPB.Elab.Engine.kill`). -/
@[inline] private def engKill (S : St) (i : ℕ) : EM Unit := S.withEng fun e => (e.kill i, ())

/-- The hints of `rup` from the engine (`Cslib.Logic.PL.VeriPB.Elab.Engine.rupHints`). -/
@[inline] private def engRupHints (S : St) (neg : PBConstr) : EM (Option (Array Hint)) :=
  S.withEng (·.rupHints neg)

/-- Extend an assignment by the engine (`Cslib.Logic.PL.VeriPB.Elab.Engine.extend`). -/
@[inline] private def engExtend (S : St) (ls : List (Literal ℕ)) :
    EM (Option (Array (Literal ℕ))) :=
  S.withEng (·.extend ls)

/-- Put the engine `e` in the state, and return the one it replaces. -/
@[inline] private def swapEng (S : St) (e : Engine) : EM Engine := S.withEng fun e' => (e, e')

end St

namespace St

/-- Fail with a message naming the current line. -/
private def fail {α : Type} (S : St) (msg : String) : EM α := liftPM (Parse.fail S.L msg)

/-- Take the next kernel number. -/
private def takeKid (S : St) : EM ℕ := do
  let k ← S.kerNext.get
  S.kerNext.set (k + 1)
  return k

/-- The next augmented number. -/
private def augNext (S : St) : EM ℕ := return (← S.db.get).size

/-- Add a constraint, stored by the kernel as `c` under the kernel number `kid`: it takes the
next augmented number, which is returned. `top` tags it with the current level. Its canonical
form `key` is computed unless given. -/
private def add (S : St) (c : PBConstr) (kid : ℕ) (core top : Bool) (key? : Option Key := none) :
    EM ℕ := do
  let id ← S.augNext
  let eidx ← S.engAdd c (.id kid)
  let key := key?.getD (keyOf c)
  S.db.modify (·.push ⟨c, kid, eidx, true, core, key⟩)
  S.varOcc.modify fun m => c.terms.foldl (fun m t => m.alter (termVar t) fun
    | some ids => some (ids.push id)
    | none => some #[id]) m
  S.specs.modify fun m => m.alter key fun
    | some (ids, k) => some (ids.push id, k)
    | none => some (#[id], 0)
  if top then
    if let some l ← S.level.get then
      S.levels.modify fun m => m.alter l fun
        | some ids => some (ids.push id)
        | none => some #[id]
  return id

/-- The live entry with augmented number `id`. -/
private def entry (S : St) (id : ℕ) : EM Entry := do
  let db ← S.db.get
  match db[id]? with
  | some e => if e.alive && id != 0 then return e else S.fail s!"constraint {id} is deleted"
  | none => S.fail s!"no constraint {id}"

/-- The augmented number a reference names. -/
private def resolve (S : St) : Ref → EM ℕ
  | .abs n => return n
  | .rel k => do
    let n ← S.augNext
    if k ≤ n then return n - k else S.fail s!"bad relative reference -{k}"
  | .label l => do
    match (← S.labels.get)[l]? with
    | some n => return n
    | none => S.fail s!"unknown label {l}"

/-- The live entry a reference names. -/
private def entryOf (S : St) (r : Ref) : EM Entry := do S.entry (← S.resolve r)

/-- Remove the constraint `id` from the database, the engine and the canonical index. -/
private def drop (S : St) (id : ℕ) : EM Unit := do
  let e := (← S.db.get)[id]!
  if !e.alive then return
  S.engKill e.eidx
  S.db.modify (·.modify id ({ · with alive := false }))
  S.specs.modify fun m => m.alter e.key fun
    | some (ids, k) => some (ids.filter (· != id), k)
    | none => none

/-- Remove the constraints numbered from `start`, the local constraints of a subproof. -/
private def dropFrom (S : St) (start : ℕ) : EM Unit := do
  let n ← S.augNext
  for i in [start:n] do S.drop i

/-- A live constraint numbered below `start` equal to `G` up to the order of terms (a core
constraint if `core`). -/
private def findBelow (S : St) (start : ℕ) (core : Bool) (G : PBConstr) : EM (Option ℕ) := do
  let db ← S.db.get
  match (← S.specs.get)[keyOf G]? with
  | some (l, _) => return l.find? fun i => i < start && (!core || db[i]!.core)
  | none => return none

/-- Remove the constraints numbered from `start` and give their numbers back: the premises of a
goal proved automatically, which take no number in the augmented proof (§5.5). -/
private def popTo (S : St) (start : ℕ) : EM Unit := do
  S.dropFrom start
  S.db.modify (·.shrink start)

/-- The most recent live contradiction numbered from `start`, if any. -/
private def lastContra (S : St) (start : ℕ) : EM (Option ℕ) := do
  let db ← S.db.get
  for k in [0:db.size - start] do
    let i := db.size - 1 - k
    let e := db[i]!
    if e.alive && decide e.c.IsContradiction then return some i
  return none

/-- The hinted `rup` of the contradiction `0 ≥ 1`, if propagation finds it. -/
private def rupContra (S : St) : EM (Option (List Hint)) := do
  let c : PBConstr := ⟨[], 1⟩
  return (← S.engRupHints c.negate).map (·.toList)

/-- The kernel deletions of the augmented numbers `ids`, all live: `deld` of the derived ones
and the unchecked `delc` of the core ones (§5.7.1). -/
private def kernelDeletions (S : St) (ids : Array ℕ) : EM (Array TopStep) := do
  for i in ids do S.drop i
  -- Read after the deletions, which keep the kernel numbers and types: a copy of the database
  -- held across them would be copied by each.
  let db ← S.db.get
  let ds := ids.filter (!db[·]!.core) |>.map (db[·]!.kid)
  let cs := ids.filter (db[·]!.core) |>.map (db[·]!.kid)
  return (if ds.isEmpty then #[] else #[.deld ds.toList]) ++
    (if cs.isEmpty then #[] else #[.delc cs.toList])

/-- **Deletion by reference** of the augmented numbers `ids` (§5.7.2, §5.7.3): each is taken off
its canonical form; a form whose kill counter then reaches the number of its copies loses all of
them. -/
private def deleteRefs (S : St) (ids : List ℕ) : EM (Array TopStep) := do
  let mut out : Array ℕ := #[]
  let mut keys : Array Key := #[]
  for i in ids do
    let e ← S.entry i
    if out.contains i then S.fail s!"constraint {i} deleted twice"
    out := out.push i
    keys := keys.push e.key
    S.specs.modify fun m => m.alter e.key fun
      | some (l, k) => some (l.filter (· != i), k)
      | none => none
  for key in keys do
    match (← S.specs.get)[key]? with
    | some (l, k) =>
      if 0 < k && l.size ≤ k then
        out := out ++ l.filter (!out.contains ·)
        S.specs.modify (·.insert key (#[], 0))
    | none => pure ()
  S.kernelDeletions out

/-- **Deletion by specification** of `c` (§5.7.2, §5.7.3). -/
private def deleteSpec (S : St) (c : PBConstr) : EM (Array TopStep) := do
  let key := keyOfParsed c
  match (← S.specs.get)[key]? with
  | some (l, k) =>
    if l.isEmpty then S.fail "del spec: no such constraint"
    if l.size ≤ k + 1 then
      S.specs.modify (·.insert key (#[], 0))
      S.kernelDeletions l
    else
      S.specs.modify (·.insert key (l, k + 1))
      return #[]
  | none => S.fail "del spec: no such constraint"

end St

/-! ### Cutting planes -/

/-- The cutting-planes rules on canonical forms, with the results of the kernel checker's rules
(`Cslib.Logic.PL.PBConstr.add`, …) up to the order of terms, in linear time, where the kernel's
normalization is quadratic. On canonical forms the rules keep the terms sorted by variable:
addition merges them, cancelling opposite literals, and the other rules map or filter them. -/
private def canon (c : PBConstr) : PBConstr := ofKey (keyOf c)

/-- `Cslib.Logic.PL.PBConstr.normalize` of a constraint of the parser (`Parse.constr`), in linear
time: its terms have positive coefficients on distinct variables, and then the normal form is the
terms reversed, with the same degree (`Cslib.Logic.PL.VeriPB.Elab.normalizeParsed_eq`). -/
def normalizeParsed (c : PBConstr) : PBConstr := ⟨c.terms.reverse, c.degree⟩

/-- `Cslib.Logic.PL.PBConstr.negate` of a constraint of the parser, in linear time
(`Cslib.Logic.PL.VeriPB.Elab.negateParsed_eq`). -/
def negateParsed (c : PBConstr) : PBConstr :=
  ⟨c.terms.reverse.map fun t => (t.1, Std.Sat.Literal.negate t.2), coeffSum c.terms + 1 - c.degree⟩

/-- On a constraint with positive coefficients on distinct variables, as the parser produces,
`Cslib.Logic.PL.VeriPB.Elab.normalizeParsed` is the kernel's normalization. -/
theorem normalizeParsed_eq {c : PBConstr} (hd : (c.terms.map termVar).Nodup)
    (hpos : ∀ t ∈ c.terms, 0 < t.1) : normalizeParsed c = c.normalize :=
  (normalize_of_nodup hd hpos).symm

/-- On a constraint with positive coefficients on distinct variables, as the parser produces,
`Cslib.Logic.PL.VeriPB.Elab.negateParsed` is the kernel's negation. -/
theorem negateParsed_eq {c : PBConstr} (hd : (c.terms.map termVar).Nodup)
    (hpos : ∀ t ∈ c.terms, 0 < t.1) : negateParsed c = c.negate := by
  rw [negate, normalize_of_nodup hd hpos, negateParsed]
  simp [coeffSum, List.map_reverse, List.sum_reverse]

/-- The literal axiom `ℓ ≥ 0` (`Cslib.Logic.PL.PBConstr.litAxiom`), in canonical form. -/
private def litKey (l : Literal ℕ) : Key := (#[⟨l.1, l.2, 1⟩], 0)

/-- Merge the sorted terms of `x` from `i` and `y` from `j` into `out`, adding to `dec` what the
degree loses where opposite literals cancel: `a x + b ¬x = (a - b) x + b` for `a ≥ b`. -/
private def mergeTerms (x y : Array KTerm) (i j : ℕ) (out : Array KTerm) (dec : ℕ) :
    Array KTerm × ℕ :=
  if h : i < x.size then
    if h' : j < y.size then
      let p := x[i]
      let q := y[j]
      if p.var < q.var then mergeTerms x y (i + 1) j (out.push p) dec
      else if q.var < p.var then mergeTerms x y i (j + 1) (out.push q) dec
      else if p.pos == q.pos then
        mergeTerms x y (i + 1) (j + 1) (out.push ⟨p.var, p.pos, p.coeff + q.coeff⟩) dec
      else if q.coeff < p.coeff then
        mergeTerms x y (i + 1) (j + 1) (out.push ⟨p.var, p.pos, p.coeff - q.coeff⟩) (dec + q.coeff)
      else if p.coeff < q.coeff then
        mergeTerms x y (i + 1) (j + 1) (out.push ⟨q.var, q.pos, q.coeff - p.coeff⟩) (dec + p.coeff)
      else mergeTerms x y (i + 1) (j + 1) out (dec + p.coeff)
    else mergeTerms x y (i + 1) j (out.push x[i]) dec
  else if h' : j < y.size then mergeTerms x y i (j + 1) (out.push y[j]) dec
  else (out, dec)
termination_by x.size - i + (y.size - j)

/-- Addition, as `Cslib.Logic.PL.PBConstr.add`. -/
private def fadd (c d : Key) : Key :=
  let (ts, dec) := mergeTerms c.1 d.1 0 0 (.mkEmpty (c.1.size + d.1.size)) 0
  (ts, c.2 + d.2 - dec)

/-- Multiplication, as `Cslib.Logic.PL.PBConstr.mul`. -/
private def fmul (c : Key) (k : ℕ) : Key :=
  if k = 0 then (#[], 0) else (c.1.map fun t => { t with coeff := k * t.coeff }, k * c.2)

/-- Division by `k > 0`, as `Cslib.Logic.PL.PBConstr.div`. -/
private def fdiv (c : Key) (k : ℕ) : Key :=
  (c.1.map fun t => { t with coeff := ceilDiv t.coeff k }, ceilDiv c.2 k)

/-- Saturation, as `Cslib.Logic.PL.PBConstr.saturate`. -/
private def fsat (c : Key) : Key :=
  if c.2 = 0 then (#[], 0)
  else if c.1.all (·.coeff ≤ c.2) then c
  else (c.1.map fun t => if t.coeff ≤ c.2 then t else { t with coeff := c.2 }, c.2)

/-- Weakening, as `Cslib.Logic.PL.PBConstr.weaken`. -/
private def fweaken (c : Key) (v : ℕ) : Key :=
  (c.1.filter (·.var != v), c.2 - (c.1.filter (·.var == v)).foldl (· + ·.coeff) 0)

/-- The constraint is a contradiction: its coefficients sum to less than its degree. -/
private def Key.isContradiction (c : Key) : Bool := c.1.foldl (· + ·.coeff) 0 < c.2

/-- An operand of a `pol` step during elaboration: its constraint, as the kernel computes it up to
the order of terms, in canonical form, and the kernel operations that push it. -/
private structure PVal where
  /-- The constraint. -/
  k : Key
  /-- The kernel operations. -/
  ops : Array PolOp

private instance : Inhabited PVal := ⟨⟨(#[], 0), #[]⟩⟩

/-- The constraint of an operand. -/
private def PVal.c (v : PVal) : PBConstr := ofKey v.k

/-- One more than the largest variable of the constraint. -/
private def freshVar (c : PBConstr) : ℕ := c.terms.foldl (fun m t => max m (termVar t + 1)) 0

/-- `k -`: add `k x` and `k ¬x` for a variable `x` not in the constraint
(`Cslib.Logic.PL.VeriPB.Elab.St.lowerVar`). -/
private def lowerOps (v : PVal) (k x : ℕ) : PVal :=
  if k = 0 then v else
  let c₁ := fadd v.k (fmul (litKey (x, true)) k)
  ⟨fadd c₁ (fmul (litKey (x, false)) k),
    v.ops ++ #[.lit (x, true), .mul k, .add, .lit (x, false), .mul k, .add]⟩

/-- Add `b ℓ` for each pair `(ℓ, b)`, `b > 0`. -/
private def addAxioms (v : PVal) (ls : List (Literal ℕ × ℕ)) : PVal :=
  ls.foldl (fun v (l, b) => if b = 0 then v else
    ⟨fadd v.k (fmul (litKey l) b), v.ops ++ #[.lit l, .mul b, .add]⟩) v

/-- `k c`, division in variable form: make the coefficients of negative literals multiples of
`k`, then divide. -/
private def vdivOps (v : PVal) (k : ℕ) : PVal :=
  let v := addAxioms v (v.k.1.toList.reverse.filterMap fun t =>
    if t.pos then none else some ((t.var, true), t.coeff % k))
  ⟨fdiv v.k k, v.ops.push (.div k)⟩

/-- The mixed-integer-rounding cut of the normalized constraint `c` with divisor `d > 0`, in
normalized form (`vf = false`) or variable form (`vf = true`), as VeriPB 3.0.2 computes it
(`normalized_form_mir`, `variable_form_mir`): with `r` the remainder of the degree, the
coefficient `a` becomes `⌊a / d⌋ r + min (a mod d, r)` and the degree `⌈A / d⌉ r`. Returns the cut
and the literal axioms `(ℓ, b)` that raise the constraint to multiples of `d` on the terms whose
remainder is at least `r`; `none` when `r = 0`, the cut being trivial. -/
private def mir (c : PBConstr) (d : ℕ) (vf : Bool) : Option (PBConstr × List (Literal ℕ × ℕ) × ℕ) :=
  if vf then
    let lin : List (ℕ × ℤ) := c.terms.map fun t =>
      (termVar t, if termPos t then (t.1 : ℤ) else -t.1)
    let B : ℤ := c.degree - (c.terms.filter (!termPos ·)).foldl (fun s t => s + (t.1 : ℤ)) 0
    let r := B % d
    if r = 0 then none else
    let f (b : ℤ) : ℤ := b / d * r + min (b % d) r
    let M := fromLinear (lin.map fun e => (e.1, f e.2)) ((B / d + 1) * r)
    let ax := lin.filterMap fun e =>
      if e.2 % (d : ℤ) ≥ r then some ((e.1, true), ((d : ℤ) - e.2 % d).toNat) else none
    some (M, ax, r.toNat)
  else
    let r := c.degree % d
    if r = 0 then none else
    let M : PBConstr := ⟨c.terms.map fun t => (t.1 / d * r + min (t.1 % d) r, t.2),
      (c.degree / d + 1) * r⟩
    let ax := c.terms.filterMap fun t => if t.1 % d ≥ r then some (t.2, d - t.1 % d) else none
    some (M, ax, r)

namespace St

/-- A variable not in the terms `ts`, for the `pol` operation `-`: the one after their largest
variable if it has a name, else the least named variable not in them, else a new variable
(`Cslib.Logic.PL.VeriPB.Elab.Lexer.fresh`). So the kernel proof names every variable it uses. -/
private def lowerVar (S : St) (ts : List (ℕ × Literal ℕ)) : EM ℕ := do
  let n ← S.L.nextVar
  let c : PBConstr := ⟨ts, 0⟩
  if freshVar c < n then return freshVar c
  let vs : Std.HashSet ℕ := ts.foldl (fun m t => m.insert (termVar t)) {}
  for v in [0:n] do
    if !vs.contains v then return v
  liftPM S.L.fresh

/-- The trivial constraint `0 ≥ 0`, as `x + ¬x`. -/
private def trivial (S : St) : EM PVal := do
  let x ← S.lowerVar []
  return ⟨fadd (litKey (x, true)) (litKey (x, false)), #[.lit (x, true), .lit (x, false), .add]⟩

/-- The kernel operations pushing a value, as one operation if possible: a `pol` step deriving
it is emitted otherwise, into `pre`. -/
private def asSingle (S : St) (v : PVal) (pre : Array Step) : EM (PVal × Array Step) := do
  if v.ops.size == 1 then return (v, pre)
  let k ← S.takeKid
  return (⟨v.k, #[.id k]⟩, pre.push (.pol v.ops.toList))

/-- **A mixed-integer-rounding cut** of the value `v` with divisor `d`, in variable form if
`vf`: a `pbc` step for the cut, emitted into `pre`, whose subproof refutes its negation. -/
private def mirStep (S : St) (v : PVal) (d : ℕ) (vf : Bool) (pre : Array Step) :
    EM (PVal × Array Step) := do
  if d = 0 then S.fail "division by 0"
  -- The normal form of a canonical form, as the kernel computes it, has the terms reversed.
  let c : PBConstr := ⟨v.c.terms.reverse, v.k.2⟩
  match mir c d vf with
  | none =>
    return (← S.trivial, pre)
  | some (M, ax, r) =>
    let (v, pre) ← S.asSingle v pre
    let n ← S.takeKid
    let negK := keyOf M.negate
    let w := addAxioms v ax
    let E : PVal := ⟨fdiv (fadd w.k negK) (d - r), w.ops ++ #[.id n, .add, .div (d - r)]⟩
    let e ← S.takeKid
    let X := fadd (fmul E.k r) negK
    let x ← S.takeKid
    if !X.isContradiction then S.fail "internal error: MIR cut derivation"
    let m ← S.takeKid
    let _ := m
    return (⟨keyOf M, #[.id m]⟩, pre.push (.pbc M [.pol E.ops.toList,
      .pol [.id e, .mul r, .id n, .add]] x))

/-- **Elaborate a `pol` step**: its constraint, the kernel operations of its final `pol` step,
and the kernel steps to emit before it. -/
private def polOps (S : St) (ops : List AOp) : EM (PVal × Array Step) := do
  let mut st : Array PVal := #[]
  let mut pre : Array Step := #[]
  for op in ops do
    match op with
    | .ref r =>
      let e ← S.entryOf r
      st := st.push ⟨e.key, #[.id e.kid]⟩
    | .lit l => st := st.push ⟨litKey l, #[.lit l]⟩
    | .add =>
      let some b := st.back? | S.fail "pol: empty stack"
      st := st.pop
      let some a := st.back? | S.fail "pol: empty stack"
      st := st.pop.push ⟨fadd a.k b.k, a.ops ++ b.ops |>.push .add⟩
    | _ =>
      let some a := st.back? | S.fail "pol: empty stack"
      st := st.pop
      let a' ← match op with
        | .mul k =>
          if k = 0 then S.trivial
          else pure (⟨fmul a.k k, a.ops.push (.mul k)⟩ : PVal)
        | .div k => if k = 0 then S.fail "pol: division by 0" else
          pure ⟨fdiv a.k k, a.ops.push (.div k)⟩
        | .vdiv k => if k = 0 then S.fail "pol: division by 0" else pure (vdivOps a k)
        | .sat => pure ⟨fsat a.k, a.ops.push .sat⟩
        | .weaken x => pure ⟨fweaken a.k x, a.ops.push (.weaken x)⟩
        | .minus k => pure (lowerOps a k (← S.lowerVar a.c.terms))
        | .nmir k => do
          let (v, p) ← S.mirStep a k false pre
          pre := p
          pure v
        | .vmir k => do
          let (v, p) ← S.mirStep a k true pre
          pre := p
          pure v
        | _ => S.fail "pol: bad operation"
      st := st.push a'
  if st.size != 1 then S.fail "pol: the stack must end with one constraint"
  return (st[0]!, pre)

/-! ### Syntactic implication -/

/-- **Strong syntactic implication** (VeriPB 3.0.2, `PBConstraintGetter::implies`): `t` follows
from `s` by weakening, saturation and adding literal axioms. Both are canonical forms. -/
private def implies (s t : Key) : Bool := Id.run do
  if t.2 == 0 then return true
  if (s.1.foldl (fun a x => a + x.coeff) 0) < s.2 then return true
  let mut cost : ℤ := (t.2 : ℤ) - s.2
  if cost > 0 then return false
  let tm : Std.HashMap (ℕ × Bool) ℕ := t.1.foldl (fun m x => m.insert (x.var, x.pos) x.coeff) {}
  for x in s.1 do
    match tm[(x.var, x.pos)]? with
    | some b => if x.coeff > b && b < t.2 then cost := cost + (x.coeff - b)
    | none => cost := cost + x.coeff
    if cost > 0 then return false
  return true

/-- **The derivation of `ia t : s`**: kernel operations deriving the constraint `t` from the
premise `v`, given `implies`: weaken the terms not in `t` and lower the coefficients above those
of `t` (below its degree), lower the degree to that of `t`, saturate, and add literal axioms up
to the coefficients of `t`. -/
private def impOps (v : PVal) (t : Key) (x : ℕ) : PVal := Id.run do
  let s := v.k
  let tm : Std.HashMap (ℕ × Bool) ℕ := t.1.foldl (fun m x => m.insert (x.var, x.pos) x.coeff) {}
  let mut v := v
  if (s.1.foldl (fun a x => a + x.coeff) 0) < s.2 then
    -- A contradiction: drop its terms, which leaves `0 ≥ k`, `k > 0`.
    for x in s.1 do v := ⟨fweaken v.k x.var, v.ops.push (.weaken x.var)⟩
    v := ⟨fmul v.k (max t.2 1), v.ops.push (.mul (max t.2 1))⟩
  else
    for x in s.1 do
      match tm[(x.var, x.pos)]? with
      | some b =>
        if x.coeff > b && b < t.2 then v := addAxioms v [((x.var, !x.pos), x.coeff - b)]
      | none => v := ⟨fweaken v.k x.var, v.ops.push (.weaken x.var)⟩
  let cur := v.k
  if cur.2 > t.2 then v := lowerOps v (cur.2 - t.2) x
  if t.2 > 0 then v := ⟨fsat v.k, v.ops.push .sat⟩
  let cur := v.k
  let cm : Std.HashMap (ℕ × Bool) ℕ :=
    cur.1.foldl (fun m x => m.insert (x.var, x.pos) x.coeff) {}
  return addAxioms v (t.1.toList.filterMap fun x =>
    let a := (cm[(x.var, x.pos)]?).getD 0
    if a < x.coeff then some ((x.var, x.pos), x.coeff - a) else none)

/-- The premise of `i` or `ia`: the given one, or a constraint of the database implying the
constraint of canonical form `t`, equal ones first (VeriPB 3.0.2, `check_implication`). -/
private def implPremise (S : St) (t : Key) (hint : Option Ref) : EM ℕ := do
  match hint with
  | some r =>
    let i ← S.resolve r
    let e ← S.entry i
    if implies e.key t then return i else S.fail "i/ia: not implied by the given constraint"
  | none =>
    if let some (l, _) := (← S.specs.get)[t]? then
      if let some i := l.back? then return i
    let db ← S.db.get
    for k in [0:db.size - 1] do
      let i := db.size - 1 - k
      let e := db[i]!
      if e.alive && implies e.key t then return i
    S.fail "i/ia: not implied by any constraint"

/-- The constraint of `e t [: r]` and `ea t [: r]`, `t` a canonical form: the one `r` names if it
has the form `t`, else the latest live one with it. -/
private def equalPremise (S : St) (t : Key) (hint : Option Ref) : EM ℕ := do
  match hint with
  | some r =>
    let i ← S.resolve r
    let e ← S.entry i
    if e.key != t then S.fail "e: not the same constraint"
    return i
  | none =>
    match (← S.specs.get)[t]? with
    | some (l, _) =>
      match l.back? with
      | some i => return i
      | none => S.fail "e: no such constraint"
    | none => S.fail "e: no such constraint"

/-! ### RUP -/

/-- One round of propagation of the hinted constraints `cs` from the trail `ρ`, the hints that
propagated so far being `out`: the hints at a conflict, or else the trail, the hints, and
whether the trail grew (`ch`). -/
private def setHintsRound : List (Hint × PBConstr) → List (Literal ℕ) → Array Hint → Bool →
    Array Hint ⊕ (List (Literal ℕ) × Array Hint × Bool)
  | [], ρ, out, ch => .inr (ρ, out, ch)
  | (h, d) :: cs, ρ, out, ch =>
    match propagate ρ d with
    | none => .inl (out.push h)
    | some ρ' =>
      if ρ'.length != ρ.length then setHintsRound cs ρ' (out.push h) true
      else setHintsRound cs ρ out ch

/-- Rounds of propagation of the hinted constraints `cs`, at most `fuel`, until a conflict (its
hints) or a round that adds nothing (`none`). -/
private def setHintsLoop (cs : List (Hint × PBConstr)) :
    ℕ → List (Literal ℕ) → Array Hint → Option (Array Hint)
  | 0, _, _ => none
  | fuel + 1, ρ, out =>
    match setHintsRound cs ρ out false with
    | .inl out => some out
    | .inr (ρ, out, ch) => if ch then setHintsLoop cs fuel ρ out else none

/-- The hints of `rup c` with the augmented set annotation `hs` (§5.2.1): propagate the hinted
constraints and `¬c` until a conflict or a fixpoint, and list those that propagated, in order. -/
private def setHints (S : St) (c : PBConstr) (hs : List AHint) : EM (List Hint) := do
  let neg := negateParsed c
  let mut cs : Array (Hint × PBConstr) := #[(.neg, neg)]
  for h in hs do
    match h with
    | .neg => pure ()
    | .ref r =>
      let e ← S.entryOf r
      cs := cs.push (.id e.kid, e.c)
  -- Each round but the last adds a literal of a term to the trail.
  let fuel := (cs.toList.map (·.2.terms.length)).sum + 1
  match setHintsLoop cs.toList fuel [] #[] with
  | some out => return out.toList
  | none => S.fail "rup: the hints do not propagate to a conflict"

/-- The hints of `rup c`. -/
private def rupHintsOf (S : St) (c : PBConstr) (hs : Option (List AHint)) : EM (List Hint) := do
  match hs with
  | some hs => S.setHints c hs
  | none =>
    match ← S.engRupHints (negateParsed c) with
    | some h => return h.toList
    | none => S.fail "rup: propagation finds no conflict"

/-! ### Steps -/

/-- The value a label gets from a rule that derives nothing: its premise or match. -/
private abbrev Returned := Option ℕ

/-- The closing contradiction of a subproof whose constraints are numbered from `start`: the
given one, or the most recent contradiction, or else a hinted `rup` of `0 ≥ 1` found by
propagation, or, for a subproof refuting `¬G` (`goal`, with the kernel number of `¬G`), a `pol`
step adding `¬G` to `G` derived from a constraint of the database that implies it. The extra step
is returned, to append. -/
private def closing (S : St) (start : ℕ) (q : Option Ref) (goal : Option (ℕ × PBConstr)) :
    EM (Array Step × ℕ) := do
  match q with
  | some r => return (#[], (← S.entryOf r).kid)
  | none =>
    match ← S.lastContra start with
    | some i => return (#[], (← S.entry i).kid)
    | none =>
      match ← S.rupContra with
      | some h =>
        let k ← S.takeKid
        return (#[.rup ⟨[], 1⟩ h], k)
      | none =>
        let some (n, G) := goal | S.fail "subproof: no contradiction"
        let t := keyOf G
        let i ← try S.implPremise t none catch _ => S.fail "subproof: no contradiction"
        let e ← S.entry i
        let v := impOps ⟨e.key, #[.id e.kid]⟩ t (← S.lowerVar (e.c.terms ++ G.terms))
        if !(fadd v.k (keyOf G.negate)).isContradiction then S.fail "subproof: no contradiction"
        let k ← S.takeKid
        return (#[.pol (v.ops.push (.id n) |>.push .add).toList], k)

mutual

/-- **Elaborate an implicational step**, in a subproof or at top level: the kernel steps, and
the augmented number of the constraint the step names, for a label. -/
private def step (S : St) (top : Bool) (s : AStep) : EM (Array Step × Returned) := do
  match s with
  | .labeled l s =>
    let (ks, r) ← S.step top s
    let some id := r | S.fail s!"nothing to label with {l}"
    S.labels.modify (·.insert l id)
    return (ks, r)
  | .pol ops =>
    let (v, pre) ← S.polOps ops
    let k ← S.takeKid
    let id ← S.add v.c k false top v.k
    return (pre.push (.pol v.ops.toList), some id)
  | .rup c hs =>
    let h ← S.rupHintsOf c hs
    let k ← S.takeKid
    let id ← S.add (normalizeParsed c) k false top (keyOfParsed c)
    return (#[.rup c h], some id)
  | .imp c add hint =>
    let t := keyOfParsed c
    let i ← S.implPremise t hint
    if !add then return (#[], some i)
    let e ← S.entry i
    let v := impOps ⟨e.key, #[.id e.kid]⟩ t (← S.lowerVar (e.c.terms ++ c.terms))
    if v.k != t then S.fail "internal error: ia derivation"
    let k ← S.takeKid
    let id ← S.add v.c k false top v.k
    return (#[.pol v.ops.toList], some id)
  | .equal c hint => return (#[], some (← S.equalPremise (keyOfParsed c) hint))
  | .equalAdd c hint =>
    let e ← S.entry (← S.equalPremise (keyOfParsed c) hint)
    let k ← S.takeKid
    let id ← S.add e.c k false top e.key
    return (#[.pol [.id e.kid]], some id)
  | .isDeleted c =>
    match (← S.specs.get)[keyOfParsed c]? with
    | some (l, _) => if l.isEmpty then return (#[], none) else S.fail "is_deleted: not deleted"
    | none => return (#[], none)
  | .pbc c sub q =>
    let n ← S.takeKid
    let start ← S.augNext
    let _ ← S.add (negateParsed c) n false false
    let ks ← match sub with
      | some sub => S.steps false sub
      | none => pure #[]
    let (extra, qk) ← S.closing start q (some (n, c))
    S.dropFrom start
    let k ← S.takeKid
    let id ← S.add (normalizeParsed c) k false top
    return (#[.pbc c (ks ++ extra).toList qk], some id)
  | .noop => return (#[], none)
  | _ => S.fail "this rule is allowed only at top level"

/-- Elaborate implicational steps, after the kernel steps `out`. -/
private def steps (S : St) (top : Bool) : List AStep → (out : Array Step := #[]) →
    EM (Array Step)
  | [], out => return out
  | s :: ss, out => do S.steps top ss (out ++ (← S.step top s).1)

end

/-- The premises of the goals and scopes of a subproof: for a goal label, its kernel label and
the constraints it adds; for a scope, its constraints. -/
private structure Premises where
  /-- The premises of a goal. -/
  goal : AGoal → EM (GoalId × List PBConstr)
  /-- The premises of a scope. -/
  scope : Bool → Option (List PBConstr)

/-- **Elaborate the items of a subproof** of `red`, `dom`, a checked deletion, `obju` or a change
of the preserved set. A `proofgoal` block without a closing contradiction gets the most recent
one, or a hinted `rup` of `0 ≥ 1`. -/
private def items (S : St) (P : Premises) :
    List AStep → (out : Array RedItem := #[]) → EM (Array RedItem)
  | [], out => return out
  | .goal g sub q :: ss, out => do
    let (kg, ps) ← P.goal g
    let start ← S.augNext
    for p in ps do
      let k ← S.takeKid
      let _ ← S.add p k false false
    let ks ← S.steps false sub
    let (extra, qk) ← S.closing start q none
    let ks := ks ++ extra
    S.dropFrom start
    S.items P ss (out.push (.goal kg ks.toList qk))
  | .scope b inner :: ss, out => do
    let some ps := P.scope b | S.fail "scope not allowed here"
    let start ← S.augNext
    for p in ps do
      let k ← S.takeKid
      let _ ← S.add p k false false
    let ki ← S.items P inner
    S.dropFrom start
    S.items P ss (out.push (.scope b ki.toList))
  | s :: ss, out => do S.items P ss (out ++ (← S.step false s).1.map .step)

/-- The `#k` entry of a list of goals, numbered from `1`. -/
private def hashAt {α : Type} (l : List α) (k : ℕ) : Option α := if k = 0 then none else l[k - 1]?

/-- The premises of the subproof of `red C : ω` (`dom = false`) or `dom C : ω`, with the database
`db₀` of the step given by its augmented numbers. -/
private def redPremises (S : St) (dom : Bool) (c : PBConstr) (ω : Witness) :
    EM Premises := do
  let obj ← S.obj.get
  let ord ← S.order.get
  let db₀ ← S.db.get
  let dbGoal (r : Ref) : EM (GoalId × List PBConstr) := do
    let i ← S.resolve r
    let some e := db₀[i]? | S.fail s!"proofgoal: no constraint {i}"
    if !e.alive || (dom && !e.core) then S.fail s!"proofgoal: constraint {i} is not a goal"
    return (.db e.kid, [(Witness.substC ω e.c).negate])
  if dom then
    let some L := ord | S.fail "dom: no order loaded"
    return ⟨fun
      | .hash k => match hashAt (domHashPremises obj L ω) k with
        | some ps => pure (.hash k, ps)
        | none => S.fail s!"proofgoal: no goal #{k}"
      | .ref r => dbGoal r, domScope L ω⟩
  return ⟨fun
    | .hash k => match hashAt (redHashGoals obj ord ω c) k with
      | some G => pure (.hash k, [G.negate])
      | none => S.fail s!"proofgoal: no goal #{k}"
    | .ref r => dbGoal r, redScope ord ω⟩

/-- The premises of a subproof whose goals are only `#k`, the constraints `gs`. -/
private def hashPremises (S : St) (gs : List PBConstr) : Premises :=
  ⟨fun
    | .hash k => match hashAt gs k with
      | some G => pure (.hash k, [G.negate])
      | none => S.fail s!"proofgoal: no goal #{k}"
    | .ref _ => S.fail "proofgoal: no database goals here", fun _ => none⟩


/-! ### Autoproving (§5.5) -/

/-- The goal `G` is covered without a subproof in the kernel format (§5.5.1): it is trivially true
after normalization, or weakly syntactically implied by `negC`, or, for a database goal (`db`), it
is, up to the order of terms, a live constraint numbered below `start`, a core constraint if
`core`. (The Lean checker also accepts the last case for `#k` goals and `obju`; CakePB does not, so
such goals get a subproof.) -/
private def covered (S : St) (start : ℕ) (core db : Bool) (negC : Option PBConstr)
    (G : PBConstr) : EM Bool := do
  if G.normalize.degree == 0 then return true
  if negC.any (weakImplies · G) then return true
  if !db then return false
  return (← S.findBelow start core G).isSome

/-- A goal to prove: its label, its premises, the goal constraint when the premise is its
negation, and, for the goal `D|ω` of a database constraint `D`, the augmented number of `D`. -/
private abbrev Goal := GoalId × List PBConstr × Option PBConstr × Option ℕ

/-- The canonical form `k` with the assignment `ρ` substituted, as VeriPB 3.0.2 substitutes the
propagated assignment (`PBConstraint::substitute`): a true term is dropped and lowers the degree,
a false term is dropped. A negative degree becomes `0`, which changes no answer of `implies`: a
constraint of degree at most `0` is trivial as a target and implies no non-trivial target. -/
private def substKey (ρ : Std.HashMap ℕ Bool) (k : Key) : Key := Id.run do
  let mut ts : Array KTerm := .mkEmpty k.1.size
  let mut d := k.2
  for t in k.1 do
    match ρ[t.var]? with
    | some b => if b == t.pos then d := d - t.coeff
    | none => ts := ts.push t
  return (ts, d)

/-- `implies (substKey ρ s) t`, without building the substituted constraint; `tm` maps the
literals of `t` to their coefficients. -/
private def substImplies (ρ : Std.HashMap ℕ Bool) (tm : Std.HashMap (ℕ × Bool) ℕ) (s t : Key) :
    Bool := Id.run do
  if t.2 == 0 then return true
  let mut d := s.2
  let mut sum := 0
  for x in s.1 do
    match ρ[x.var]? with
    | some b => if b == x.pos then d := d - x.coeff
    | none => sum := sum + x.coeff
  if sum < d then return true
  let mut cost : ℤ := (t.2 : ℤ) - d
  if cost > 0 then return false
  for x in s.1 do
    if ρ.contains x.var then continue
    match tm[(x.var, x.pos)]? with
    | some b => if x.coeff > b && b < t.2 then cost := cost + (x.coeff - b)
    | none => cost := cost + x.coeff
    if cost > 0 then return false
  return true

/-- The largest coefficient of a canonical form, at least `1`. -/
private def maxCoeff (k : Key) : ℕ := k.1.foldl (fun m t => max m t.coeff) 1

/-- **The refutation of `¬G` by syntactic implication**: kernel operations that derive `t` from the
premise `e` (`impOps`), after adding `M` times the units `u` (canonical form and kernel number;
`M` the largest coefficient of `e`), which substitutes them into `e`, and then add `¬G` (kernel
number `pk`) and `M'` times the units (`M'` the largest coefficient of `G`), a contradiction if
`t` is `G` with the units substituted. As VeriPB 3.0.2 elaborates the autoproving of a
substituted implication (`write_substituted_implication_subproof`), whose `ia` step becomes the
weakening, saturation and literal axioms of `impOps`. `none` if the result is not a
contradiction. -/
private def implRefute (S : St) (e : Entry) (G : PBConstr) (t : Key) (pk : ℕ)
    (u : Option (Key × ℕ)) : EM (Option (List PolOp)) := do
  let v₀ : PVal := match u with
    | some (ku, ui) =>
      let m := maxCoeff e.key
      ⟨fadd e.key (fmul ku m), #[.id e.kid, .id ui, .mul m, .add]⟩
    | none => ⟨e.key, #[.id e.kid]⟩
  let v := impOps v₀ t (← S.lowerVar (e.c.terms ++ G.terms))
  if v.k != t then return none
  let negG := keyOf G.negate
  let (w, ops) : Key × Array PolOp := match u with
    | some (ku, ui) =>
      let m := maxCoeff (keyOf G)
      (fadd negG (fmul ku m), #[.id pk, .id ui, .mul m, .add])
    | none => (negG, #[.id pk])
  if !(fadd v.k w).isContradiction then return none
  return some (v.ops ++ ops |>.push .add).toList

/-- **Autoproving by syntactic implication** (§5.5.2; VeriPB 3.0.2, `Proofgoal::autoprove`), for
a goal `G` whose negation has the kernel number `pk` and is no longer in the engine: the steps of
a `proofgoal` block refuting `¬G`, if
* one of `direct` (the additional premise, and for the goal `D|ω` the constraint `D`) strongly
  syntactically implies `G` (`implies`), or
* with the assignment `ρ` that the database propagates (the root trail of the engine), some live
  constraint `D` not in `skip` has `D|ρ` implying `G|ρ`. Then the block first derives the units
  of `ρ` on the variables of `D` and `G` by a hinted `rup`. If `core`, `D` is a core constraint
  or numbered from `start`: VeriPB 3.0.2 adds the constraints of a core-only subproof to the core
  set (`ForwardsChecker::execute_rule`), `¬C` among them when the step has a subproof.

VeriPB tries every constraint of the database for the second case; only those containing a
literal of `G|ρ` can succeed, since with no conflict at the root no `D|ρ` is a contradiction, and
a constraint sharing no literal with `G|ρ` implies it only if `G|ρ` is trivial, when the goal is
RUP. So the constraints tried are those containing a variable of `G|ρ`, from `varOcc`, the
variables with fewer occurrences first. -/
private def implGoal (S : St) (start : ℕ) (core : Bool) (direct skip : List ℕ) (G : PBConstr)
    (pk : ℕ) : EM (Option (Array Step)) := do
  let t := keyOf G
  for i in direct do
    let e ← S.entry i
    if implies e.key t then
      if let some ops ← S.implRefute e G t pk none then return some #[.pol ops]
  let some tr ← S.engExtend [] | return none
  let ρ : Std.HashMap ℕ Bool := tr.foldl (fun m l => m.insert l.1 l.2) {}
  let st := substKey ρ t
  let db ← S.db.get
  let occ ← S.varOcc.get
  let tm : Std.HashMap (ℕ × Bool) ℕ := st.1.foldl (fun m x => m.insert (x.var, x.pos) x.coeff) {}
  -- The shortest occurrence lists first.
  let lists := (st.1.map fun x => (occ[x.var]?).getD #[]).qsort (·.size < ·.size)
  let mut seen : Std.HashSet ℕ := {}
  for l in lists do
    for i in l do
      if seen.contains i then continue
      seen := seen.insert i
      let some e := db[i]? | continue
      if i == 0 || !e.alive || (core && !e.core && i < start) || skip.contains i then continue
      if !substImplies ρ tm e.key st then continue
      -- The units of `ρ` on the variables of `D` and `G`.
      let vs : Std.HashSet ℕ := (e.key.1 ++ t.1).foldl (fun m t => m.insert t.var) {}
      let us := tr.filter (vs.contains ·.1)
      if us.isEmpty then
        let some ops ← S.implRefute e G st pk none | return none
        return some #[.pol ops]
      let U : PBConstr := ⟨us.toList.map ((1, ·)), us.size⟩
      let some h ← S.engRupHints (negateParsed U) | return none
      let u ← S.takeKid
      let some ops ← S.implRefute e G st pk (some (keyOfParsed U, u)) | return none
      return some #[.rup U h.toList, .pol ops]
  return none

/-- **Prove goals automatically** (§5.5.2): for each goal not proved by the user (`proved`), a
`proofgoal` block whose premises propagate to a conflict, closed by a hinted `rup` of `0 ≥ 1`, or,
for a goal that is a constraint of the database numbered below `start` (a core constraint if
`core`), the sum of its negation and that constraint, or else a refutation by syntactic
implication (`implGoal`) from the additional premise `prem` or a database constraint other than
those of `skip` (a core constraint or one numbered from `start` if `core`). A goal none proves
fails the elaboration, as in VeriPB. The premises take kernel numbers but no augmented ones. -/
private def autoGoals (S : St) (start : ℕ) (core : Bool) (proved : List GoalId) (gs : List Goal)
    (prem : Option ℕ := none) (skip : List ℕ := []) : EM (Array RedItem) := do
  let mut out := #[]
  for (g, ps, G?, src) in gs do
    if proved.contains g then continue
    let mark ← S.augNext
    let mut pk := 0
    for p in ps do
      pk ← S.takeKid
      let _ ← S.add p pk false false
    match ← S.rupContra with
    | some h =>
      let k ← S.takeKid
      out := out.push (.goal g [.rup ⟨[], 1⟩ h] k)
    | none =>
      let some G := G? | S.fail s!"a proof goal could not be autoproven ({repr g})"
      match ← S.findBelow start core G with
      | some i =>
        let e ← S.entry i
        let k ← S.takeKid
        out := out.push (.goal g [.pol [.id pk, .id e.kid, .add]] k)
      | none =>
        -- The substituted assignment is propagated without `¬G`.
        S.popTo mark
        let some sub ← S.implGoal start core (prem.toList ++ src.toList) skip G pk
          | S.fail s!"a proof goal could not be autoproven ({repr g})"
        let k ← S.takeKid
        out := out.push (.goal g sub.toList k)
    S.popTo mark
  return out

/-- The live constraints numbered below `start` that contain a variable the witness sets (core
constraints if `core`, and other than `skip`). -/
private def touched (S : St) (start : ℕ) (core : Bool) (ω : Witness) (skip : ℕ := 0) :
    EM (Array ℕ) := do
  let occ ← S.varOcc.get
  let db ← S.db.get
  let mut seen : Std.HashMap ℕ Unit := {}
  let mut out := #[]
  for (x, _) in ω do
    for i in (occ[x]?).getD #[] do
      if i < start && i != skip && !seen.contains i && db[i]!.alive && (!core || db[i]!.core)
      then
        seen := seen.insert i ()
        out := out.push i
  return out.qsort (· < ·)

/-- The goals of a database constraint `D` under `ω` that are not covered: `D|ω`, unless `ω` sets
every literal of `D` it touches true, or `D` implies `D|ω`, or `D|ω` is covered. -/
private def dbGoals (S : St) (start : ℕ) (core : Bool) (negC : Option PBConstr) (ω : Witness)
    (ids : Array ℕ) : EM (List Goal) := do
  let db ← S.db.get
  let mut out := #[]
  for i in ids do
    let e := db[i]!
    let G := Witness.substC ω e.c
    if Witness.touchedTrue ω e.c || weakImplies e.c G then continue
    if ← S.covered start core true negC G then continue
    out := out.push (GoalId.db e.kid, [G.negate], some G, some i)
  return out.toList

/-- The goals of `red C : ω` that are not covered (§5.4.1, §5.5.1), with the database of the step
numbered below `start`: `#1` is `C|ω`, then the order goals (if the witness touches the loaded
order), the objective goal, and `D|ω` for the constraints `D` touched by `ω` (core constraints in
strengthening-to-core mode, `gsCore`). -/
private def redGoals (S : St) (start : ℕ) (gsCore : Bool) (c : PBConstr) (ω : Witness)
    (skip : ℕ := 0) : EM (List Goal) := do
  let obj ← S.obj.get
  let ord ← S.order.get
  let negC := c.negate
  let hash := redHashGoals obj ord ω c
  let mut out : Array Goal := #[]
  let n := ((ord.map (·.leGoals ω)).getD []).length
  for (G, k) in hash.zipIdx do
    -- The order goals need no proof when the witness leaves the order alone.
    if 1 ≤ k && k ≤ n && ord.any (·.untouched ω) then continue
    if !(← S.covered start false false (some negC) G) then
      out := out.push (.hash (k + 1), [G.negate], some G, none)
  let ids ← S.touched start gsCore ω skip
  return out.toList ++ (← S.dbGoals start false (some negC) ω ids)

/-- The goals of `dom C : ω` that are not covered (§5.4.2): the order goals, goal `#N + 1` with the
constraints `O⪯(z, z↾ω, a)` to refute, the objective goal, and `D|ω` for the core constraints
`D` touched by `ω`. -/
private def domGoals (S : St) (start : ℕ) (L : LoadedOrder) (c : PBConstr) (ω : Witness) :
    EM (List Goal) := do
  let obj ← S.obj.get
  let negC := c.negate
  let le := L.leGoals ω
  let mut out : Array Goal := #[]
  for (G, k) in le.zipIdx do
    if !(← S.covered start false false (some negC) G) then
      out := out.push (.hash (k + 1), [G.negate], some G, none)
  out := out.push (.hash (le.length + 1), (L.geGoals ω).map normalize, none, none)
  if let some f := obj then
    let G := objGoal f ω
    if !(← S.covered start false false (some negC) G) then
      out := out.push (.hash (le.length + 2), [G.negate], some G, none)
  let ids ← S.touched start true ω
  return out.toList ++ (← S.dbGoals start false (some negC) ω ids)

/-- The labels of the goals proved by the items of a subproof. -/
private def givenGoals : List RedItem → List GoalId
  | [] => []
  | .goal g _ _ :: items => g :: givenGoals items
  | .scope _ inner :: items => givenGoals inner ++ givenGoals items
  | .step _ :: items => givenGoals items

/-- Run `act` with a fresh propagation engine holding only the live core constraints (other than
`skip`) and the constraints numbered from `start`: the goals of `obju`, of the changes of the
preserved set and of checked deletion are derived from the core set alone (§5.9, §5.10,
§5.7.1), to which VeriPB 3.0.2 adds the constraints of the subproof. -/
private def withCoreEngine {α : Type} (S : St) (start : ℕ) (skip : ℕ) (act : St → EM α) :
    EM α := do
  let mut eng := Engine.new
  let db ← S.db.get
  let mut db' := db
  for i in [1:db.size] do
    let e := db[i]!
    if e.alive && i != skip && (e.core || start ≤ i) then
      let (eng', k) := eng.add e.c (.id e.kid)
      eng := eng'
      db' := db'.set! i { e with eidx := k }
  let saved := db
  S.db.set db'
  -- The fresh engine replaces the main one while `act` runs.
  let main ← S.swapEng eng
  let r ← act S
  let _ ← S.swapEng main
  -- Restore the engine indices of the main engine.
  let after ← S.db.get
  S.db.set (after.mapIdx fun i e => if h : i < saved.size then
    { e with eidx := saved[i].eidx } else e)
  return r

/-- Mark every live constraint as a core constraint. -/
private def allCore (S : St) : EM Unit :=
  S.db.modify (·.map fun e => { e with core := true })

/-- A logged solution, extended by propagation and completed with the other variables of the
database false (§5.8.1). -/
private def completeSolution (S : St) (ρ : List (Literal ℕ)) : EM (List (Literal ℕ)) := do
  let db ← S.db.get
  let cs := (db.filter (·.alive)).toList.map (·.c)
  if solves ρ cs then return ρ
  let some ext ← S.engExtend ρ | S.fail "sol: the solution propagates to a conflict"
  let mut seen : Std.HashMap ℕ Unit := {}
  for l in ext do seen := seen.insert l.1 ()
  let mut out := ext
  for c in cs do
    for t in c.terms do
      if !seen.contains (termVar t) then
        seen := seen.insert (termVar t) ()
        out := out.push (termVar t, false)
  return out.toList

/-- **Elaborate a top-level rule**. -/
private def top (S : St) (s : AStep) : EM (Array TopStep) := do
  match s with
  | .labeled l s' =>
    match s' with
    | .red .. | .sol .. | .obji .. | .pol .. =>
      let n ← S.augNext
      let ks ← S.top s'
      if (← S.augNext) == n then S.fail s!"nothing to label with {l}"
      S.labels.modify (·.insert l ((← S.augNext) - 1))
      return ks
    | _ =>
      let (ks, r) ← S.step true s
      let _ := r
      return ks.map .step
  | .red dom c ω sub q =>
    let P ← S.redPremises dom c ω
    let core ← S.tcb.get
    let ord ← S.order.get
    let n ← S.takeKid
    let start ← S.augNext
    let _ ← S.add (negateParsed c) n false false
    let ki ← match sub with
      | some sub => S.items P sub
      | none => pure #[]
    let qk ← q.mapM fun r => do return (← S.entryOf r).kid
    -- The goals the user left to autoproving.
    let auto ← if qk.isSome then pure #[] else do
      let gs ← if dom then
          match ord with
          | some L => S.domGoals start L c ω
          | none => S.fail "dom: no order loaded"
        else S.redGoals start core c ω
      S.autoGoals start false (givenGoals ki.toList) gs (prem := some start)
        (skip := if sub.isNone then [start] else [])
    let ki := ki ++ auto
    -- The kernel step always has a subproof, as CakePB's parser requires; without one in the
    -- augmented proof, `¬C` takes no augmented number.
    if sub.isNone then S.popTo start else S.dropFrom start
    let k ← S.takeKid
    let _ ← S.add (normalizeParsed c) k core true
    return #[if dom then .dom c ω (some ki.toList) qk else .red c ω (some ki.toList) qk]
  | .delId ids => S.deleteRefs (← ids.mapM S.resolve)
  | .delSpec c => S.deleteSpec c
  | .delRange a b =>
    let a ← S.resolve a
    let b ← S.resolve b
    let db ← S.db.get
    S.deleteRefs ((List.range' a (b - a)).filter fun i => (db[i]?.map (·.alive)).getD false)
  | .deld ids =>
    let ids ← ids.mapM S.resolve
    for i in ids do
      if (← S.entry i).core then S.fail s!"deld: constraint {i} is a core constraint"
    S.deleteRefs ids
  | .delc ids =>
    let ids ← ids.mapM S.resolve
    for i in ids do
      if !(← S.entry i).core then S.fail s!"delc: constraint {i} is a derived constraint"
    S.deleteRefs ids
  | .delcChecked r ω sub q =>
    let i ← S.resolve r
    let e ← S.entry i
    let obj ← S.obj.get
    let ord ← S.order.get
    if !e.core then
      -- A derived constraint needs no check.
      return ← S.deleteRefs [i]
    let n ← S.takeKid
    let start ← S.augNext
    let _ ← S.add e.c.negate n false false
    let P : Premises := ⟨fun
      | .hash k => match hashAt (redHashGoals obj ord ω e.c) k with
        | some G => pure (.hash k, [G.negate])
        | none => S.fail s!"proofgoal: no goal #{k}"
      | .ref r => do
        let d ← S.entryOf r
        return (.db d.kid, [(Witness.substC ω d.c).negate]), redScope ord ω⟩
    let ki ← match sub with
      | some sub => S.items P sub
      | none => pure #[]
    let qk ← q.mapM fun r => do return (← S.entryOf r).kid
    let auto ← if qk.isSome then pure #[] else
      S.withCoreEngine start i fun S' => do
        let gs ← S'.redGoals start true e.c ω (skip := i)
        S'.autoGoals start true (givenGoals ki.toList) gs (prem := some start)
          (skip := i :: if sub.isNone then [start] else [])
    let ki := ki ++ auto
    if sub.isNone then S.popTo start else S.dropFrom start
    S.drop i
    return #[.delcChecked e.kid ω (some ki.toList) qk]
  | .coreId ids =>
    let ids ← ids.mapM S.resolve
    let es ← ids.mapM S.entry
    for i in ids do S.db.modify (·.modify i ({ · with core := true }))
    return #[.core (es.map (·.kid))]
  | .coreRange a b =>
    let a ← S.resolve a
    let b ← S.resolve b
    let db ← S.db.get
    let ids := (List.range' a (b - a)).filter fun i => (db[i]?.map (·.alive)).getD false
    for i in ids do S.db.modify (·.modify i ({ · with core := true }))
    return if ids.isEmpty then #[] else #[.core (ids.map (db[·]!.kid))]
  | .setlvl l =>
    S.level.set (some l)
    return #[]
  | .wiplvl l =>
    let lv ← S.levels.get
    let ks := lv.fold (fun acc k _ => if l ≤ k then acc.push k else acc) #[]
    let db ← S.db.get
    let mut ids : Array ℕ := #[]
    for k in ks do
      for i in lv[k]! do
        if db[i]!.alive && !ids.contains i then ids := ids.push i
      S.levels.modify (·.erase k)
    S.deleteRefs ids.toList
  | .sol kind ρ =>
    let ρ ← S.completeSolution ρ
    match kind with
    | 0 => return #[.sol ρ]
    | 1 =>
      let some f ← S.obj.get | S.fail "soli: no objective"
      let k ← S.takeKid
      let _ ← S.add (f.improving (f.eval (assignOf ρ))).normalize k true true
      return #[.soli ρ]
    | _ =>
      let some P ← S.pres.get | S.fail "solx: no preserved set"
      let k ← S.takeKid
      let _ ← S.add (exclusion P ρ) k true true
      return #[.solx ρ]
  | .obji v =>
    let some f ← S.obj.get | S.fail "obji: no objective"
    let k ← S.takeKid
    let _ ← S.add (f.improving v).normalize k true true
    return #[.obji v]
  | .obju diff g sub =>
    let some f ← S.obj.get | S.fail "obju: no objective"
    let f' := if diff then f.add g else g
    let gs := [f'.geGoal f, f.geGoal f']
    let start ← S.augNext
    let ki ← match sub with
      | some sub => S.items (S.hashPremises gs) sub
      | none => pure #[]
    let auto ← S.withCoreEngine start 0 fun S' => do
      let mut need : Array Goal := #[]
      for (G, k) in gs.zipIdx do
        if !(← S'.covered start true false none G) then
          need := need.push (GoalId.hash (k + 1), [G.negate], some G, none)
      S'.autoGoals start true (givenGoals ki.toList) need.toList
    let ki := ki ++ auto
    S.obj.set (some f')
    return #[.obju diff g (some ki.toList)]
  | .stc on =>
    if on then S.allCore
    S.tcb.set on
    return #[.strengthenToCore on]
  | .defOrder name O sp w tp rp =>
    S.orders.modify (·.insert name O)
    return #[.defOrder name O sp w tp rp]
  | .loadOrder name z =>
    let some O := (← S.orders.get)[name]? | S.fail s!"unknown order {name}"
    S.allCore
    S.order.set (some ⟨O, z⟩)
    return #[.loadOrder name z]
  | .unloadOrder =>
    S.order.set none
    return #[.unloadOrder]
  | .eordDef name O => return #[.eordDef name O]
  | .eordLoaded name z => return #[.eordLoaded name z]
  | .presChange add x c sub =>
    let some P ← S.pres.get | S.fail "preserved set changes need a preserved set"
    let gs := presGoals x c
    let start ← S.augNext
    let ki ← match sub with
      | some sub => S.items (S.hashPremises gs) sub
      | none => pure #[]
    let auto ← S.withCoreEngine start 0 fun S' => do
      let need : List Goal := (gs.zipIdx.filter fun (G, _) => G.normalize.degree != 0).map
        fun (G, k) => (GoalId.hash (k + 1), [G.negate], some G, none)
      S'.autoGoals start true (givenGoals ki.toList) need
    let ki := ki ++ auto
    S.pres.set (some (if add then P.insert x else P.filter (· != x)))
    return #[.presChange add x c (some ki.toList)]
  | .epreserved vs => return #[.epreserved vs]
  | .eobj g =>
    match ← S.obj.get with
    | some f => if f.equiv g then return #[] else S.fail "eobj: not the current objective"
    | none => S.fail "eobj: no objective"
  | .pol .. =>
    -- At top level, the auxiliary constraints of a `pol` step are deleted after it: the `pol`
    -- steps before the last and the cuts of the `pbc` steps.
    let k₀ ← S.kerNext.get
    let (ks, _) ← S.step true s
    let mut k := k₀
    let mut tmp : Array ℕ := #[]
    for st in ks.pop do
      match st with
      | .pbc _ sub _ => k := k + sub.length + 2; tmp := tmp.push (k - 1)
      | _ => tmp := tmp.push k; k := k + 1
    return ks.map .step ++ (if tmp.isEmpty then #[] else #[.deld tmp.toList])
  | s => return (← S.step true s).1.map .step

/-- The kernel conclusion of an augmented one. -/
private def conclusion (S : St) : AConclusion → EM Conclusion
  | .unsat q => do
    match q with
    | some r => return .unsat (← S.entryOf r).kid
    | none =>
      match ← S.lastContra 1 with
      | some i => return .unsat (← S.entry i).kid
      | none => S.fail "conclusion UNSAT: no contradiction"
  | .sat asg => return .sat asg
  | .bounds lb q ub asg => do
    let kq ← match q with
      | some r => pure (← S.entryOf r).kid
      | none =>
        match ← S.lastContra 1 with
        | some i => pure (← S.entry i).kid
        | none =>
          let some f ← S.obj.get | S.fail "conclusion BOUNDS: no objective"
          let some l := lb | S.fail "conclusion BOUNDS INF: no contradiction"
          let t := keyOf (f.atLeast l)
          let db ← S.db.get
          match (db.toList.zipIdx.reverse.find? fun (e, i) =>
              i != 0 && e.alive && weakImplies e.c (f.atLeast l)) with
          | some (e, _) => pure e.kid
          | none => S.fail s!"conclusion BOUNDS: no constraint implies the bound {t.2}"
    return .bounds lb kq ub asg
  | .noClaim => return .noClaim
  | .enumPartial n => return .enumPartial n
  | .enumComplete n q => do
    match q with
    | some r => return .enumComplete n (← S.entryOf r).kid
    | none =>
      match ← S.lastContra 1 with
      | some i => return .enumComplete n (← S.entry i).kid
      | none => S.fail "conclusion ENUMERATION_COMPLETE: no contradiction"

end St

/-! ### Trimming -/

/-- The constraint numbers a hint refers to. -/
private def Hint.ids : Hint → List ℕ
  | .neg => []
  | .id n => [n]

mutual

/-- The constraint numbers a kernel step refers to, other than those it deletes. -/
private def stepRefs : Step → List ℕ
  | .pol ops => ops.filterMap fun | .id n => some n | _ => none
  | .rup _ hs => hs.flatMap Hint.ids
  | .rupSearch _ => []
  | .pbc _ sub q => q :: sub.flatMap stepRefs
  | .del _ => []

/-- The constraint numbers an item of a subproof refers to. -/
private def itemRefs : RedItem → List ℕ
  | .step s => stepRefs s
  | .goal g sub q => (match g with | .db n => [n] | .hash _ => []) ++ q :: sub.flatMap stepRefs
  | .scope _ items => items.flatMap itemRefs

end

/-- The constraint numbers a top-level kernel step refers to, other than those it deletes. Orders
have numbers of their own and refer to none. -/
private def topRefs : TopStep → List ℕ
  | .step s => stepRefs s
  | .red _ _ sub q | .dom _ _ sub q => q.toList ++ (sub.getD []).flatMap itemRefs
  | .delcChecked i _ sub q => i :: q.toList ++ (sub.getD []).flatMap itemRefs
  | .core ids => ids
  | .obju _ _ sub | .presChange _ _ _ sub => (sub.getD []).flatMap itemRefs
  | _ => []

mutual

/-- Renumber the constraint references of a kernel step. -/
private def stepRenum (f : ℕ → ℕ) : Step → Step
  | .pol ops => .pol (ops.map fun | .id n => .id (f n) | o => o)
  | .rup c hs => .rup c (hs.map fun | .id n => .id (f n) | h => h)
  | .rupSearch c => .rupSearch c
  | .pbc c sub q => .pbc c (sub.map (stepRenum f)) (f q)
  | .del ids => .del (ids.map f)

/-- Renumber the constraint references of an item of a subproof. -/
private def itemRenum (f : ℕ → ℕ) : RedItem → RedItem
  | .step s => .step (stepRenum f s)
  | .goal g sub q =>
    .goal (match g with | .db n => .db (f n) | g => g) (sub.map (stepRenum f)) (f q)
  | .scope b items => .scope b (items.map (itemRenum f))

end

/-- Renumber the constraint references of a top-level kernel step. -/
private def topRenum (f : ℕ → ℕ) : TopStep → TopStep
  | .step s => .step (stepRenum f s)
  | .red c ω sub q => .red c ω (sub.map (·.map (itemRenum f))) (q.map f)
  | .dom c ω sub q => .dom c ω (sub.map (·.map (itemRenum f))) (q.map f)
  | .delcChecked i ω sub q => .delcChecked (f i) ω (sub.map (·.map (itemRenum f))) (q.map f)
  | .deld ids => .deld (ids.map f)
  | .delc ids => .delc (ids.map f)
  | .core ids => .core (ids.map f)
  | .obju d g sub => .obju d g (sub.map (·.map (itemRenum f)))
  | .presChange a x c sub => .presChange a x c (sub.map (·.map (itemRenum f)))
  | t => t

/-- The constraint numbers of a conclusion. -/
private def conclIds : Conclusion → List ℕ
  | .unsat q | .bounds _ q _ _ | .enumComplete _ q => [q]
  | _ => []

/-- Renumber the constraint of a conclusion. -/
private def conclRenum (f : ℕ → ℕ) : Conclusion → Conclusion
  | .unsat q => .unsat (f q)
  | .bounds lb q ub a => .bounds lb (f q) ub a
  | .enumComplete n q => .enumComplete n (f q)
  | c => c

/-- **Trim a kernel proof**, as VeriPB's elaborator does: drop the top-level `pol` and `rup`
steps (those tagged with their number) whose constraint nothing kept refers to, take them out of
the deletions, and renumber. The kernel database then holds fewer constraints, which no rule of
the kernel format can tell apart from a weaker database: a dropped constraint is only derived,
never core, and no step propagates the whole database. Not applied when a step moves every
constraint to the core set, or with an output section, which compare the core set with a
formula. -/
private def trim (steps : Array (TopStep × Option ℕ)) (concl : Conclusion) (next : ℕ) :
    Array TopStep × Conclusion := Id.run do
  let mut needed : Array Bool := .replicate (next + 1) false
  for q in conclIds concl do needed := needed.set! q true
  let mut keep : Array Bool := .replicate steps.size true
  for k in [0:steps.size] do
    let i := steps.size - 1 - k
    let some (t, id?) := steps[i]? | continue
    match id? with
    | some k => if !needed[k]! then keep := keep.set! i false; continue
    | none => pure ()
    for r in topRefs t do needed := needed.set! r true
  -- The number of dropped constraints below each number.
  let mut dropped : Array Bool := .replicate (next + 1) false
  for (st, k) in steps.zip keep do
    if !k then if let some n := st.2 then dropped := dropped.set! n true
  let mut shift : Array ℕ := .mkEmpty (next + 1)
  let mut c := 0
  for n in [0:next + 1] do
    shift := shift.push c
    if dropped[n]! then c := c + 1
  let f (n : ℕ) : ℕ := n - shift[n]?.getD c
  let mut out : Array TopStep := #[]
  for (st, k) in steps.zip keep do
    if !k then continue
    let t := match st.1 with
      | .deld ids => TopStep.deld (ids.filter (!dropped[·]?.getD false))
      | t => t
    match t with
    | .deld [] => pure ()
    | t => out := out.push (topRenum f t)
  return (out, conclRenum f concl)

/-- The result of elaboration: the kernel proof, its output section (`none` for `NONE`, else the
guarantee and `FILE` (`true`) or `IMPLICIT`), and the variable names. -/
structure Result where
  /-- The kernel proof. -/
  proof : RedProof
  /-- The output section. -/
  output : Option (Guarantee × Bool)
  /-- The variable names: those of the instance, extended by those of the proof
  (`Cslib.Logic.PL.VeriPB.Text.Names.Extends`). -/
  names : Text.Names

/-- Elaborate the top-level rules up to the output section, after the kernel steps `out` (each
with the kernel number of its constraint if it may be trimmed); whether no rule forbids
trimming (`trimmable`). At most `fuel` rules are read, which
`Cslib.Logic.PL.VeriPB.Elab.Parse.fuelOf` takes above the number of bytes. -/
private def St.topSteps (S : St) :
    ℕ → Array (TopStep × Option ℕ) → Bool → EM (Array (TopStep × Option ℕ) × Bool)
  | 0, _, _ => S.fail "internal error: out of fuel"
  | fuel + 1, out, trimmable => do
    match ← Parse.step (Parse.fuelOf S.L) S.L with
    | some s =>
      let k₀ ← S.kerNext.get
      let ts ← S.top s
      let k₁ ← S.kerNext.get
      -- A single `pol` or `rup` step deriving one constraint may be trimmed.
      let tag := match ts.toList with
        | [.step (.pol _)] | [.step (.rup ..)] => if k₁ == k₀ + 1 then some k₀ else none
        | _ => none
      let mut out := out
      let mut trimmable := trimmable
      for t in ts do
        match t with
        | .strengthenToCore _ | .loadOrder .. => trimmable := false
        | _ => pure ()
        -- Short runs of deletions of derived constraints become one, which the kernel checker
        -- runs as one pass over its database (its duplicate check is quadratic in the list).
        match out.back?, t with
        | some (.deld a, _), .deld b =>
          if a.length + b.length ≤ 32 then out := out.pop.push (.deld (a ++ b), none)
          else out := out.push (t, tag)
        | _, t => out := out.push (t, tag)
      S.topSteps fuel out trimmable
    | none => return (out, trimmable)

/-- Run the elaborator. -/
private def St.run (S : St) (F : List PBConstr) : EM Result := do
  let mut kid := 1
  for c in F do
    let _ ← S.add c.normalize kid true false
    kid := kid + 1
  let n ← Parse.header S.L
  if let some n := n then
    if n != F.length then S.fail s!"f {n}: the formula has {F.length} constraints"
  let (out, trimmable) ← S.topSteps (Parse.fuelOf S.L) #[] true
  let (sec, concl) ← Parse.tail S.L
  let c ← S.conclusion concl
  let next ← S.kerNext.get
  let names ← liftPM S.L.namesOf
  -- Release the database, the engine and the tables before trimming, which builds a second copy
  -- of the kernel proof.
  set (⟨Lexer.init ⟨[], 0⟩, Engine.new, #[], 0, {}, {}, {}, none, none, none, {}, none, false,
    {}⟩ : Ext)
  let (steps, c) := if trimmable && sec.isNone then trim out c next else (out.map (·.1), c)
  return ⟨⟨steps.toList, c⟩, sec, names⟩

/-- **The elaborator**: the kernel proof of the augmented proof text `pbp` for the formula `F`,
the objective `obj` and the preserved set `pres`, whose variables are named by `N` (for an OPB
text, `Cslib.Logic.PL.VeriPB.Text.opbNames`; by default the standard names,
`Cslib.Logic.PL.VeriPB.Text.stdNames`), or an error message. The proof may refer to the
constraint `k` of `F`, numbered from `1`, by a label `l` with `(l, k)` in `labels`, a later pair
taking precedence (the labels of an instance, `Cslib.Logic.PL.VeriPB.Text.parseOPBLabelled`).
Untrusted: the result is meant to be checked by `Cslib.Logic.PL.VeriPB.checkRed`. -/
def elaborate (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ))
    (pbp : String) (N : Text.Names := Text.stdNames ⟨F, obj, pres⟩)
    (labels : List (String × ℕ) := []) : Except String Result :=
  -- The labels of the instance name its constraints, which keep their numbers `1, 2, …`.
  let e : Ext := ⟨Lexer.init N, Engine.new, #[default], F.length + 1, Std.HashMap.ofList labels, {},
    {}, none, obj, pres, {}, none, false, {}⟩
  match (St.run ⟨Lexer.new pbp N⟩ F).run e with
  | .ok r _ => .ok r
  | .error e _ => .error e

end Cslib.Logic.PL.VeriPB.Elab

end
