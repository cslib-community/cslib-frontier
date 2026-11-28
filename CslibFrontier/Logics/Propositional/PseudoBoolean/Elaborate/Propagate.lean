/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
public import Std.Data.HashMap

/-!
# Unit propagation with hints, for the VeriPB elaborator

A propagation engine over a database of pseudo-Boolean constraints that finds the hints of a
`rup` step: the constraints, in order, whose propagation from the negation of the constraint
reaches a conflict (`Cslib.Logic.PL.VeriPB.Elab.Engine.rupHints`). It serves the elaborator
(`Cslib.Logic.PL.VeriPB.Elab`), which turns the hintless `rup C;` of the augmented format of
VeriPB [Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023] into the
hinted `rup C : hints;` of the kernel format (§5.2.1 of the VeriPB/CakePB documentation,
22 June 2026 edition).

The engine is untrusted: it has no correctness theorem, and the hints it returns are checked by
the kernel checker (`Cslib.Logic.PL.VeriPB.rup`). It is written for compiled execution: its state
is one value, private to this module, updated in place by pure functions while it is uniquely
referenced. The engine's interface is `Cslib.Logic.PL.VeriPB.Elab.Engine.new` and the
operations `add`, `kill`, `rupHints` and `extend`, pure functions too. Its loops are total: those
over arrays by well-founded recursion, and the processing of the trail and the conflict analysis
with fuel above the length the trail can reach.

**Data.** A constraint is stored as its literal codes (`2 i` for the `i`-th variable met, `2 i + 1`
for its negation) and coefficients, sorted by decreasing coefficient, in two arrays shared by all
constraints, and its degree. A
constraint whose coefficients all reach a positive degree, with at least two terms, propagates as
a clause; it is watched by two literals. Every other constraint keeps a slack counter, updated
through occurrence lists, and propagates every unassigned term whose coefficient exceeds the
slack, as `Cslib.Logic.PL.VeriPB.propagate` does.

**Root level.** The propagations that the database makes on its own stay on the trail between
`rup` steps. Adding a constraint propagates it there; deleting a constraint that is the reason of
a root propagation, or the source of a root conflict, makes the engine rebuild the root level
before the next step.

**Hints.** After a conflict, the reasons of the literals the conflict needs are collected by
walking the trail backwards, a literal being needed when it falsifies a term of the conflicting
constraint or of the reason of a needed literal, earlier on the trail. The hints are these
reasons in trail order, a reason repeated on consecutive needed literals given once, then the
conflicting constraint. The kernel checker propagates each hint once, in order; a hint then forces
every needed literal it forced here, or meets a conflict earlier.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Elab

/-- A constraint of the engine: the position of its terms in the term arrays of the engine
(literal codes and coefficients, sorted by decreasing coefficient; a clause's first two literals
are its watches), their number, the degree, the slack of the empty assignment, whether it
propagates as a clause, and the kernel hint that names it. -/
private structure CRec where
  /-- The position of the first term. -/
  start : Nat
  /-- The number of terms. -/
  size : Nat
  /-- The degree. -/
  degree : Nat
  /-- The sum of the coefficients minus the degree. -/
  slack0 : Int
  /-- The constraint propagates as a clause and is watched by its first two literals. -/
  clause : Bool
  /-- The kernel hint naming the constraint. -/
  hint : Hint

private instance : Inhabited CRec := ⟨⟨0, 0, 0, 0, false, .neg⟩⟩

/-- The assignment of the engine. -/
private structure Asg where
  /-- The value of each literal code: `0` unassigned, `1` true, `2` false. -/
  value : ByteArray := .empty
  /-- The reason of each assigned variable. -/
  reason : Array ℕ := #[]
  /-- The trail position of each assigned variable. -/
  tpos : Array ℕ := #[]
  /-- The true literals, in order of assignment. -/
  trail : Array ℕ := #[]

private instance : Inhabited Asg := ⟨{}⟩

/-- The state of the propagation engine. -/
private structure EState where
  /-- The index of each variable met. -/
  varIdx : Std.HashMap ℕ ℕ := {}
  /-- The variable of each index. -/
  vars : Array ℕ := #[]
  /-- The constraints, by engine index; index `0` is unused. -/
  cons : Array CRec := #[default]
  /-- The position of the first term of each constraint, by engine index: the terms of `c` are
  those up to the next constraint's, or to the end. -/
  cpos : Array ℕ := #[0]
  /-- `1` for the constraints in the database, by engine index. -/
  alive : ByteArray := ⟨#[0]⟩
  /-- The literal codes of all constraints. -/
  lits : Array ℕ := #[]
  /-- The coefficients of all constraints, in the order of `lits`. -/
  coeffs : Array ℕ := #[]
  /-- The clauses watched by each literal, which are visited when it becomes false. -/
  watches : Array (Array ℕ) := #[]
  /-- The non-clause constraints containing each literal, with its coefficient, as consecutive
  pairs. -/
  occ : Array (Array ℕ) := #[]
  /-- The constraints that propagate on the empty assignment. -/
  roots : Array ℕ := #[]
  /-- The assignment. -/
  asg : Asg := {}
  /-- The trail entries whose falsified literal has been processed. -/
  qhead : ℕ := 0
  /-- The slack of each non-clause constraint under the processed part of the trail. -/
  slack : Array ℤ := #[0]
  /-- `1` for the constraints that are reasons of root propagations. -/
  rootReason : ByteArray := ⟨#[0]⟩
  /-- The length of the root trail. -/
  rootLen : ℕ := 0
  /-- A conflict of the database alone, if any. -/
  rootConflict : Option ℕ := none
  /-- The root level must be rebuilt before the next check. -/
  dirty : Bool := false
  /-- Marks on variables, for the conflict analysis; all clear between analyses. -/
  seen : ByteArray := .empty

/-- The propagation engine: its state, a value updated in place while it is uniquely referenced.
The state and its transitions are private; the engine is used through `new`, `add`, `kill`,
`rupHints` and `extend`. -/
-- `structureInType` cannot read a private field from outside this module and fails on it.
@[nolint structureInType]
structure Engine where
  private mk ::
  /-- The state. -/
  private st : EState

/-- The value of a literal code: `0` unassigned, `1` true, `2` false. -/
@[inline] private def litVal (value : ByteArray) (code : ℕ) : UInt8 := value.get! code

/-- Make the literal `code` true with the reason `r`. -/
@[inline] private def Asg.assign (a : Asg) (code r : ℕ) : Asg :=
  match a with
  | ⟨value, reason, tpos, trail⟩ =>
    let v := code / 2
    ⟨(value.set! code 1).set! (code ^^^ 1) 2, reason.set! v r, tpos.set! v trail.size,
      trail.push code⟩

/-- Propagate the non-clause constraint `c` with slack `sl` on the assignment `a`: make true every
unassigned term whose coefficient exceeds `sl`. -/
private def propagatePB (cons : Array CRec) (lits coeffs : Array ℕ) (c : ℕ) (sl : ℤ) (a : Asg) :
    Asg :=
  let r := cons[c]!
  go (r.start + r.size) r.start a
where
  /-- The terms from position `k` below `e`, while their coefficient exceeds `sl`. -/
  go (e k : ℕ) (a : Asg) : Asg :=
    if k < e && (coeffs[k]! : ℤ) > sl then
      let l := lits[k]!
      go e (k + 1) (if litVal a.value l == 0 then a.assign l c else a)
    else a
  termination_by e - k
  decreasing_by grind

/-- The results of the hot loops: a conflict, if any, the changed arrays, and the assignment,
whose parts are passed separately so that no structure is rebuilt per step. -/
private structure Hot where
  confl : Option ℕ
  arr : Array ℕ
  lits : Array ℕ
  watches : Array (Array ℕ)
  slack : Array ℤ
  value : ByteArray
  reason : Array ℕ
  tpos : Array ℕ
  trail : Array ℕ

private instance : Inhabited Hot := ⟨⟨none, #[], #[], #[], #[], .empty, #[], #[], #[]⟩⟩

/-- The non-clause part of processing a falsified literal: the pairs `os` of constraint and
coefficient from `i` on, the live ones written back from `j`. Every live slack is updated, so that
backtracking can undo it; the first constraint whose slack becomes negative is the conflict. The
result carries `os` as `arr`. -/
private def pbLoop (cons : Array CRec) (alive : ByteArray) (lits coeffs : Array ℕ)
    (watches : Array (Array ℕ)) (os : Array ℕ) (i j : ℕ) (confl : Option ℕ) (slack : Array ℤ)
    (value : ByteArray) (reason tpos trail : Array ℕ) : Hot :=
  if i + 1 < os.size then
    let c := os[i]!
    let w := os[i + 1]!
    if alive.get! c == 0 then
      pbLoop cons alive lits coeffs watches os (i + 2) j confl slack value reason tpos trail
    else
      let os := (os.set! j c).set! (j + 1) w
      let sl := slack[c]! - w
      let slack := slack.set! c sl
      if confl.isNone && sl < 0 then
        pbLoop cons alive lits coeffs watches os (i + 2) (j + 2) (some c) slack value reason
          tpos trail
      else if confl.isNone then
        match propagatePB cons lits coeffs c sl ⟨value, reason, tpos, trail⟩ with
        | ⟨value, reason, tpos, trail⟩ =>
          pbLoop cons alive lits coeffs watches os (i + 2) (j + 2) confl slack value reason tpos
            trail
      else
        pbLoop cons alive lits coeffs watches os (i + 2) (j + 2) confl slack value reason tpos trail
  else ⟨confl, os.shrink j, lits, watches, slack, value, reason, tpos, trail⟩
termination_by os.size - i
decreasing_by all_goals ((try simp only [Array.set!, Array.size_setIfInBounds]); omega)

/-- The first position from `k` below `e` whose literal is not false, or `e`. -/
private def nonFalse (lits : Array ℕ) (value : ByteArray) (k e : ℕ) : ℕ :=
  if k < e then if litVal value lits[k]! != 2 then k else nonFalse lits value (k + 1) e
  else e
termination_by e - k

/-- Copy the live entries of `ws` from `i` on to `j` on. -/
private def keepLive (alive : ByteArray) (ws : Array ℕ) (i j : ℕ) : Array ℕ :=
  if i < ws.size then
    let c := ws[i]!
    if alive.get! c == 0 then keepLive alive ws (i + 1) j
    else keepLive alive (ws.set! j c) (i + 1) (j + 1)
  else ws.shrink j
termination_by ws.size - i
decreasing_by all_goals ((try simp only [Array.set!, Array.size_setIfInBounds]); omega)

/-- The clause part of processing the falsified literal `f`: the clauses `ws` watched by `f` from
`i` on, those still watched by `f` written back from `j`. A clause whose other watch is true stays;
else its watch moves to a literal that is not false, or else the other watch is propagated or the
clause conflicts. After a conflict, the remaining live clauses stay. The result carries `ws` as
`arr`. -/
private def watchLoop (cpos : Array ℕ) (alive : ByteArray) (f : ℕ) (ws : Array ℕ)
    (i j : ℕ) (lits : Array ℕ) (watches : Array (Array ℕ)) (slack : Array ℤ) (value : ByteArray)
    (reason tpos trail : Array ℕ) : Hot :=
  if i < ws.size then
    let c := ws[i]!
    if alive.get! c == 0 then
      watchLoop cpos alive f ws (i + 1) j lits watches slack value reason tpos trail
    else
      let p := cpos[c]!
      -- The literal `f` goes to the second watch.
      let lits := if lits[p]! == f then lits.swapIfInBounds p (p + 1) else lits
      let o := lits[p]!
      let vo := litVal value o
      if vo == 1 then
        watchLoop cpos alive f (ws.set! j c) (i + 1) (j + 1) lits watches slack value reason tpos
          trail
      else
        let e := if c + 1 < cpos.size then cpos[c + 1]! else lits.size
        let k := nonFalse lits value (p + 2) e
        if k < e then
          let lits := lits.swapIfInBounds (p + 1) k
          let watches := watches.modify lits[p + 1]! (·.push c)
          watchLoop cpos alive f ws (i + 1) j lits watches slack value reason tpos trail
        else
          let ws := ws.set! j c
          if vo == 0 then
            -- Propagate the other watch.
            match Asg.assign ⟨value, reason, tpos, trail⟩ o c with
            | ⟨value, reason, tpos, trail⟩ =>
              watchLoop cpos alive f ws (i + 1) (j + 1) lits watches slack value reason tpos trail
          else
            -- A conflict: keep the remaining live clauses.
            ⟨some c, keepLive alive ws (i + 1) (j + 1), lits, watches, slack, value, reason, tpos,
              trail⟩
  else ⟨none, ws.shrink j, lits, watches, slack, value, reason, tpos, trail⟩
termination_by ws.size - i
decreasing_by all_goals ((try simp only [Array.set!, Array.size_setIfInBounds]); omega)

/-- Process the trail from `qhead` until a conflict or until every entry is processed: for each
entry, the slacks of the non-clause constraints containing its negation, then the clauses
watching it. The slack updates of an entry are always completed, so that backtracking can undo
them. Returns the new `qhead` and the occurrence lists with the other results. The number of
entries processed is bounded by `fuel`, which the caller takes above the number of literal codes,
a bound on the length of the trail: with the fuel spent, the entries left are not processed. -/
private def propLoop (cons : Array CRec) (cpos : Array ℕ) (alive : ByteArray)
    (coeffs : Array ℕ) (fuel : ℕ)
    (qhead : ℕ) (lits : Array ℕ) (watches occ : Array (Array ℕ)) (slack : Array ℤ)
    (value : ByteArray) (reason tpos trail : Array ℕ) : ℕ × Array (Array ℕ) × Hot :=
  match fuel with
  | 0 => (qhead, occ, ⟨none, #[], lits, watches, slack, value, reason, tpos, trail⟩)
  | fuel + 1 =>
  if qhead < trail.size then
    let f := trail[qhead]! ^^^ 1
    let (os, occ) := occ.swapAt! f #[]
    match pbLoop cons alive lits coeffs watches os 0 0 none slack value reason tpos trail with
    | ⟨confl, os, lits, watches, slack, value, reason, tpos, trail⟩ =>
      let occ := occ.set! f os
      if confl.isSome then
        (qhead + 1, occ, ⟨confl, #[], lits, watches, slack, value, reason, tpos, trail⟩)
      else
        let (ws, watches) := watches.swapAt! f #[]
        match watchLoop cpos alive f ws 0 0 lits watches slack value reason tpos trail with
        | ⟨confl, ws, lits, watches, slack, value, reason, tpos, trail⟩ =>
          let watches := watches.set! f ws
          if confl.isSome then
            (qhead + 1, occ, ⟨confl, #[], lits, watches, slack, value, reason, tpos, trail⟩)
          else
            propLoop cons cpos alive coeffs fuel (qhead + 1) lits watches occ slack value reason
              tpos trail
  else (qhead, occ, ⟨none, #[], lits, watches, slack, value, reason, tpos, trail⟩)

namespace EState

/-- Set the byte `i` to `v`, or push it if `i` is the size. -/
@[inline] private def setPush (b : ByteArray) (i : ℕ) (v : UInt8) : ByteArray :=
  if i < b.size then b.set! i v else b.push v

/-- The code of a literal, registering its variable if it is new. -/
private def litCode (s : EState) (l : Literal ℕ) : EState × ℕ :=
  let sign := if l.2 then 0 else 1
  match s.varIdx[l.1]? with
  | some i => (s, 2 * i + sign)
  | none =>
    let i := s.vars.size
    let s := { s with varIdx := s.varIdx.insert l.1 i }
    let s := { s with vars := s.vars.push l.1 }
    let s := { s with asg := match s.asg with
      | ⟨value, reason, tpos, trail⟩ =>
        ⟨(value.push 0).push 0, reason.push 0, tpos.push 0, trail⟩ }
    let s := { s with watches := (s.watches.push #[]).push #[] }
    let s := { s with occ := (s.occ.push #[]).push #[] }
    (s, 2 * i + sign)

/-- The terms of `c` with positive coefficients, as coefficients and literal codes, sorted by
decreasing coefficient. -/
private def codes (s : EState) (c : PBConstr) : EState × Array (ℕ × ℕ) := Id.run do
  let mut s := s
  let mut ts : Array (ℕ × ℕ) := #[]
  for t in c.terms do
    if t.1 > 0 then
      let (s', code) := s.litCode t.2
      s := s'
      ts := ts.push (t.1, code)
  return (s, ts.qsort (fun a b => a.1 > b.1))

/-- Make the literal `code` true with the reason `r`. -/
private def assign (s : EState) (code r : ℕ) : EState := { s with asg := s.asg.assign code r }

/-- Propagate the non-clause constraint `c` with slack `sl`. -/
private def propagatePB (s : EState) (c : ℕ) (sl : ℤ) : EState :=
  { s with asg := Elab.propagatePB s.cons s.lits s.coeffs c sl s.asg }

/-- Process the trail until a conflict or until every entry is processed. -/
private def propagate (s : EState) : EState × Option ℕ :=
  match s with
  | ⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots,
      ⟨value, reason, tpos, trail⟩, qhead, slack, rootReason, rootLen, rootConflict, dirty, seen⟩ =>
    match propLoop cons cpos alive coeffs (value.size + 1) qhead lits watches occ slack value
      reason tpos trail with
    | (qhead, occ, ⟨confl, _, lits, watches, slack, value, reason, tpos, trail⟩) =>
      (⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots,
        ⟨value, reason, tpos, trail⟩, qhead, slack, rootReason, rootLen, rootConflict, dirty,
        seen⟩, confl)

/-- Undo the trail from position `i` down to length `n`, restoring the slacks of the entries
below `q`, which were processed. -/
private def undo (occ : Array (Array ℕ)) (q n i : ℕ) (slack : Array ℤ) (a : Asg) :
    Array ℤ × Asg :=
  if n < i then
    let i := i - 1
    let t := a.trail[i]!
    let slack := if i < q then restore occ[t ^^^ 1]! 0 slack else slack
    undo occ q n i slack { a with value := (a.value.set! t 0).set! (t ^^^ 1) 0 }
  else (slack, { a with trail := a.trail.shrink n })
termination_by i
where
  /-- Add back the coefficients of the pairs `os` from `k` on. -/
  restore (os : Array ℕ) (k : ℕ) (slack : Array ℤ) : Array ℤ :=
    if k + 1 < os.size then restore os (k + 2) (slack.modify os[k]! (· + os[k + 1]!)) else slack
  termination_by os.size - k

/-- Undo the trail down to length `n`, restoring the slacks of the processed entries. -/
private def backtrack (s : EState) (n : ℕ) : EState :=
  match s with
  | ⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots, asg, qhead, slack,
      rootReason, rootLen, rootConflict, dirty, seen⟩ =>
    let size := asg.trail.size
    let (slack, asg) := undo occ qhead n size slack asg
    ⟨varIdx, vars, cons, cpos, alive, lits, coeffs, watches, occ, roots, asg, min qhead n, slack,
      rootReason, rootLen, rootConflict, dirty, seen⟩

/-- Mark the reasons of the trail entries from `n` as root reasons. -/
private def markRootReasons (s : EState) (n : ℕ) : EState := Id.run do
  let mut s := s
  for i in [n:s.asg.trail.size] do
    let r := s.asg.reason[s.asg.trail[i]! / 2]!
    s := { s with rootReason := s.rootReason.set! r 1 }
  return s

/-- The slack of the terms at positions `[p, p + m)` with degree `d` under the processed part of
the trail: a literal counts as false only once its falsification has been processed. -/
private def freshSlack (s : EState) (p m d : ℕ) : ℤ := Id.run do
  let mut sl : ℤ := -(d : ℤ)
  for k in [p:p + m] do
    let l := s.lits[k]!
    if !(litVal s.asg.value l == 2 && s.asg.tpos[l / 2]! < s.qhead) then sl := sl + s.coeffs[k]!
  return sl

/-- Propagate the constraint `c`, just added at the root level or checked during a rebuild,
from scratch: its slack under the current assignment, then a conflict or its propagations. The
processed part of the trail must be the whole trail. -/
private def checkFresh (s : EState) (c : ℕ) : EState × Option ℕ := Id.run do
  let r := s.cons[c]!
  let p := r.start
  let sl := s.freshSlack p r.size r.degree
  if r.clause then
    -- A clause with at least two terms: watch two non-false literals, if possible.
    let mut s := s
    let mut j := 0
    for k in [0:r.size] do
      if j < 2 && litVal s.asg.value s.lits[p + k]! != 2 then
        s := { s with lits := s.lits.swapIfInBounds (p + j) (p + k) }
        j := j + 1
    let w₀ := s.lits[p]!
    let w₁ := s.lits[p + 1]!
    s := { s with watches := (s.watches.modify w₀ (·.push c)).modify w₁ (·.push c) }
    if sl < 0 then return (s, some c)
    if j == 1 && litVal s.asg.value w₀ == 0 then s := s.assign w₀ c
    return (s, none)
  else
    let s := { s with slack := s.slack.set! c sl }
    if sl < 0 then return (s, some c)
    return (s.propagatePB c sl, none)

/-- Push a constraint with the sorted terms `ts`, the degree `d` and the hint `h`, whether it
propagates as a clause; returns its engine index. -/
private def pushCons (s : EState) (ts : Array (ℕ × ℕ)) (d : ℕ) (slack0 : ℤ) (clause : Bool)
    (h : Hint) : EState × ℕ := Id.run do
  let i := s.cons.size
  let start := s.lits.size
  let mut s := { s with cons := s.cons.push ⟨start, ts.size, d, slack0, clause, h⟩ }
  s := { s with cpos := s.cpos.push start }
  for (a, l) in ts do
    s := { s with lits := s.lits.push l }
    s := { s with coeffs := s.coeffs.push a }
  s := { s with alive := setPush s.alive i 1 }
  s := { s with rootReason := setPush s.rootReason i 0 }
  s := { s with slack := s.slack.push 0 }
  if !clause && 0 < d then
    for (a, l) in ts do
      s := { s with occ := s.occ.modify l (·.push i |>.push a) }
  return (s, i)

/-- Add a constraint at the root level, named by the kernel hint `h`; returns its engine
index. -/
private def add (s : EState) (c : PBConstr) (h : Hint) : EState × ℕ := Id.run do
  let (s, ts) := s.codes c
  let total : ℕ := ts.foldl (fun t x => t + x.1) 0
  let clause := 2 ≤ ts.size && 0 < c.degree && ts.all (c.degree ≤ ·.1)
  let (s, i) := s.pushCons ts c.degree ((total : ℤ) - c.degree) clause h
  let mut s := s
  if (total : ℤ) - c.degree < (((ts[0]?.map (·.1)).getD 0 : ℕ) : ℤ) || total < c.degree then
    s := { s with roots := s.roots.push i }
  if s.dirty || s.rootConflict.isSome then
    -- The root level is rebuilt or already in conflict; only record the slack.
    let r := s.cons[i]!
    if !clause then s := { s with slack := s.slack.set! i (s.freshSlack r.start r.size r.degree) }
    else
      let w₀ := s.lits[r.start]!
      let w₁ := s.lits[r.start + 1]!
      s := { s with watches := (s.watches.modify w₀ (·.push i)).modify w₁ (·.push i) }
    if s.rootConflict.isSome then s := { s with dirty := true }
    return (s, i)
  let n := s.asg.trail.size
  let (s', confl) := match s.checkFresh i with
    | (s, some k) => (s, some k)
    | (s, none) => s.propagate
  s := s'.markRootReasons n
  s := { s with rootLen := s.asg.trail.size }
  if confl.isSome then s := { s with rootConflict := confl }
  return (s, i)

/-- Delete the constraint with engine index `i`. -/
private def kill (s : EState) (i : ℕ) : EState :=
  let s := { s with alive := s.alive.set! i 0 }
  if s.rootReason.get! i != 0 || s.rootConflict == some i then { s with dirty := true } else s

/-- Rebuild the root level: undo it, and propagate the constraints that propagate on the empty
assignment. -/
private def rebuild (s : EState) : EState := Id.run do
  let mut s := s.backtrack 0
  s := { s with rootConflict := none }
  s := { s with rootReason := ⟨.replicate s.rootReason.size 0⟩ }
  let roots := s.roots.filter fun i => s.alive.get! i != 0
  s := { s with roots := roots }
  let mut confl := none
  for i in roots do
    if confl.isNone then
      let r := s.cons[i]!
      -- The constraint's slack is up to date; it propagates at most its own terms.
      let sl : ℤ := if r.clause then r.slack0 else s.slack[i]!
      if sl < 0 then confl := some i
      else
        if !r.clause then s := s.propagatePB i sl
        let (s', c) := s.propagate
        s := s'
        confl := c
  s := s.markRootReasons 0
  s := { s with rootLen := s.asg.trail.size }
  s := { s with rootConflict := confl }
  return { s with dirty := false }

/-- Restore the max-heap order of `h` above position `i`. -/
private def siftUp (h : Array ℕ) (i : ℕ) : Array ℕ :=
  if 0 < i && h[(i - 1) / 2]! < h[i]! then siftUp (h.swapIfInBounds i ((i - 1) / 2)) ((i - 1) / 2)
  else h
termination_by i
decreasing_by grind

/-- Restore the max-heap order of `h` below position `i`. -/
private def siftDown (h : Array ℕ) (i : ℕ) : Array ℕ :=
  let l := 2 * i + 1
  let r := 2 * i + 2
  let m := if l < h.size && h[i]! < h[l]! then l else i
  let m := if r < h.size && h[m]! < h[r]! then r else m
  if _hm : m == i then h else siftDown (h.swapIfInBounds i m) m
termination_by h.size - i
decreasing_by simp only [Array.size_swapIfInBounds]; grind

/-- Mark the variables of the false literals at positions `[q, e)` of `lits` assigned below the
trail position `lim` and not marked yet (`seen`), pushing their trail positions onto the
max-heap `heap`. -/
private def markLits (lits tpos : Array ℕ) (value : ByteArray) (q e lim : ℕ)
    (seen : ByteArray) (heap : Array ℕ) : ByteArray × Array ℕ :=
  if q < e then
    let l := lits[q]!
    let v := l / 2
    if litVal value l == 2 && tpos[v]! < lim && seen.get! v == 0 then
      markLits lits tpos value (q + 1) e lim (seen.set! v 1) (siftUp (heap.push tpos[v]!) heap.size)
    else markLits lits tpos value (q + 1) e lim seen heap
  else (seen, heap)
termination_by e - q

/-- Process the marked trail positions `heap`, latest first: record the reason of each (once for
consecutive repeats) and mark the false literals of the reason assigned before it; unmark the
variables processed. The number of positions processed is bounded by `fuel`, which the caller
takes above the length of the trail: each position is pushed at most once. -/
private def collect (cons : Array CRec) (lits tpos reason trail : Array ℕ)
    (value : ByteArray) (fuel : ℕ) (seen : ByteArray) (heap out : Array ℕ) :
    ByteArray × Array ℕ :=
  match fuel with
  | 0 => (seen, out)
  | fuel + 1 =>
  if h : 0 < heap.size then
    let p := heap[0]
    let heap := siftDown (heap.swapIfInBounds 0 (heap.size - 1)).pop 0
    let v := trail[p]! / 2
    let r := reason[v]!
    let out := if out.size == 0 || out[out.size - 1]! != r then out.push r else out
    let rc := cons[r]!
    match markLits lits tpos value rc.start (rc.start + rc.size) p (seen.set! v 0) heap with
    | (seen, heap) => collect cons lits tpos reason trail value fuel seen heap out
  else (seen, out)

/-- The kernel hints of a conflict at the constraint `k`: the reasons of the needed literals, in
trail order, a reason repeated on consecutive needed literals given once, then `k`. A literal is
needed when it falsifies a term of `k`, or of the reason of a needed literal, earlier on the
trail. The marks (`seen`) are clear again afterwards. -/
private def analyze (s : EState) (k : ℕ) : EState × Array Hint :=
  let seen := s.seen
  let s := { s with seen := .empty }
  let seen := if seen.size < s.vars.size then
      ⟨seen.data ++ .replicate (s.vars.size - seen.size) 0⟩ else seen
  let rk := s.cons[k]!
  let a := s.asg
  let (seen, heap) :=
    markLits s.lits a.tpos a.value rk.start (rk.start + rk.size) a.trail.size seen #[]
  let (seen, out) :=
    collect s.cons s.lits a.tpos a.reason a.trail a.value (a.trail.size + 1) seen heap #[]
  ({ s with seen := seen }, (out.reverse.map (s.cons[·]!.hint)).push rk.hint)

/-- **The hints of `rup C`**, given the negation `neg` of `C`: propagate the database and `neg`,
and on a conflict return its hints (`analyze`), `neg` being
named `~`. Returns `none` when propagation reaches no conflict. The negation is removed again. -/
private def rupHints (s : EState) (neg : PBConstr) : EState × Option (Array Hint) := Id.run do
  let s := if s.dirty then s.rebuild else s
  if let some k := s.rootConflict then
    let (s, h) := s.analyze k
    return (s, some h)
  let rl := s.rootLen
  -- The negation, as a non-clause constraint of its own, the last one.
  let (s, ts) := s.codes neg
  let (s, i) := s.pushCons ts neg.degree 0 false .neg
  let start := s.cons[i]!.start
  let (s, confl) := match s.checkFresh i with
    | (s, some k) => (s, some k)
    | (s, none) => s.propagate
  let (s, res) := match confl with
    | some k => let (s, h) := s.analyze k; (s, some h)
    | none => (s, none)
  let mut s := s.backtrack rl
  -- Remove the negation: its occurrences are the last pair of each of its lists.
  if 0 < neg.degree then
    for (_, l) in ts do
      s := { s with occ := s.occ.modify l (·.pop.pop) }
  s := { s with cons := s.cons.pop }
  s := { s with cpos := s.cpos.pop }
  s := { s with alive := s.alive.set! i 0 }
  s := { s with slack := s.slack.pop }
  s := { s with lits := s.lits.shrink start }
  s := { s with coeffs := s.coeffs.shrink start }
  return (s, res)

/-- **Extend a partial assignment by propagation**, as VeriPB does for a logged solution
(§5.8.1): make the literals `ls` true, propagate the database, and return every assigned
literal; `none` on a conflict. -/
private def extend (s : EState) (ls : List (Literal ℕ)) :
    EState × Option (Array (Literal ℕ)) := Id.run do
  let s := if s.dirty then s.rebuild else s
  if s.rootConflict.isSome then return (s, none)
  let rl := s.rootLen
  let mut s := s
  let mut ok := true
  for l in ls do
    let (s', code) := s.litCode l
    s := s'
    let v := litVal s.asg.value code
    if v == 0 then s := s.assign code 0
    else if v == 2 then ok := false
  if ok then
    let (s', c) := s.propagate
    s := s'
    ok := c.isNone
  let res := if ok then some (s.asg.trail.map fun c => (s.vars[c / 2]!, c % 2 == 0)) else none
  return (s.backtrack rl, res)

end EState

namespace Engine

/-- A new empty engine. -/
def new : Engine := ⟨{}⟩

/-- Add a constraint at the root level, named by the kernel hint `h`, and propagate it there;
returns its engine index. -/
def add (e : Engine) (c : PBConstr) (h : Hint) : Engine × ℕ :=
  let (s, i) := e.st.add c h
  (⟨s⟩, i)

/-- Delete the constraint with engine index `i`; the root level is rebuilt before the next
step if the constraint was the reason of a root propagation or a root conflict. -/
def kill (e : Engine) (i : ℕ) : Engine := ⟨e.st.kill i⟩

/-- **The hints of `rup C`**, given the negation `neg` of `C`: propagate the database and `neg`,
and on a conflict return the reasons of the literals the conflict needs, in trail order, then
the conflicting constraint, `neg` being named `~`. Returns `none` when propagation reaches no
conflict. The negation is removed again. -/
def rupHints (e : Engine) (neg : PBConstr) : Engine × Option (Array Hint) :=
  let (s, r) := e.st.rupHints neg
  (⟨s⟩, r)

/-- **Extend a partial assignment by propagation**, as VeriPB does for a logged solution
(§5.8.1): make the literals `ls` true, propagate the database, and return every assigned
literal; `none` on a conflict. -/
def extend (e : Engine) (ls : List (Literal ℕ)) : Engine × Option (Array (Literal ℕ)) :=
  let (s, r) := e.st.extend ls
  (⟨s⟩, r)

end Engine

end Cslib.Logic.PL.VeriPB.Elab

end
