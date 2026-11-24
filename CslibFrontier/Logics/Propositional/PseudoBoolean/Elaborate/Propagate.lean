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
the kernel checker (`Cslib.Logic.PL.VeriPB.rup`). It is written for compiled execution, with
arrays and mutable references in `ST`, and the kernel cannot evaluate it.

**Data.** A constraint is stored as its literal codes (`2 i` for the `i`-th variable met, `2 i + 1`
for its negation) and coefficients, sorted by decreasing coefficient, and its degree. A
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

/-- A constraint of the engine: literal codes and coefficients, sorted by decreasing coefficient
(a clause's first two literals are its watches), the degree, the slack of the empty assignment,
whether it propagates as a clause, whether it is still in the database, and the kernel hint that
names it. -/
structure CRec where
  /-- The literal codes. -/
  lits : Array Nat
  /-- The coefficients, in the order of `lits`. -/
  coeffs : Array Nat
  /-- The degree. -/
  degree : Nat
  /-- The sum of the coefficients minus the degree. -/
  slack0 : Int
  /-- The constraint propagates as a clause and is watched by its first two literals. -/
  clause : Bool
  /-- The constraint is in the database. -/
  alive : Bool
  /-- The kernel hint naming the constraint. -/
  hint : Hint

instance : Inhabited CRec := ⟨⟨#[], #[], 0, 0, false, false, .neg⟩⟩

/-- The state of the propagation engine, as mutable references. -/
structure Engine (σ : Type) where
  /-- The index of each variable met. -/
  varIdx : ST.Ref σ (Std.HashMap ℕ ℕ)
  /-- The variable of each index. -/
  vars : ST.Ref σ (Array ℕ)
  /-- The constraints, by engine index. -/
  cons : ST.Ref σ (Array CRec)
  /-- The clauses watched by each literal, which are visited when it becomes false. -/
  watches : ST.Ref σ (Array (Array ℕ))
  /-- The non-clause constraints containing each literal, with its coefficient. -/
  occ : ST.Ref σ (Array (Array (ℕ × ℕ)))
  /-- The constraints that propagate on the empty assignment. -/
  roots : ST.Ref σ (Array ℕ)
  /-- The value of each variable: `0` unassigned, `1` true, `2` false. -/
  value : ST.Ref σ ByteArray
  /-- The reason of each assigned variable. -/
  reason : ST.Ref σ (Array ℕ)
  /-- The trail position of each assigned variable. -/
  tpos : ST.Ref σ (Array ℕ)
  /-- The true literals, in order of assignment. -/
  trail : ST.Ref σ (Array ℕ)
  /-- The trail entries whose falsified literal has been processed. -/
  qhead : ST.Ref σ ℕ
  /-- The slack of each non-clause constraint under the processed part of the trail. -/
  slack : ST.Ref σ (Array ℤ)
  /-- The constraints that are reasons of root propagations. -/
  rootReason : ST.Ref σ ByteArray
  /-- The length of the root trail. -/
  rootLen : ST.Ref σ ℕ
  /-- A conflict of the database alone, if any. -/
  rootConflict : ST.Ref σ (Option ℕ)
  /-- The root level must be rebuilt before the next check. -/
  dirty : ST.Ref σ Bool

namespace Engine

variable {σ : Type}

/-- A new empty engine. -/
def new : ST σ (Engine σ) := do
  return {
    varIdx := ← ST.mkRef {}, vars := ← ST.mkRef #[], cons := ← ST.mkRef #[default],
    watches := ← ST.mkRef #[],
    occ := ← ST.mkRef #[], roots := ← ST.mkRef #[], value := ← ST.mkRef ByteArray.empty,
    reason := ← ST.mkRef #[], tpos := ← ST.mkRef #[], trail := ← ST.mkRef #[],
    qhead := ← ST.mkRef 0, slack := ← ST.mkRef #[0], rootReason := ← ST.mkRef (.mk #[0]),
    rootLen := ← ST.mkRef 0, rootConflict := ← ST.mkRef none, dirty := ← ST.mkRef false }

/-- The code of a literal, registering its variable if it is new. -/
private def litCode (e : Engine σ) (l : Literal ℕ) : ST σ ℕ := do
  let m ← e.varIdx.get
  let i ← match m[l.1]? with
    | some i => pure i
    | none =>
      let i := m.size
      e.varIdx.modify (·.insert l.1 i)
      e.vars.modify (·.push l.1)
      e.value.modify (·.push 0)
      e.reason.modify (·.push 0)
      e.tpos.modify (·.push 0)
      e.watches.modify fun w => (w.push #[]).push #[]
      e.occ.modify fun o => (o.push #[]).push #[]
      pure i
  return 2 * i + (if l.2 then 0 else 1)

/-- The value of a literal code: `0` unassigned, `1` true, `2` false. -/
@[inline] private def litVal (value : ByteArray) (code : ℕ) : UInt8 :=
  let v := value.get! (code / 2)
  if v == 0 then 0 else if (v == 1) == (code % 2 == 0) then 1 else 2

/-- Make the literal `code` true with the reason `r`. -/
private def assign (e : Engine σ) (code r : ℕ) : ST σ Unit := do
  let v := code / 2
  let n := (← e.trail.get).size
  e.value.modify (·.set! v (if code % 2 == 0 then 1 else 2))
  e.reason.modify (·.set! v r)
  e.tpos.modify (·.set! v n)
  e.trail.modify (·.push code)

/-- Propagate the non-clause constraint `c` with slack `s`: make true every unassigned term whose
coefficient exceeds `s`. -/
private def propagatePB (e : Engine σ) (c : ℕ) (s : ℤ) : ST σ Unit := do
  let r := (← e.cons.get)[c]!
  let mut k := 0
  while k < r.lits.size && (r.coeffs[k]! : ℤ) > s do
    if litVal (← e.value.get) r.lits[k]! == 0 then e.assign r.lits[k]! c
    k := k + 1

/-- Process the falsification of the literal `f`: update the slacks of the non-clause
constraints containing it, and visit the clauses watching it. Returns a conflicting constraint,
if any. The slack updates are always completed, so that backtracking can undo them. -/
private def falsify (e : Engine σ) (f : ℕ) : ST σ (Option ℕ) := do
  let mut confl : Option ℕ := none
  -- Non-clause constraints.
  let os := (← e.occ.get)[f]!
  let mut keep : Array (ℕ × ℕ) := Array.mkEmpty os.size
  for (c, a) in os do
    if (← e.cons.get)[c]!.alive then
      keep := keep.push (c, a)
      let s := (← e.slack.get)[c]! - a
      e.slack.modify (·.set! c s)
      if confl.isNone then
        if s < 0 then confl := some c
        else e.propagatePB c s
  if keep.size < os.size then e.occ.modify (·.set! f keep)
  if confl.isSome then return confl
  -- Clauses.
  let ws := (← e.watches.get)[f]!
  e.watches.modify (·.set! f #[])
  let mut kept : Array ℕ := Array.mkEmpty ws.size
  let mut i := 0
  while i < ws.size do
    let c := ws[i]!
    i := i + 1
    let r := (← e.cons.get)[c]!
    if !r.alive then continue
    if confl.isSome then kept := kept.push c; continue
    let mut lits := r.lits
    if lits[0]! == f then lits := lits.swapIfInBounds 0 1
    let value ← e.value.get
    if litVal value lits[0]! == 1 then
      if lits[1]! != r.lits[1]! then e.cons.modify (·.modify c ({ · with lits := lits }))
      kept := kept.push c
      continue
    let mut k := 2
    let mut found := false
    while k < lits.size && !found do
      if litVal value lits[k]! != 2 then found := true else k := k + 1
    if found then
      lits := lits.swapIfInBounds 1 k
      e.cons.modify (·.modify c ({ · with lits := lits }))
      e.watches.modify fun w => w.modify lits[1]! (·.push c)
    else
      if lits[1]! != r.lits[1]! then e.cons.modify (·.modify c ({ · with lits := lits }))
      kept := kept.push c
      if litVal value lits[0]! == 0 then e.assign lits[0]! c
      else confl := some c
  e.watches.modify fun w => w.modify f (· ++ kept)
  return confl

/-- Process the trail until a conflict or until every entry is processed. -/
private def propagate (e : Engine σ) : ST σ (Option ℕ) := do
  let mut confl := none
  while confl.isNone && (← e.qhead.get) < (← e.trail.get).size do
    let q ← e.qhead.get
    e.qhead.set (q + 1)
    confl ← e.falsify ((← e.trail.get)[q]! ^^^ 1)
  return confl

/-- Undo the trail down to length `n`, restoring the slacks of the processed entries. -/
private def backtrack (e : Engine σ) (n : ℕ) : ST σ Unit := do
  let q ← e.qhead.get
  let trail ← e.trail.get
  let mut i := trail.size
  while n < i do
    i := i - 1
    let t := trail[i]!
    if i < q then
      for (c, a) in (← e.occ.get)[t ^^^ 1]! do
        e.slack.modify fun s => s.modify c (· + a)
    e.value.modify (·.set! (t / 2) 0)
  e.trail.modify (·.shrink n)
  e.qhead.set (min q n)

/-- Mark the reasons of the trail entries from `n` as root reasons. -/
private def markRootReasons (e : Engine σ) (n : ℕ) : ST σ Unit := do
  let trail ← e.trail.get
  for i in [n:trail.size] do
    let r := (← e.reason.get)[trail[i]! / 2]!
    e.rootReason.modify (·.set! r 1)

/-- The slack of the terms `lits`, `coeffs` with degree `d` under the processed part of the
trail: a literal counts as false only once its falsification has been processed. -/
private def freshSlack (e : Engine σ) (lits coeffs : Array ℕ) (d : ℕ) : ST σ ℤ := do
  let value ← e.value.get
  let tpos ← e.tpos.get
  let q ← e.qhead.get
  let mut s : ℤ := -(d : ℤ)
  for k in [0:lits.size] do
    if !(litVal value lits[k]! == 2 && tpos[lits[k]! / 2]! < q) then s := s + coeffs[k]!
  return s

/-- Propagate the constraint `c`, just added at the root level or checked during a rebuild,
from scratch: its slack under the current assignment, then a conflict or its propagations. The
processed part of the trail must be the whole trail. -/
private def checkFresh (e : Engine σ) (c : ℕ) : ST σ (Option ℕ) := do
  let r := (← e.cons.get)[c]!
  let value ← e.value.get
  let s ← e.freshSlack r.lits r.coeffs r.degree
  if r.clause then
    -- A clause with at least two terms: watch two non-false literals, if possible.
    let mut lits := r.lits
    let mut j := 0
    for k in [0:lits.size] do
      if j < 2 && litVal value lits[k]! != 2 then
        lits := lits.swapIfInBounds j k
        j := j + 1
    e.cons.modify (·.modify c ({ · with lits := lits }))
    e.watches.modify fun w => (w.modify lits[0]! (·.push c)).modify lits[1]! (·.push c)
    if s < 0 then return some c
    if j == 1 && litVal value lits[0]! == 0 then e.assign lits[0]! c
    return none
  else
    e.slack.modify (·.set! c s)
    if s < 0 then return some c
    e.propagatePB c s
    return none

/-- Add a constraint at the root level, named by the kernel hint `h`; returns its engine
index. -/
def add (e : Engine σ) (c : PBConstr) (h : Hint) : ST σ ℕ := do
  let mut ts : Array (ℕ × ℕ) := #[]
  for t in c.terms do
    if t.1 > 0 then ts := ts.push (t.1, ← e.litCode t.2)
  let sorted := ts.qsort (fun a b => a.1 > b.1)
  let coeffs := sorted.map (·.1)
  let lits := sorted.map (·.2)
  let total := (coeffs.foldl (· + ·) 0 : ℕ)
  let clause := 2 ≤ lits.size && 0 < c.degree && coeffs.all (c.degree ≤ ·)
  let i := (← e.cons.get).size
  e.cons.modify (·.push ⟨lits, coeffs, c.degree, (total : ℤ) - c.degree, clause, true, h⟩)
  e.slack.modify (·.push 0)
  e.rootReason.modify (·.push 0)
  if !clause && 0 < c.degree then
    for k in [0:lits.size] do
      e.occ.modify fun o => o.modify lits[k]! (·.push (i, coeffs[k]!))
  if (total : ℤ) - c.degree < ((coeffs[0]?.getD 0 : ℕ) : ℤ) || total < c.degree then
    e.roots.modify (·.push i)
  if (← e.dirty.get) || (← e.rootConflict.get).isSome then
    -- The root level is rebuilt or already in conflict; only record the slack.
    if !clause then e.slack.modify (·.set! i (← e.freshSlack lits coeffs c.degree))
    else
      e.watches.modify fun w => (w.modify lits[0]! (·.push i)).modify lits[1]! (·.push i)
    if (← e.rootConflict.get).isSome then e.dirty.set true
    return i
  let n := (← e.trail.get).size
  let confl ← match ← e.checkFresh i with
    | some k => pure (some k)
    | none => e.propagate
  e.markRootReasons n
  e.rootLen.set (← e.trail.get).size
  if confl.isSome then e.rootConflict.set confl
  return i

/-- Delete the constraint with engine index `i`. -/
def kill (e : Engine σ) (i : ℕ) : ST σ Unit := do
  e.cons.modify (·.modify i ({ · with alive := false }))
  if (← e.rootReason.get).get! i != 0 || (← e.rootConflict.get) == some i then e.dirty.set true

/-- Rebuild the root level: undo it, and propagate the constraints that propagate on the empty
assignment. -/
private def rebuild (e : Engine σ) : ST σ Unit := do
  e.backtrack 0
  e.rootConflict.set none
  e.rootReason.modify fun b => ⟨b.data.map fun _ => 0⟩
  let cons ← e.cons.get
  let roots := (← e.roots.get).filter fun i => cons[i]!.alive
  e.roots.set roots
  let mut confl := none
  for i in roots do
    if confl.isNone then
      let r := (← e.cons.get)[i]!
      -- The constraint's slack is up to date; it propagates at most its own terms.
      let s : ℤ ← if r.clause then pure r.slack0 else pure (← e.slack.get)[i]!
      if s < 0 then confl := some i
      else
        if !r.clause then e.propagatePB i s
        confl ← e.propagate
  e.markRootReasons 0
  e.rootLen.set (← e.trail.get).size
  e.rootConflict.set confl
  e.dirty.set false

/-- Push onto a binary max-heap. -/
private def heapPush (h : Array ℕ) (x : ℕ) : Array ℕ := Id.run do
  let mut h := h.push x
  let mut i := h.size - 1
  while 0 < i && h[(i - 1) / 2]! < h[i]! do
    h := h.swapIfInBounds i ((i - 1) / 2)
    i := (i - 1) / 2
  return h

/-- Pop the maximum of a nonempty binary max-heap. -/
private def heapPop (h : Array ℕ) : ℕ × Array ℕ := Id.run do
  let top := h[0]!
  let mut h := (h.swapIfInBounds 0 (h.size - 1)).pop
  let mut i := 0
  let mut go := true
  while go do
    let l := 2 * i + 1
    let r := 2 * i + 2
    let mut m := i
    if l < h.size && h[m]! < h[l]! then m := l
    if r < h.size && h[m]! < h[r]! then m := r
    if m == i then go := false
    else
      h := h.swapIfInBounds i m
      i := m
  return (top, h)

/-- The kernel hints of a conflict at the constraint `k`: the reasons of the needed literals, in
trail order, a reason repeated on consecutive needed literals given once, then `k`. -/
private def analyze (e : Engine σ) (k : ℕ) : ST σ (Array Hint) := do
  let cons ← e.cons.get
  let trail ← e.trail.get
  let tpos ← e.tpos.get
  let reason ← e.reason.get
  let value ← e.value.get
  -- `marked` holds the trail positions of the needed literals, `heap` those not yet processed.
  let mark (r : CRec) (lim : ℕ) (st : Std.HashMap ℕ Unit × Array ℕ) :
      Std.HashMap ℕ Unit × Array ℕ := Id.run do
    let mut (marked, heap) := st
    for l in r.lits do
      if litVal value l == 2 then
        let p := tpos[l / 2]!
        if p < lim && !marked.contains p then
          marked := marked.insert p ()
          heap := heapPush heap p
    return (marked, heap)
  let mut st := mark cons[k]! trail.size ({}, #[])
  let mut out : Array ℕ := #[]
  while !st.2.isEmpty do
    let (p, heap) := heapPop st.2
    st := (st.1, heap)
    let r := reason[trail[p]! / 2]!
    if out.back? != some r then out := out.push r
    st := mark cons[r]! p st
  return (out.reverse.map (cons[·]!.hint)).push cons[k]!.hint

/-- **The hints of `rup C`**, given the negation `neg` of `C`: propagate the database and `neg`,
and on a conflict return its hints, found by conflict analysis, `neg` being named `~`. Returns
`none` when propagation reaches no conflict. -/
def rupHints (e : Engine σ) (neg : PBConstr) : ST σ (Option (Array Hint)) := do
  if ← e.dirty.get then e.rebuild
  if let some k ← e.rootConflict.get then return some (← e.analyze k)
  let rl ← e.rootLen.get
  -- The negation, as a non-clause constraint of its own.
  let mut ts : Array (ℕ × ℕ) := #[]
  for t in neg.terms do
    if t.1 > 0 then ts := ts.push (t.1, ← e.litCode t.2)
  let sorted := ts.qsort (fun a b => a.1 > b.1)
  let i := (← e.cons.get).size
  let coeffs := sorted.map (·.1)
  let lits := sorted.map (·.2)
  e.cons.modify (·.push ⟨lits, coeffs, neg.degree, 0, false, true, .neg⟩)
  e.slack.modify (·.push 0)
  e.rootReason.modify (·.push 0)
  for k in [0:lits.size] do
    e.occ.modify fun o => o.modify lits[k]! (·.push (i, coeffs[k]!))
  let confl ← match ← e.checkFresh i with
    | some k => pure (some k)
    | none => e.propagate
  let res ← match confl with
    | some k => pure (some (← e.analyze k))
    | none => pure none
  e.backtrack rl
  e.cons.modify (·.modify i ({ · with alive := false, lits := #[], coeffs := #[] }))
  return res

/-- **Extend a partial assignment by propagation**, as VeriPB does for a logged solution
(§5.8.1): make the literals `ls` true, propagate the database, and return every assigned
literal; `none` on a conflict. -/
def extend (e : Engine σ) (ls : List (Literal ℕ)) : ST σ (Option (Array (Literal ℕ))) := do
  if ← e.dirty.get then e.rebuild
  if (← e.rootConflict.get).isSome then return none
  let rl ← e.rootLen.get
  let mut ok := true
  for l in ls do
    let code ← e.litCode l
    let v := litVal (← e.value.get) code
    if v == 0 then e.assign code 0
    else if v == 2 then ok := false
  if ok then ok := (← e.propagate).isNone
  let res ← if ok then do
      let vars ← e.vars.get
      pure (some ((← e.trail.get).map fun c => (vars[c / 2]!, c % 2 == 0)))
    else pure none
  e.backtrack rl
  return res

end Engine

end Cslib.Logic.PL.VeriPB.Elab

end
