/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
public import CslibFrontier.Tactic.WramOmega.Init
public meta import CslibFrontier.Tactic.WramOmega.Prove
public meta import Lean.Elab.Tactic.Omega

/-!
# Closing word-size bounds

`Cslib.WordRAM.Fits w v` states `v < 2 ^ w`, and word-RAM proofs need many such side conditions,
one per value an instruction writes. `fits` proves them by linear arithmetic: it unfolds `Fits` in
the goal and in every hypothesis that mentions it, then runs `omega`. The hypotheses are found by
their statements, not by their names, so a bound follows from whichever word-size facts are in
context, without first choosing the fact to weaken with `Fits.of_le`. `Cslib.GenericRAM.Signed.Fits`
is unfolded in the same way when in scope.

Only hypotheses whose statements contain `Fits` are unfolded: they are added to the context in
unfolded form, and the others are left to `omega` as they are. Each power of two `2 ^ e` among
them is added as positive, which `omega` does not know by itself. `fits [h₁, h₂]` also adds the
statements of the given terms, such as a product bound that `omega` cannot derive.

When the direct linear attempt cannot close the bound, `fits` injects bounded dominance facts for
subexpressions actually appearing in the goal and arithmetic context, then runs `omega` again:

* `a / b ≤ a` (`Nat.div_le_self`), `a % b ≤ a` (`Nat.mod_le`), `a % b < b` (`Nat.mod_lt`) when
  `0 < b` is established or `b = 2 ^ k`;
* `a &&& b ≤ a` and `a &&& b ≤ b` (`Nat.and_le_left` / `Nat.and_le_right`);
* `a >>> k ≤ a` (`Nat.shiftRight_le`);
* `a ^^^ b < 2 ^ k` and `a ||| b < 2 ^ k` (`Nat.xor_lt_two_pow` / `Nat.or_lt_two_pow`) in bottom-up
  order from already-known upper bounds on the operands;
* `a <<< s < 2 ^ w` from `a < 2 ^ i` with `i + s ≤ w`, and `a * b < 2 ^ w` from `a < 2 ^ i`,
  `b < 2 ^ j` with `i + j ≤ w` for subterms occurring in the target;
* `k < 2 ^ k` (`Nat.lt_two_pow_self`);
* power-of-two monotonicity `(2 ^ d) * 2 ^ i ≤ 2 ^ j` when `d + i ≤ j` (`d ∈ {0, 1, 2, 3}`),
  bridging `(2 : ℤ) ^ k` to `((2 ^ k : ℕ) : ℤ)` via `Int.natCast_pow`;
* `i.val < n` (`Fin.isLt`) for `Fin.val` reads;
* `x.regs i < 2 ^ w` and `x.mem a < 2 ^ w` for concrete reads of data with a `Data.Bounded w x`
  hypothesis in context.

The fast linear path runs first, so simple linear word-size bounds incur no extra preprocessing.

The tactic fails on a goal that is not a word-size bound, naming the plain `omega` that is then the
right call, and when `omega` cannot close the unfolded goal, showing that goal and saying whether
any hypothesis `Fits w v` was found.

`fits` unfolds `Fits` and nothing else. A word-size bound that follows only once definitions of
addresses and sizes are unfolded, such as `Fits w (keysBase base n + i)` from
`Fits w (base + space n)`, is for `wram_omega` of `CslibFrontier.Tactic.WramOmega`, which unfolds
the definitions tagged `@[wram_arith]`, `Fits` among them; so is a goal of another shape that
follows from hypotheses `Fits w v`.

The simplification procedure `Cslib.WordRAM.reduceFits` rewrites `Fits w v` to `True` when `omega`
proves it from the hypotheses that mention `Fits` and target-only dominance facts (`div`, `mod`,
`and`, `shiftRight`), so that `ram_eval` and `ram_exact_eval` decide whether written values fit a
word without named `Fits` lemmas while keeping cost independent of context length.

## Main definitions

* `fits`: prove `Fits w v`, `v < 2 ^ w`, or `GenericRAM.Signed.Fits w z`, by `omega` with
  bounded dominance preprocessing.
* `Cslib.WordRAM.reduceFits`: target-local `Fits` simplification procedure for `ram_eval`.
-/

public meta section

namespace Cslib.Tactic.Fits

open Lean Meta Elab Tactic
open Cslib.Tactic.WramOmega (isPowerOfTwo proveOmega?)

/-- Name of `Cslib.GenericRAM.Signed.Fits`, checked without importing `GenericRAM.Signed`. -/
private def signedFitsName : Name := `Cslib.GenericRAM.Signed.Fits

/-- Whether `e` is a power of two `(2 : ℤ) ^ k` on integers. -/
private def isIntPowerOfTwo (e : Expr) : Bool :=
  match_expr e with
  | HPow.hPow α β _ _ b _ =>
    α.isConstOf ``Int && β.isConstOf ``Nat &&
      match_expr b with
      | OfNat.ofNat _ n _ => n.rawNatLit? == some 2 || n.nat? == some 2
      | Int.ofNat n => n.rawNatLit? == some 2 || n.nat? == some 2
      | _ => false
  | _ => false

/-- Exponent `k` of `(2 : ℤ) ^ k`, if `e` is one. -/
private def intPowerExp? (e : Expr) : Option Expr :=
  if isIntPowerOfTwo e then
    let_expr HPow.hPow _ _ _ _ _ k := e | none
    some k
  else none

/-- Unfold `Cslib.WordRAM.Fits` (and `Cslib.GenericRAM.Signed.Fits` when visible) everywhere in
`e`. -/
private def unfoldFits (e : Expr) : CoreM Expr := do
  let env ← getEnv
  let hasSigned := match env.find? signedFitsName with
    | some info => info.hasValue
    | none => false
  deltaExpand e fun n => n == ``Cslib.WordRAM.Fits || (hasSigned && n == signedFitsName)

/-- Whether `e` mentions `Cslib.WordRAM.Fits`. -/
private def mentionsWordFits (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Cslib.WordRAM.Fits)).isSome

/-- Whether `e` mentions `Cslib.WordRAM.Fits` or `Cslib.GenericRAM.Signed.Fits`. -/
private def mentionsFits (e : Expr) : Bool :=
  (e.find? fun t => t.isConstOf ``Cslib.WordRAM.Fits || t.isConstOf signedFitsName).isSome

/-- Whether `e` is a word-size bound: it mentions `Fits`, or is `v < 2 ^ k` (on `ℕ` or `ℤ`), or
`-(2 ^ k : ℤ) ≤ v`. -/
private def isWordBound (e : Expr) : Bool :=
  mentionsFits e || match_expr e with
    | LT.lt _ _ _ b => isPowerOfTwo b || isIntPowerOfTwo b
    | LE.le _ _ a _ =>
      match_expr a with
      | Neg.neg _ _ p => isIntPowerOfTwo p
      | _ => false
    | _ => false

/-- The hypotheses whose statements mention `Fits`, with `Fits` unfolded in their statements. -/
private def fitsHypotheses (includeSigned : Bool := true) : MetaM (Array Hypothesis) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let type ← instantiateMVars d.type
    let ok := if includeSigned then mentionsFits type else mentionsWordFits type
    unless ok do return acc
    unless ← isProp type do return acc
    return acc.push { userName := d.userName, type := ← unfoldFits type, value := d.toExpr }

/-- Extract a natural-number binary application matching either an `H*` form or `Nat.*`. -/
private def natDivArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HDiv.hDiv α β _ _ a b => if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.div a b => some (a, b)
  | _ => none

private def natModArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HMod.hMod α β _ _ a b => if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.mod a b => some (a, b)
  | _ => none

private def natAndArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HAnd.hAnd α β _ _ a b => if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.land a b => some (a, b)
  | _ => none

private def natOrArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HOr.hOr α β _ _ a b => if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.lor a b => some (a, b)
  | _ => none

private def natXorArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HXor.hXor α β _ _ a b => if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.xor a b => some (a, b)
  | _ => none

private def natShiftRightArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HShiftRight.hShiftRight α β _ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.shiftRight a b => some (a, b)
  | _ => none

private def natShiftLeftArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HShiftLeft.hShiftLeft α β _ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.shiftLeft a b => some (a, b)
  | _ => none

private def natMulArgs? (t : Expr) : Option (Expr × Expr) :=
  match_expr t with
  | HMul.hMul α β _ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat then some (a, b) else none
  | Nat.mul a b => some (a, b)
  | _ => none

/-- Extract the closed `Nat` literal of `e` (`NatLit` or `OfNat.ofNat Nat n _`). -/
private def natLit? (e : Expr) : Option ℕ :=
  match e.nat? with
  | some n => some n
  | none =>
    match e.rawNatLit? with
    | some n => some n
    | none =>
      match_expr e with
      | OfNat.ofNat α n _ => if α.isConstOf ``Nat then n.rawNatLit? else none
      | _ => none

private def natAdd2 (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]
private def natPow2 (k : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[mkNatLit 2, k]
private def natLt (a b : Expr) : MetaM Expr := mkAppM ``LT.lt #[a, b]

/-- Bridge `((2 ^ k : ℕ) : ℤ) = t` for an integer power-of-two term `t = (2 : ℤ) ^ k`. -/
private def mkIntPowBridge? (t k : Expr) : MetaM (Option Hypothesis) := do
  try
    let natPow ← natPow2 k
    let lhs ← mkAppOptM ``Nat.cast #[some (mkConst ``Int), none, some natPow]
    let type ← mkAppM ``Eq #[lhs, t]
    let raw := mkApp2 (mkConst ``Int.natCast_pow) (mkNatLit 2) k
    unless ← isDefEq type (← inferType raw) do return none
    let value ← mkExpectedTypeHint raw type
    return some { userName := `this, type, value }
  catch _ => return none

/-- Build a proof of `(2 ^ d) * 2 ^ k₁ ≤ 2 ^ k₂` (or `2 ^ k₁ ≤ 2 ^ k₂` when `d = 0`) from
`hle : d + k₁ ≤ k₂` (respectively `k₁ ≤ k₂`). -/
private def mkTwoPowGapLe (d : ℕ) (k₁ k₂ hle : Expr) : MetaM Expr := do
  if d == 0 then
    mkAppOptM ``Nat.pow_le_pow_right
      #[some (mkNatLit 2), some (mkConst ``Nat.two_pos), some k₁, some k₂, some hle]
  else
    let dk₁ ← natAdd2 (mkNatLit d) k₁
    let hpow ← mkAppOptM ``Nat.pow_le_pow_right
      #[some (mkNatLit 2), some (mkConst ``Nat.two_pos), some dk₁, some k₂, some hle]
    let heq ← mkAppM ``Eq.symm #[mkApp3 (mkConst ``Nat.pow_add) (mkNatLit 2) (mkNatLit d) k₁]
    let lhs ← mkAppM ``HMul.hMul #[mkNatLit (Nat.pow 2 d), ← natPow2 k₁]
    let ty ← mkAppM ``LE.le #[lhs, ← natPow2 k₂]
    let prf ← mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_of_eq #[heq], hpow]
    mkExpectedTypeHint prf ty

/-- Build a proof of `a <<< s < 2 ^ w` from `ha : a < 2 ^ i` and `hle : i + s ≤ w`. -/
private def mkShiftLeftLtTwoPow (a s i w ha hle : Expr) : MetaM Expr := do
  let h1 := mkApp2 (mkConst ``Nat.shiftLeft_eq) a s
  let h2 ← mkAppM ``Nat.mul_lt_mul_of_pos_right #[ha, mkApp (mkConst ``Nat.two_pow_pos) s]
  let h3 ← mkAppM ``Nat.lt_of_le_of_lt #[← mkAppM ``Nat.le_of_eq #[h1], h2]
  let h4 ← mkAppM ``Eq.symm #[mkApp3 (mkConst ``Nat.pow_add) (mkNatLit 2) i s]
  let h5 ← mkAppM ``Nat.lt_of_lt_of_le #[h3, ← mkAppM ``Nat.le_of_eq #[h4]]
  let isSum ← natAdd2 i s
  let h6 ← mkAppOptM ``Nat.pow_le_pow_right
    #[some (mkNatLit 2), some (mkConst ``Nat.two_pos), some isSum, some w, some hle]
  mkAppM ``Nat.lt_of_lt_of_le #[h5, h6]

/-- Build a proof of `a * b < 2 ^ w` from `ha : a < 2 ^ i`, `hb : b < 2 ^ j`, `hle : i + j ≤ w`. -/
private def mkMulLtTwoPow (i j w ha hb hle : Expr) : MetaM Expr := do
  let h1 ← mkAppM ``Nat.mul_lt_mul_of_lt_of_lt #[ha, hb]
  let h2 ← mkAppM ``Eq.symm #[mkApp3 (mkConst ``Nat.pow_add) (mkNatLit 2) i j]
  let h3 ← mkAppM ``Nat.lt_of_lt_of_le #[h1, ← mkAppM ``Nat.le_of_eq #[h2]]
  let ijSum ← natAdd2 i j
  let h4 ← mkAppOptM ``Nat.pow_le_pow_right
    #[some (mkNatLit 2), some (mkConst ``Nat.two_pos), some ijSum, some w, some hle]
  mkAppM ``Nat.lt_of_lt_of_le #[h3, h4]

/-- The facts `0 < 2 ^ e` for the powers of two in `es`, plus `((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k`
bridges for integer powers of two. `omega` reads `2 ^ e` as an atom without knowing that it is
positive, which a bound such as `Fits w (2 ^ e - 1)` needs. -/
private def powerFacts (es : Array Expr) : MetaM (Array Hypothesis) := do
  let powers ← IO.mkRef (#[] : Array Expr)
  let intPowers ← IO.mkRef (#[] : Array (Expr × Expr))
  for e in es do
    forEachExpr e fun t => do
      if t.hasLooseBVars then return
      if isPowerOfTwo t && !(← powers.get).contains t then powers.modify (·.push t)
      if let some k := intPowerExp? t then
        if !(← intPowers.get).any (·.1 == t) then intPowers.modify (·.push (t, k))
  let mut facts : Array Hypothesis := #[]
  for (t, k) in ← intPowers.get do
    let np ← natPow2 k
    if !(← powers.get).contains np then powers.modify (·.push np)
    if let some h ← mkIntPowBridge? t k then facts := facts.push h
  for t in ← powers.get do
    let_expr HPow.hPow _ _ _ _ _ k := t | continue
    let type ← mkAppM ``LT.lt #[mkNatLit 0, t]
    let value := mkApp (mkConst ``Nat.two_pow_pos) k
    if ← isDefEq type (← inferType value) then
      facts := facts.push { userName := `this, type, value }
  return facts

/-- Collector state for Stage 2 dominance facts, avoiding duplicate assertions. -/
private structure FactPool where
  facts : Array Hypothesis := #[]
  seen : Std.HashSet Expr := {}

private def pushFact (pool : IO.Ref FactPool) (value : Expr) (type? : Option Expr := none) :
    MetaM Unit := do
  let type ← match type? with
    | some ty => pure ty
    | none => inferType value
  if type.hasLooseBVars || type.hasExprMVar then return
  if (← pool.get).seen.contains type then return
  pool.modify fun s =>
    { facts := s.facts.push { userName := `this, type, value }, seen := s.seen.insert type }

/-- Node count bounded by `limit` to skip huge algebraic equalities in side-queries. -/
private def exprSmall (e : Expr) (limit : ℕ := 96) : Bool :=
  go e limit |>.isSome
where
  go : Expr → ℕ → Option ℕ
  | _, 0 => none
  | .app f a, n + 1 => match go f n with | some r => go a r | none => none
  | .lam _ _ b _, n + 1 => go b n
  | .forallE _ t b _, n + 1 => match go t n with | some r => go b r | none => none
  | .letE _ _ v b _, n + 1 => match go v n with | some r => go b r | none => none
  | .mdata _ b, n + 1 => go b n
  | .proj _ _ s, n + 1 => go s n
  | _, n + 1 => some n

/-- Whether `type` is an arithmetic proposition worth scanning for subexpressions. -/
private partial def isSimpleArithProp (type : Expr) : Bool :=
  match_expr type with
  | Eq α _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | Ne α _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | LE.le α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | LT.lt α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | GE.ge α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | GT.gt α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | Dvd.dvd α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | Not p => isSimpleArithProp p
  | And p q => isSimpleArithProp p || isSimpleArithProp q
  | Or p q => isSimpleArithProp p || isSimpleArithProp q
  | _ => mentionsFits type

/-- Whether `e` contains a `2 ^ _` term (used to keep exponent-only queries separate from word-size
hypotheses when proving `k₁ ≤ k₂`). -/
private def hasPowTwo (e : Expr) : Bool :=
  (e.find? fun t => isPowerOfTwo t || isIntPowerOfTwo t).isSome

/-- Per-query heartbeat budget (in thousands) for internal side-queries to `Omega.omega`. -/
private def microMaxHeartbeats : ℕ := 2000

/-- Total heartbeat budget (in thousands) that Stage 2 side-queries may spend on one `fits` call. -/
private def stage2QueryBudget : ℕ := 30000

private def underBudget (startHb : ℕ) : CoreM Bool := do
  return (← IO.getNumHeartbeats) - startHb ≤ stage2QueryBudget * 1000

/-- Try to prove `prop` using `Omega.omega` with a tiny heartbeat budget over `proofs`. -/
private def tryOmegaQuick (startHb : ℕ) (proofs : List Expr) (prop : Expr) :
    MetaM (Option Expr) := do
  if prop.hasLooseBVars || prop.hasExprMVar then return none
  unless ← underBudget startHb do return none
  proveOmega? microMaxHeartbeats proofs prop

/-- Fast syntactic lookup in context or `extra` for a proof whose type is `prop`. -/
private def findExactProof? (extra : Array Hypothesis) (prop : Expr) : MetaM (Option Expr) := do
  let p := prop.cleanupAnnotations
  for h in extra do
    if h.type.cleanupAnnotations == p then
      return some (← mkExpectedTypeHint h.value h.type)
  (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    let eq := (← instantiateMVars d.type).cleanupAnnotations == p
    return if eq then some d.toExpr else none

/-- Prove a `Nat` order relation `a ≤ b` by literal `decide` if closed, else `tryOmegaQuick`. -/
private def proveNatLe? (startHb : ℕ) (proofs : List Expr) (a b : Expr) :
    MetaM (Option Expr) := do
  if a == b then
    return some (mkApp (mkConst ``Nat.le_refl) a)
  if let (some na, some nb) := (natLit? a, natLit? b) then
    if na ≤ nb then
      return some (← mkDecideProof (← mkAppM ``LE.le #[a, b]))
    else
      return none
  tryOmegaQuick startHb proofs (← mkAppM ``LE.le #[a, b])

private def maxPowExps : ℕ := 10
private def maxDominanceFacts : ℕ := 96

/-- Extract the target's outer `2 ^ w` exponent, if the goal has the form `v < 2 ^ w` or
`-(2 ^ w : ℤ) ≤ v` / `v < (2 : ℤ) ^ w`. -/
private partial def targetPowExp? (target : Expr) : Option (Bool × Expr) :=
  match_expr target with
  | LT.lt _ _ _ rhs =>
    if isPowerOfTwo rhs then
      let_expr HPow.hPow _ _ _ _ _ w := rhs | none
      some (false, w)
    else if let some w := intPowerExp? rhs then
      some (true, w)
    else none
  | And p _ => targetPowExp? p
  | _ => none

/-- Simple local `Data.Bounded w' x` hypotheses as `(proof, width, dataExpr)`. -/
private def collectBoundedHyps : MetaM (Array (Expr × Expr × Expr)) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let ty := (← instantiateMVars d.type).cleanupAnnotations
    let_expr Cslib.WordRAM.Data.Bounded _ w x := ty | return acc
    return acc.push (d.toExpr, w, x)

/-- Build `fits`'s Stage 2 dominance facts from `roots` (unfolded goal, unfolded `Fits` hyps, user
terms, and small local arithmetic hyps), with `^^^`/`|||`/`<<<`/`*` closure scoped to `target` and
a strict total heartbeat budget. -/
private def dominanceFacts (baseHyps : Array Hypothesis) (target : Expr) :
    MetaM (Array Hypothesis) := do
  let startHb ← IO.getNumHeartbeats
  let pool ← IO.mkRef ({} : FactPool)
  let baseProofs ← baseHyps.mapM fun h => mkExpectedTypeHint h.value h.type
  let mut roots : Array Expr := #[target]
  let mut linProofs : Array Expr := baseProofs
  let mut expProofs : Array Expr := #[]
  for h in baseHyps do
    roots := roots.push h.type
    if !hasPowTwo h.type && exprSmall h.type 128 then
      expProofs := expProofs.push (← mkExpectedTypeHint h.value h.type)
    else if h.type.isAppOfArity ``And 2 then
      let p := h.type.getArg! 0
      if !hasPowTwo p && exprSmall p 128 then
        try
          let hprf ← mkExpectedTypeHint h.value h.type
          expProofs := expProofs.push (← mkAppM ``And.left #[hprf])
        catch _ => pure ()
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some v := d.value? then
      let v ← instantiateMVars v
      if (target.find? (· == d.toExpr)).isSome && exprSmall v 128 then
        roots := roots.push v
    if ← isProp ty then
      if isSimpleArithProp ty && exprSmall ty 128 then
        roots := roots.push ty
        linProofs := linProofs.push d.toExpr
        if !hasPowTwo ty then
          expProofs := expProofs.push d.toExpr
  let bounded ← collectBoundedHyps
  let natExps ← IO.mkRef (#[] : Array Expr)
  let modDivisors ← IO.mkRef (#[] : Array (Expr × Expr))
  let pushExp (k : Expr) : MetaM Unit := do
    if k.hasLooseBVars || k.hasExprMVar then return
    let cur ← natExps.get
    if cur.size < maxPowExps && !cur.contains k then
      natExps.modify (·.push k)
  let rec visit (t : Expr) (visited : IO.Ref (Std.HashSet Expr)) : MetaM Unit := do
    if t.hasLooseBVars then return
    if (← visited.get).contains t then return
    visited.modify (·.insert t)
    match t with
    | .app fn arg => visit fn visited; visit arg visited
    | .mdata _ b => visit b visited
    | .proj _ _ s => visit s visited
    | .letE _ _ v b _ => visit v visited; visit b visited
    | _ => pure ()
    if (← pool.get).facts.size ≥ maxDominanceFacts then return
    if isPowerOfTwo t then
      let_expr HPow.hPow _ _ _ _ _ k := t | pure ()
      pushExp k
    if let some k := intPowerExp? t then
      pushExp k
      if let some h ← mkIntPowBridge? t k then
        pushFact pool h.value (some h.type)
    if let some (a, b) := natDivArgs? t then
      try pushFact pool (← mkAppM ``Nat.div_le_self #[a, b]) catch _ => pure ()
    if let some (a, b) := natModArgs? t then
      try pushFact pool (← mkAppM ``Nat.mod_le #[a, b]) catch _ => pure ()
      if isPowerOfTwo b then
        try
          let_expr HPow.hPow _ _ _ _ _ k := b | pure ()
          pushFact pool (← mkAppM ``Nat.mod_lt #[a, mkApp (mkConst ``Nat.two_pow_pos) k])
        catch _ => pure ()
      else
        modDivisors.modify (·.push (a, b))
    if let some (a, b) := natAndArgs? t then
      try
        pushFact pool (← mkAppOptM ``Nat.and_le_left #[some a, some b])
        pushFact pool (← mkAppOptM ``Nat.and_le_right #[some a, some b])
      catch _ => pure ()
    if let some (a, k) := natShiftRightArgs? t then
      try pushFact pool (← mkAppM ``Nat.shiftRight_le #[a, k]) catch _ => pure ()
    if t.isAppOfArity ``Fin.val 2 then
      let n := t.getArg! 0
      let i := t.getArg! 1
      try
        pushFact pool (mkApp2 (mkConst ``Fin.isLt) n i)
        if isPowerOfTwo n then
          let_expr HPow.hPow _ _ _ _ _ k := n | pure ()
          pushExp k
      catch _ => pure ()
    else if let .proj ``Fin 0 i := t then
      try
        let ity ← whnfR (← inferType i)
        match_expr ity with
        | Fin n =>
          pushFact pool (mkApp2 (mkConst ``Fin.isLt) n i)
          if isPowerOfTwo n then
            let_expr HPow.hPow _ _ _ _ _ k := n | pure ()
            pushExp k
        | _ => pure ()
      catch _ => pure ()
    unless bounded.isEmpty do
      match_expr t with
      | Cslib.WordRAM.Data.regs _ x i =>
        for (hb, w, xb) in bounded do
          if x == xb then
            try
              let prf := mkApp (← mkAppM ``And.left #[hb]) i
              let ty ← unfoldFits (← inferType prf)
              pushFact pool (← mkExpectedTypeHint prf ty) (some ty)
              pushExp w
            catch _ => pure ()
      | Cslib.WordRAM.Data.mem _ x a =>
        for (hb, w, xb) in bounded do
          if x == xb then
            try
              let prf := mkApp (← mkAppM ``And.right #[hb]) a
              let ty ← unfoldFits (← inferType prf)
              pushFact pool (← mkExpectedTypeHint prf ty) (some ty)
              pushExp w
            catch _ => pure ()
      | _ => pure ()
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  for r in roots do
    visit r visited
  let exps ← natExps.get
  for k in exps do
    try
      pushFact pool (mkApp (mkConst ``Nat.two_pow_pos) k)
      pushFact pool (← mkAppOptM ``Nat.lt_two_pow_self #[some k])
    catch _ => pure ()
  let expList := expProofs.toList
  let poolToList : MetaM (List Expr) := do
    let cur := (← pool.get).facts
    let ps ← cur.mapM fun h => mkExpectedTypeHint h.value h.type
    return (linProofs ++ ps).toList
  -- Check `0 < b` for non-power-of-two `a % b` terms.
  for (a, b) in ← modDivisors.get do
    if (← pool.get).facts.size ≥ maxDominanceFacts then break
    let posProp ← natLt (mkNatLit 0) b
    if let some c := natLit? b then
      if c > 0 then
        try pushFact pool (← mkAppM ``Nat.mod_lt #[a, ← mkDecideProof posProp]) catch _ => pure ()
    else
      let hpos? ← match ← findExactProof? (← pool.get).facts posProp with
        | some p => pure (some p)
        | none => tryOmegaQuick startHb expList posProp
      if let some hpos := hpos? then
        try pushFact pool (← mkAppM ``Nat.mod_lt #[a, hpos]) catch _ => pure ()
  -- Check literal lower-bound exponent for concrete `Fits w c` / `c < 2 ^ w` goals.
  match_expr target with
  | LT.lt α _ lhs rhs =>
    if α.isConstOf ``Nat && isPowerOfTwo rhs then
      let_expr HPow.hPow _ _ _ _ _ w := rhs | pure ()
      if let some c := natLit? lhs then
        if c > 0 then
          let m := c.log2 + 1
          if m ≤ 64 then
            let mExpr := mkNatLit m
            if let some hle ← proveNatLe? startHb expList mExpr w then
              try pushFact pool (← mkTwoPowGapLe 0 mExpr w hle) catch _ => pure ()
  | _ => pure ()
  -- Monotonicity across pairs of `2 ^ k` (including integer powers bridged via `Int.natCast_pow`):
  -- test `k₁ ≤ k₂` first, then refine constant gap `d ∈ {0, 1, 2, 3}` with at most two checks.
  for i in [:exps.size] do
    for j in [:exps.size] do
      if i == j then continue
      if (← pool.get).facts.size ≥ maxDominanceFacts then break
      unless ← underBudget startHb do break
      let k₁ := exps[i]!
      let k₂ := exps[j]!
      if let some hle0 ← proveNatLe? startHb expList k₁ k₂ then
        let (d, hle) ← do
          if let some hle2 ← proveNatLe? startHb expList (← natAdd2 (mkNatLit 2) k₁) k₂ then
            if let some hle3 ← proveNatLe? startHb expList (← natAdd2 (mkNatLit 3) k₁) k₂ then
              pure (3, hle3)
            else
              pure (2, hle2)
          else if let some hle1 ← proveNatLe? startHb expList (← natAdd2 (mkNatLit 1) k₁) k₂ then
            pure (1, hle1)
          else
            pure (0, hle0)
        try pushFact pool (← mkTwoPowGapLe d k₁ k₂ hle) catch _ => pure ()
  -- Collect post-order `^^^`/`|||`, `<<<`, and `*` terms inside `target`.
  let targetXorOr ← IO.mkRef (#[] : Array (Bool × Expr × Expr))
  let seenBW ← IO.mkRef ({} : Std.HashSet Expr)
  let shiftLeftTerms ← IO.mkRef (#[] : Array (Expr × Expr))
  let mulTerms ← IO.mkRef (#[] : Array (Expr × Expr))
  let rec visitTarget (t : Expr) (seen : IO.Ref (Std.HashSet Expr)) : MetaM Unit := do
    if t.hasLooseBVars then return
    if (← seen.get).contains t then return
    seen.modify (·.insert t)
    match t with
    | .app fn arg => visitTarget fn seen; visitTarget arg seen
    | .mdata _ b => visitTarget b seen
    | .proj _ _ s => visitTarget s seen
    | .letE _ _ v b _ => visitTarget v seen; visitTarget b seen
    | _ => pure ()
    if let some (a, b) := natXorArgs? t then
      if !(← seenBW.get).contains t && (← targetXorOr.get).size < 16 then
        seenBW.modify (·.insert t)
        targetXorOr.modify (·.push (true, a, b))
    if let some (a, b) := natOrArgs? t then
      if !(← seenBW.get).contains t && (← targetXorOr.get).size < 16 then
        seenBW.modify (·.insert t)
        targetXorOr.modify (·.push (false, a, b))
    if let some (a, s) := natShiftLeftArgs? t then
      if (← shiftLeftTerms.get).size < 6 then shiftLeftTerms.modify (·.push (a, s))
    if let some (a, b) := natMulArgs? t then
      if (natLit? a).isNone && (natLit? b).isNone && (← mulTerms.get).size < 6 then
        mulTerms.modify (·.push (a, b))
  let targetSeen ← IO.mkRef ({} : Std.HashSet Expr)
  visitTarget target targetSeen
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some v := d.value? then
      let v ← instantiateMVars v
      if (target.find? (· == d.toExpr)).isSome && exprSmall v 64 then
        visitTarget v targetSeen
  let targetWs := match targetPowExp? target with
    | some (false, w) => #[w]
    | _ => exps
  unless (← shiftLeftTerms.get).isEmpty || exps.isEmpty do
    for (a, s) in ← shiftLeftTerms.get do
      if (← pool.get).facts.size ≥ maxDominanceFacts then break
      unless ← underBudget startHb do break
      let curFacts := (← pool.get).facts
      let curProofs ← poolToList
      for w in targetWs do
        let mut found := false
        for i in exps do
          if found then break
          let some hle ← proveNatLe? startHb expList (← natAdd2 i s) w | continue
          let pa ← natLt a (← natPow2 i)
          let ha? ← match ← findExactProof? curFacts pa with
            | some h => pure (some h)
            | none => tryOmegaQuick startHb curProofs pa
          let some ha := ha? | continue
          try
            pushFact pool (← mkShiftLeftLtTwoPow a s i w ha hle)
            found := true
          catch _ => pure ()
  unless (← mulTerms.get).isEmpty || exps.isEmpty do
    for (a, b) in ← mulTerms.get do
      if (← pool.get).facts.size ≥ maxDominanceFacts then break
      unless ← underBudget startHb do break
      let curFacts := (← pool.get).facts
      let curProofs ← poolToList
      let mut goodA : Array (Expr × Expr) := #[]
      let mut goodB : Array (Expr × Expr) := #[]
      for i in exps do
        let pow ← natPow2 i
        let pa ← natLt a pow
        if let some ha ← (match ← findExactProof? curFacts pa with
            | some h => pure (some h)
            | none => tryOmegaQuick startHb curProofs pa) then
          goodA := goodA.push (i, ha)
        let pb ← natLt b pow
        if let some hb ← (match ← findExactProof? curFacts pb with
            | some h => pure (some h)
            | none => tryOmegaQuick startHb curProofs pb) then
          goodB := goodB.push (i, hb)
      for w in targetWs do
        let mut found := false
        for (i, ha) in goodA do
          if found then break
          for (j, hb) in goodB do
            if found then break
            let some hle ← proveNatLe? startHb expList (← natAdd2 i j) w | continue
            try
              pushFact pool (← mkMulLtTwoPow i j w ha hb hle)
              found := true
            catch _ => pure ()
  let bwTerms ← targetXorOr.get
  unless bwTerms.isEmpty || exps.isEmpty do
    for (isXor, a, b) in bwTerms do
      if (← pool.get).facts.size ≥ maxDominanceFacts then break
      unless ← underBudget startHb do break
      let curFacts := (← pool.get).facts
      let curProofs ← poolToList
      let mut done := false
      for k in exps do
        if done then break
        let pow ← natPow2 k
        let some ha ← findExactProof? curFacts (← natLt a pow) | continue
        let some hb ← findExactProof? curFacts (← natLt b pow) | continue
        try
          let lem := if isXor then ``Nat.xor_lt_two_pow else ``Nat.or_lt_two_pow
          pushFact pool (← mkAppOptM lem #[some a, some b, some k, some ha, some hb])
          done := true
        catch _ => pure ()
      unless done do
        for k in exps do
          if done then break
          unless ← underBudget startHb do break
          let pow ← natPow2 k
          let pa ← natLt a pow
          let ha? ← match ← findExactProof? curFacts pa with
            | some h => pure (some h)
            | none => tryOmegaQuick startHb curProofs pa
          let some ha := ha? | continue
          let pb ← natLt b pow
          let hb? ← match ← findExactProof? curFacts pb with
            | some h => pure (some h)
            | none => tryOmegaQuick startHb curProofs pb
          let some hb := hb? | continue
          try
            let lem := if isXor then ``Nat.xor_lt_two_pow else ``Nat.or_lt_two_pow
            pushFact pool (← mkAppOptM lem #[some a, some b, some k, some ha, some hb])
            done := true
          catch _ => pure ()
  return (← pool.get).facts

/-- Lightweight dominance facts extracted solely from `target` for the `reduceFits` simproc. -/
private def quickTargetFacts (target : Expr) : MetaM (Array Expr) := do
  let acc ← IO.mkRef (#[] : Array Expr)
  let_expr Cslib.WordRAM.Fits w v := target | return #[]
  forEachExpr v fun t => do
    if t.hasLooseBVars then return
    if let some (a, b) := natDivArgs? t then
      try acc.modify (·.push (← mkAppM ``Nat.div_le_self #[a, b])) catch _ => pure ()
    if let some (a, b) := natModArgs? t then
      try acc.modify (·.push (← mkAppM ``Nat.mod_le #[a, b])) catch _ => pure ()
      if isPowerOfTwo b then
        try
          let_expr HPow.hPow _ _ _ _ _ k := b | pure ()
          acc.modify (·.push (← mkAppM ``Nat.mod_lt #[a, mkApp (mkConst ``Nat.two_pow_pos) k]))
        catch _ => pure ()
      else if let some c := natLit? b then
        if c > 0 then
          try
            let posProp ← natLt (mkNatLit 0) b
            acc.modify (·.push (← mkAppM ``Nat.mod_lt #[a, ← mkDecideProof posProp]))
          catch _ => pure ()
    if let some (a, b) := natAndArgs? t then
      try
        acc.modify (·.push (← mkAppOptM ``Nat.and_le_left #[some a, some b]))
        acc.modify (·.push (← mkAppOptM ``Nat.and_le_right #[some a, some b]))
      catch _ => pure ()
    if let some (a, k) := natShiftRightArgs? t then
      try acc.modify (·.push (← mkAppM ``Nat.shiftRight_le #[a, k])) catch _ => pure ()
  if v == w then
    try acc.modify (·.push (← mkAppOptM ``Nat.lt_two_pow_self #[some w])) catch _ => pure ()
  acc.get

/-- The most hypotheses that mention `Fits` for which `prove?` tries `omega`. Beyond it, as in
proofs that state one generated fact per written value, `prove?` only looks for a hypothesis of the
same statement: `omega` over many large facts, once per value written, would cost more than the
statements save. -/
private def maxFacts : ℕ := 16

/-- The heartbeats `prove?` may spend on one bound, in thousands, as for `maxHeartbeats`: a bound
that `omega` does not settle quickly, for instance through case splits on divisions, is left to
the given simp lemmas rather than slowing every evaluation, which may try hundreds of bounds. -/
private def maxHeartbeats : ℕ := 200

/-- A proof of the word-size bound `target` by `omega` from the hypotheses that mention `Fits`
and target-only dominance facts, or `none`. -/
def prove? (target : Expr) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  unless isWordBound target.cleanupAnnotations do return none
  let target' := target.cleanupAnnotations
  let exact? ← (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    let eq := (← instantiateMVars d.type).cleanupAnnotations == target'
    return if eq then some d.toExpr else none
  if exact?.isSome then return exact?
  match_expr target' with
  | Cslib.WordRAM.Fits w v =>
    match_expr v with
    | Cslib.WordRAM.Data.regs _ x i =>
      for (hb, w', xb) in ← collectBoundedHyps do
        if w' == w && xb == x then
          return some (mkApp (← mkAppM ``And.left #[hb]) i)
    | Cslib.WordRAM.Data.mem _ x a =>
      for (hb, w', xb) in ← collectBoundedHyps do
        if w' == w && xb == x then
          return some (mkApp (← mkAppM ``And.right #[hb]) a)
    | _ => pure ()
  | _ => pure ()
  let count ← (← getLCtx).foldlM (init := 0) fun n d =>
    return if !d.isImplementationDetail && mentionsWordFits d.type then n + 1 else n
  let extra ← quickTargetFacts target'
  if (count == 0 && extra.isEmpty) || count > maxFacts then return none
  let facts ← fitsHypotheses (includeSigned := false)
  let unfolded ← unfoldFits target
  let proofs ← facts.mapM fun h => mkExpectedTypeHint h.value h.type
  let some prf ← proveOmega? maxHeartbeats (proofs ++ extra).toList unfolded | return none
  return some (← mkExpectedTypeHint prf target)

/-- Rewrite a word-size bound `Fits w v` to `True` when `prove?` proves it. -/
private def reduceFitsStep : Simp.Simproc := fun e => do
  unless e.isAppOfArity ``Cslib.WordRAM.Fits 2 do return .continue
  let some h ← prove? e | return .continue
  return .done { expr := mkConst ``True, proof? := some (← mkEqTrue h) }

/-- `fits` proves a word-size bound `Fits w v`, `v < 2 ^ w`, or `GenericRAM.Signed.Fits w z`, by
linear arithmetic. It unfolds `Fits` in the goal and in each hypothesis that mentions it, and runs
`omega`; hypotheses are found by their statements, whatever their names.

When the direct linear attempt cannot close the bound, `fits` injects bounded dominance facts for
subexpressions present in the goal and arithmetic context (`Nat.div_le_self`, `Nat.mod_le`,
`Nat.mod_lt`, `Nat.and_le_left`/`right`, `Nat.shiftRight_le`, `Nat.xor_lt_two_pow`,
`Nat.or_lt_two_pow`, `Nat.lt_two_pow_self`, power-of-two monotonicity, `Fin.isLt`, and
`Data.Bounded` register/memory reads), then retries `omega`.

* `fits [h₁, h₂]` also uses the statements of the terms `h₁` and `h₂`, unfolded likewise, for
  facts `omega` cannot derive, such as bounds on products.

It fails on a goal that is not a word-size bound, for which plain `omega` is the right call.

`fits` unfolds `Fits` only. Use `wram_omega` for a word-size bound that needs definitions tagged
`@[wram_arith]` unfolded, such as `Fits w (keysBase base n + i)` from `Fits w (base + space n)`,
and for a goal of another shape that follows from hypotheses `Fits w v`. -/
syntax (name := fits) "fits" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| fits $[[$terms,*]]?) => focus <| withMainContext do
    let g ← getMainGoal
    let target ← instantiateMVars (← g.getType)
    unless isWordBound target.cleanupAnnotations do
      throwError "fits: the goal is not a word-size bound `Fits w v` or `v < 2 ^ w`; use \
        `omega` for other arithmetic.{indentExpr target}"
    let mut baseFacts ← fitsHypotheses
    let found := baseFacts.size
    for t in (terms.map (·.getElems)).getD #[] do
      let e ← elabTerm t none
      let type ← unfoldFits (← instantiateMVars (← inferType e))
      baseFacts := baseFacts.push { userName := `this, type, value := e }
    let targetUnfolded ← unfoldFits target
    -- Stage 1: fast linear path (zero preprocessing overhead on simple bounds).
    let s1 ← saveState
    let fastFacts := baseFacts ++ (← powerFacts (baseFacts.map (·.type) |>.push targetUnfolded))
    let g1 ← g.replaceTargetDefEq targetUnfolded
    let (_, g1) ← g1.assertHypotheses fastFacts
    replaceMainGoal [g1]
    try
      evalTactic (← `(tactic| omega))
      return
    catch _ =>
      s1.restore
    -- Stage 2: inject targeted dominance facts for subexpressions in the goal and context.
    let domFacts ← dominanceFacts baseFacts targetUnfolded
    let allFacts := baseFacts ++ domFacts
    let g2 ← g.replaceTargetDefEq targetUnfolded
    let (_, g2) ← g2.assertHypotheses allFacts
    replaceMainGoal [g2]
    try
      evalTactic (← `(tactic| omega))
    catch ex =>
      let foundMsg := if found == 0 then m!"There is no hypothesis `Fits w v` in context."
        else m!"Hypotheses that mention `Fits`: {found}."
      throwError "fits: `omega` could not prove the bound. {foundMsg} Products are atoms, so give \
        bounds on them with `fits [h]`.\n{g2}\n{ex.toMessageData}"

end Cslib.Tactic.Fits

end

public section

namespace Cslib.WordRAM

/-- `simp` procedure that rewrites a word-size bound `Fits w v` to `True` when `omega` proves it
from the hypotheses `Fits w' v'` in context and target-only dominance facts. `ram_eval` and
`ram_exact_eval` use it to decide which written values fit a word. -/
simproc_decl reduceFits (Fits _ _) := Cslib.Tactic.Fits.reduceFitsStep

end Cslib.WordRAM

end
