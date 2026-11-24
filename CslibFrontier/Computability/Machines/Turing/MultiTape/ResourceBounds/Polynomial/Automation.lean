/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Init
public import Mathlib.Data.Nat.Sqrt
public meta import Lean.Elab.Tactic

/-!
# Compositional polynomial resource bounds

`growth_poly` proves `Turing.MultiTapeTM.PolyBounded size cost` by the closure rules for
constants, the input size, addition, multiplication, fixed powers, powers with additive,
constant-multiple, minimum or locally bounded exponents, conditionals
(`if`, non-dependent `dite`, `cond`), one-sided `min`, and extensible `@[growth_poly]` closure and
pointwise `ℕ` bound/equation rules (covering floor and ceiling logarithms, `Nat.log2`,
`b ^ Nat.log b _`, square root, maximum, truncated subtraction, division and remainder, structural
`List.length` bounds, and encoded-length expansions for `encPair`, `encUnary`, `encBool`,
`encBits`, `encNat` and `enc_structure` encodings). It also accepts `Cslib.PolynomiallyBounded`
goals through the existing `fun_prop` rules.

Modules extend `growth_poly` without modifying this file by tagging theorems with `@[growth_poly]`
(declared in `ResourceBounds.Polynomial.Init`): either a pointwise bound `lhs ≤ rhs` or equation
`lhs = rhs` in `ℕ`, or a `PolyBounded` closure rule `PolyBounded size (fun a => op …)`.

The leaves come from the local context and optional `[h₁, h₂]` hints:

* `PolyBounded` hypotheses, also inside conjunctions and
  inside definitions that unfold to them, such as a native certificate's `IsPolynomial`; any
  `PolyBounded` bound on an encoded length `(enc x).length` — including `PolyBounded.self` on the
  input size itself — is automatically decomposed into its sub-components (`encPair` projections,
  `encList` element counts, `encUnary` values, `encBits` lengths, and `enc_structure` fields via
  `_apply`);
* pointwise `ℕ` upper-bound or equality facts (`∀ …, u ≤ v` or `∀ …, u = v`) in context or passed
  in `[h₁, …]`, which reduce `u` to `v` via `PolyBounded.mono`;
* certificates whose output length is polynomially bounded, such as
  `ComputableInPolyTime f encIn encOut`; with `encOut = encUnary` the value `f a` itself is
  bounded, with `encOut = encBits` the length of the word `f a`, and with `encOut = encList enc`
  both `(encList enc (f a)).length` and `(f a).length`;
* `Cslib.PolynomiallyBounded p` hypotheses, or `fun_prop` facts, applied at `size a` or as
  `p (u a)`;
* a `PolyBounded size' v` hypothesis at another size applied as `v (g a)`, which leaves the
  substitution `PolyBounded size (fun a => size' (g a))`.

A certificate supplies a leaf only through a lemma, and this module does not import those lemmas,
so that it stays below the machine layers. For each kind of certificate the proof uses, import
the module that proves its lemma (names relative to `CslibFrontier.Computability.Machines.Turing`,
the last one to `CslibFrontier.Computability`):

* `ComputableInPolyTime`, output length: `MultiTape.Internal.PolyTimePrimitives`, which
  `MultiTape.Complexity.PolyTime.Basic` imports;
* `ComputableInPolyTime` with `encUnary` output, the value: `MultiTape.Internal.PolyTimeLoops`,
  which `MultiTape.Complexity.PolyTime.Fold` imports;
* `encList` output or `PolyBounded` length, the element count `(f a).length`:
  `MultiTape.Complexity.Lists`, which `MultiTape.Complexity.PolyTime.List` and
  `MultiTape.Encodings.Length` import;
* `ComputableInPolySpace`: `MultiTape.Complexity.PolySpace.Plain`;
* `ComputableInLogSpace`: `MultiTape.Complexity.LogSpace`;
* `DegreeBounded`: `MultiTape.ResourceBounds.Degree`;
* `Cslib.GenericRAM.NativeCertificate`: `GenericRAM.Native.Certificate`.

When a certificate in the context gives no leaf because its lemma is not imported, the failure
message names the module to import.

Local `let` values, non-class structure projections, and definitions that unfold in bounded steps
to supported operations or leaves are unfolded without memoization;
leaf checks may invoke `unfoldDefinition?`, `isDefEq` and `fun_prop`. The tactic proves polynomial
growth only. Word admission, exact time bounds and signed overflow conditions remain separate
obligations, and it does not guess an intermediate size measure: a substitution needs the outer
bound as a fact. The search is bounded and syntax-directed—trying `min_left` then `min_right` once
at each `min` node without backtracking across surrounding operations—so an unsupported goal fails
directly and names the term it could not bound.

## Main declarations

* `Turing.MultiTapeTM.PolyBounded.log`, `clog`, `sqrt`, `max`, `min_left`, `min_right`, `sub`,
  `div`, `mod`, `ite`, `cond`: further closure rules.
* `Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp`: substitution into a polynomially
  bounded function of one natural number.
* `growth_poly`, `growth_poly [h₁, h₂]`: prove polynomial growth from these rules and the local
  context, with extra facts `h₁` and `h₂`.
* `Cslib.Tactic.GrowthPoly.certificateLemmas`: the certificate lemmas the tactic uses, with the
  modules that prove them.

The closure layer adapts Samuel Schlesinger's existing polynomial-bound API. The input-size
logarithm and square-root rules and the first `growth_poly` tactic are by Erik Demaine.
-/

public section

namespace Turing.MultiTapeTM.PolyBounded

variable {α : Type*} {size u v : α → ℕ}

/-- Natural logarithms preserve polynomial growth in any input-size measure. -/
@[growth_poly]
theorem log (b : ℕ) (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log b (u a)) :=
  hu.mono fun a => Nat.log_le_self b (u a)

/-- Natural ceiling logarithms preserve polynomial growth in any input-size measure. -/
@[growth_poly]
theorem clog (b : ℕ) (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.clog b (u a)) :=
  hu.mono fun a => by
    rcases le_or_gt b 1 with hb | hb
    · rw [Nat.clog_of_left_le_one hb]; exact Nat.zero_le _
    · exact Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le

/-- Natural square roots preserve polynomial growth in any input-size measure. -/
@[growth_poly]
theorem sqrt (hu : PolyBounded size u) : PolyBounded size (fun a => Nat.sqrt (u a)) :=
  hu.mono fun a => Nat.sqrt_le_self (u a)

/-- The maximum of two polynomially bounded functions is polynomially bounded. -/
@[growth_poly]
theorem max (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => Max.max (u a) (v a)) :=
  (hu.add hv).mono fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- The minimum of two functions preserves a polynomial bound on its first argument. -/
theorem min_left (hu : PolyBounded size u) (v : α → ℕ) :
    PolyBounded size (fun a => Min.min (u a) (v a)) :=
  hu.mono fun a => Nat.min_le_left (u a) (v a)

/-- The minimum of two functions preserves a polynomial bound on its second argument. -/
theorem min_right (u : α → ℕ) (hv : PolyBounded size v) :
    PolyBounded size (fun a => Min.min (u a) (v a)) :=
  hv.mono fun a => Nat.min_le_right (u a) (v a)

/-- Truncated subtraction preserves a polynomial bound on its first argument. -/
@[growth_poly]
theorem sub (hu : PolyBounded size u) (v : α → ℕ) : PolyBounded size (fun a => u a - v a) :=
  hu.mono fun a => Nat.sub_le (u a) (v a)

/-- Natural division preserves a polynomial bound on its dividend. -/
@[growth_poly]
theorem div (hu : PolyBounded size u) (v : α → ℕ) : PolyBounded size (fun a => u a / v a) :=
  hu.mono fun a => Nat.div_le_self (u a) (v a)

/-- Natural remainder preserves a polynomial bound on its dividend. -/
@[growth_poly]
theorem mod (hu : PolyBounded size u) (v : α → ℕ) : PolyBounded size (fun a => u a % v a) :=
  hu.mono fun a => Nat.mod_le (u a) (v a)

/-- Conditional expressions preserve polynomial bounds across their branches. -/
theorem ite {c : α → Prop} [DecidablePred c] (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => if c a then u a else v a) :=
  (hu.add hv).mono fun _ => by
    split
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _

/-- Boolean conditionals preserve polynomial bounds across their branches. -/
theorem cond {b : α → Bool} (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => _root_.cond (b a) (u a) (v a)) :=
  (hu.add hv).mono fun a => by
    cases b a
    · exact Nat.le_add_left _ _
    · exact Nat.le_add_right _ _

/-- Substitute a polynomially bounded argument into a polynomially bounded function of one
natural number. -/
theorem of_polynomiallyBounded_comp {p : ℕ → ℕ} (hp : Cslib.PolynomiallyBounded p)
    (hu : PolyBounded size u) : PolyBounded size (fun a => p (u a)) :=
  (of_polynomiallyBounded id hp).comp hu

end Turing.MultiTapeTM.PolyBounded

attribute [growth_poly]
  Nat.pow_log_le_add_one Nat.log2_le_self
  List.length_nil List.length_cons List.length_append List.length_map List.length_replicate
  List.length_reverse List.length_take List.length_drop List.length_filter_le
  List.length_range List.length_ofFn List.length_finRange List.length_zip List.length_zipIdx
  List.length_set List.length_tail List.length_eraseIdx_le

/-- `growth_poly` proves `Turing.MultiTapeTM.PolyBounded size cost` by the closure rules for
constants, the input size, `+`, `*`, fixed powers, powers with additive, constant-multiple,
minimum or locally bounded exponents, conditionals (`if`, non-dependent
`dite`, `cond`), one-sided `min`, and extensible `@[growth_poly]` closure and `ℕ` bound/equation
rules (including `Nat.log`, `Nat.clog`, `Nat.log2`, `b ^ Nat.log b _`, `Nat.sqrt`, `max`,
truncated `-`, `/`, `%`, structural `List.length` bounds, and encoding-length rules for `encPair`,
`encUnary`, `encBool`, `encBits`, `encNat`, and `enc_structure` encodings).

The leaves come from local `PolyBounded` facts (also inside conjunctions
and definitions that unfold to them, with encoded-length bounds — including the input size itself
— decomposed into `encPair`, `encList`, `encUnary`, `encBits`, and `enc_structure` components);
from local or passed pointwise `ℕ` inequalities/equations (`∀ …, u ≤ v` or `u = v`); from local
certificates, through their output-length bound; and from local `Cslib.PolynomiallyBounded`
functions or `PolyBounded` facts at another size, applied to the input size or a bounded
argument. `growth_poly [h₁, h₂]` adds the facts `h₁` and `h₂`.

A certificate gives a leaf only when the module proving its bound is imported; the module
docstring lists them, for example `MultiTape.Internal.PolyTimePrimitives` for the output length
of `ComputableInPolyTime`. When a certificate in the context gives no leaf for this reason, the
failure names the module to import.

Local `let` values, non-class structure projections, and definitions that unfold in bounded steps
to supported operations or leaves are unfolded without memoization, and leaf checks
may invoke `unfoldDefinition?`, `isDefEq` and `fun_prop`. The search is bounded and
syntax-directed—trying `min_left` then `min_right` once at each `min` node without backtracking
across surrounding operations—so an unsupported goal fails directly and names the term it could not
bound. `Cslib.PolynomiallyBounded` goals go to `fun_prop`. -/
syntax (name := growthPoly) "growth_poly" (" [" term,* "]")? : tactic

public meta section

namespace Cslib.Tactic.GrowthPoly

open Lean Meta Elab Tactic

/-- A lemma from a certificate to a `PolyBounded` fact or to another certificate. -/
structure CertificateLemma where
  /-- The lemma, applied to the local hypotheses whose head it matches when it is in scope. -/
  name : Name
  /-- The head constant of the certificate it takes, its last explicit hypothesis. -/
  head : Name
  /-- The output encoding, the certificate's last argument, that the lemma requires, if any. -/
  outEnc : Option Name := none
  /-- The module proving the lemma, named when the lemma is not in scope. -/
  module : Name

/-- The certificate lemmas, applied when they are in scope. This module does not import them,
which would make it depend on the machine layers. A lemma that requires an output encoding comes
before the general lemma with the same head, and its module imports that lemma's module.
The drift check in the `PolynomialGrowth` test checks that each lemma is proved in its `module`. -/
def certificateLemmas : List CertificateLemma :=
  [{ name := `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded
     head := `Turing.MultiTapeTM.ComputableInPolyTime
     outEnc := `Turing.MultiTapeTM.encUnary
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops },
   { name := `Turing.MultiTapeTM.ComputableInPolyTime.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInPolyTime
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives },
   { name := `Turing.MultiTapeTM.ComputableInPolySpace.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInPolySpace
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain },
   { name := `Turing.MultiTapeTM.ComputableInLogSpace.polyBounded_length
     head := `Turing.MultiTapeTM.ComputableInLogSpace
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace },
   { name := `Turing.MultiTapeTM.DegreeBounded.polyBounded
     head := `Turing.MultiTapeTM.DegreeBounded
     module := `CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree },
   { name := `Cslib.GenericRAM.NativeCertificate.polyTime
     head := `Cslib.GenericRAM.NativeCertificate.IsPolynomial
     module := `CslibFrontier.Computability.GenericRAM.Native.Certificate }]

/-- The lemma bounding `l.length` by `(encList enc l).length`, used to derive element-count leaves
from `encList` length bounds when `MultiTape.Complexity.Lists` is imported. -/
def encListLemma : CertificateLemma :=
  { name := `Turing.MultiTapeTM.length_le_length_encList
    head := ``Turing.MultiTapeTM.PolyBounded
    module := `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists }

/-- The facts available to `growth_poly`. -/
private structure Facts where
  /-- Proofs of `PolyBounded size v`, paired with whether they may serve as the outer function in
  `PolyBounded.comp` (`false` for identity-bounded facts and input-size decompositions). -/
  bounds : Array (Expr × Bool) := #[]
  /-- Proofs of `Cslib.PolynomiallyBounded p`, with their `p`. -/
  polys : Array (Expr × Expr) := #[]
  /-- Local or hinted pointwise `ℕ` inequalities/equations (`∀ …, lhs ≤ rhs` or `lhs = rhs`),
  indexed by the LHS head constant name. -/
  leBounds : Std.HashMap Name (Array Expr) := {}
  /-- Local or hinted pointwise `ℕ` inequalities/equations whose LHS head is a local variable. -/
  leBoundsFVar : Std.HashMap FVarId (Array Expr) := {}
  /-- Certificates that give no fact because their lemma is not in scope, with that lemma. -/
  unused : Array (Expr × CertificateLemma) := #[]

/-- The size and the bounded function of `PolyBounded size u`. -/
private def polyBoundedArgs? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Turing.MultiTapeTM.PolyBounded 3 then
    some (e.getArg! 1, e.getArg! 2)
  else none

/-- Replace a local `let` variable or `let` at the head of `e` by its value, and beta reduce. -/
private partial def zetaHead (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e.getAppFn with
  | .fvar id =>
    match ← id.getValue? with
    | some v => zetaHead (v.beta e.getAppArgs)
    | none => return e
  | .letE _ _ v b _ => zetaHead ((b.instantiate1 v).beta e.getAppArgs)
  | .mdata _ b => zetaHead (b.beta e.getAppArgs)
  | _ => return e

/-- Reduce projections `Prod.fst` and `Prod.snd` applied to (possibly nested) `Prod.mk` terms. -/
private partial def reduceProdProj (e : Expr) : Expr :=
  e.replace fun t =>
    let proj? : Option (Nat × Expr × (Expr → Expr)) :=
      match t with
      | .proj ``Prod idx s => some (idx, s, .proj ``Prod idx)
      | _ =>
        if t.isAppOfArity ``Prod.fst 3 then
          some (0, t.getArg! 2, fun s' => mkApp3 t.getAppFn (t.getArg! 0) (t.getArg! 1) s')
        else if t.isAppOfArity ``Prod.snd 3 then
          some (1, t.getArg! 2, fun s' => mkApp3 t.getAppFn (t.getArg! 0) (t.getArg! 1) s')
        else none
    proj?.bind fun (idx, s, rebuild) =>
      let s' := reduceProdProj s
      if s'.isAppOfArity ``Prod.mk 4 then some (s'.getArg! (2 + idx))
      else if s' != s then some (rebuild s')
      else none

/-- Drop `Function.comp` applications `(f ∘ g) x` to `f (g x)` everywhere inside `e`. -/
private def reduceComp (e : Expr) : CoreM Expr :=
  Core.betaReduce <| e.replace fun t =>
    if t.isAppOfArity ``Function.comp 6 then
      some (mkApp (t.getArg! 3) (mkApp (t.getArg! 4) t.appArg!))
    else if t.isAppOfArity ``Function.comp 5 then
      some (.lam `x (t.getArg! 0) (mkApp ((t.getArg! 3).liftLooseBVars 0 1)
        (mkApp ((t.getArg! 4).liftLooseBVars 0 1) (.bvar 0))) .default)
    else none

/-- Read the bound a certificate gives in the form goals use: drop the identity encoding
`encBits` from `(encBits w).length`, expand `Function.uncurry`, and write `(f ∘ g) a` as
`f (g a)`. -/
private def normalizeFact (ty : Expr) : CoreM Expr := do
  let ty := ty.replace fun e =>
    if e.isAppOfArity ``DFunLike.coe 6 && e.getArg! 4 == mkConst `Turing.MultiTapeTM.encBits then
      some e.appArg!
    else if e.isAppOfArity ``Function.uncurry 4 then
      match e.getAppFn with
      | .const _ [u₁, u₂, _] =>
        let α := e.getArg! 0
        let β := e.getArg! 1
        let f := e.getArg! 3
        some (.lam `p (mkApp2 (mkConst ``Prod [u₁, u₂]) α β)
          (mkApp2 (f.liftLooseBVars 0 1)
            (mkApp3 (mkConst ``Prod.fst [u₁, u₂]) α β (.bvar 0))
            (mkApp3 (mkConst ``Prod.snd [u₁, u₂]) α β (.bvar 0)))
          .default)
      | _ => none
    else none
  reduceComp ty

/-- Primitive encodings whose structure is handled directly rather than through `_apply`. -/
private def isPrimitiveEnc (c : Name) : Bool :=
  c == `Turing.MultiTapeTM.encPair || c == `Turing.MultiTapeTM.encList ||
  c == `Turing.MultiTapeTM.encUnary || c == `Turing.MultiTapeTM.encBits ||
  c == `Turing.MultiTapeTM.encFramed || c == `Turing.MultiTapeTM.encNat ||
  c == `Turing.MultiTapeTM.encBool || c == `Turing.MultiTapeTM.encUnit ||
  c == `Turing.MultiTapeTM.encOption || c == `Turing.MultiTapeTM.encSum

/-- If `enc` is an `enc_structure`-style encoding whose `<name>_apply` theorem rewrites
`enc val` to `eFields fieldsTuple` (another `DFunLike.coe` application), return
`(eFields, fieldsTuple, eqPf)` where `eqPf : enc val = eFields fieldsTuple`. -/
private def structEncApply? (enc val : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some c := enc.getAppFn.constName? | return none
  if isPrimitiveEnc c then return none
  let applyName := c.appendAfter "_apply"
  let env ← getEnv
  unless env.contains applyName do return none
  let saved ← saveState
  try
    let lem ← mkConstWithFreshMVarLevels applyName
    let (xs, binders, concl) ← forallMetaTelescope (← inferType lem)
    let some (_, lhs, rhs) := concl.eq? | do saved.restore; return none
    let target ← mkAppM ``DFunLike.coe #[enc, val]
    unless ← withReducibleAndInstances (isDefEq lhs target) do
      saved.restore; return none
    for x in xs, binder in binders do
      let g := x.mvarId!
      if ← g.isAssigned then continue
      if binder.isInstImplicit then
        g.assign (← synthInstance (← instantiateMVars (← g.getType)))
    let eqPf ← instantiateMVars (mkAppN lem xs)
    let rhs ← instantiateMVars rhs
    if eqPf.hasExprMVar || rhs.hasExprMVar then
      saved.restore; return none
    unless rhs.isAppOfArity ``DFunLike.coe 6 do
      saved.restore; return none
    return some (rhs.getArg! 4, rhs.getArg! 5, eqPf)
  catch _ =>
    saved.restore
    return none

/-- Is `u` syntactically the identity function `id` or `fun x => x`? -/
private def isIdFn (u : Expr) : Bool :=
  u.isAppOfArity ``id 1 ||
  match u with
  | .lam _ _ b _ => b == .bvar 0 || (b.isAppOfArity ``id 2 && b.appArg! == .bvar 0)
  | _ => false

/-- Recursively derive sub-component `PolyBounded` leaves from `pf : PolyBounded size u` when `u`
has the form `fun x => (enc (val x)).length`, decomposing `encPair`, `encList`, `encUnary`,
`encBits`, and `enc_structure` encodings up to `depth` layers. -/
private partial def decomposeEncBound (facts : Facts) (origPf pf size u : Expr) (depth : Nat := 6)
    (allowComp : Bool := true) : MetaM Facts := do
  if depth == 0 then return facts
  try
    let .forallE _ α _ _ ← whnfR (← inferType u) | return facts
    withLocalDeclD `x α fun x => do
      let b ← zetaHead ((u.beta #[x]).headBeta)
      unless b.isAppOfArity ``List.length 2 do return facts
      let arg ← zetaHead (b.getArg! 1)
      unless arg.isAppOfArity ``DFunLike.coe 6 do return facts
      let encWhnf ← withReducible (whnf (← zetaHead (arg.getArg! 4)))
      let val := arg.getArg! 5
      let env ← getEnv
      let pushSub (facts : Facts) (subBody hleBody : Expr) (recurse : Bool) : MetaM Facts := do
        let uSub ← mkLambdaFVars #[x] subBody
        let hle ← mkLambdaFVars #[x] hleBody
        let expectedLe ← mkForallFVars #[x] (← mkAppM ``LE.le #[mkApp uSub x, mkApp u x])
        let pfSub ← mkAppM ``Turing.MultiTapeTM.PolyBounded.mono
          #[pf, ← mkExpectedTypeHint hle expectedLe]
        let pfSubTy ← inferType pfSub
        let pfSubTy ←
          if let some (_, u') := polyBoundedArgs? pfSubTy then
            pure (mkAppN pfSubTy.getAppFn #[pfSubTy.getArg! 0, size, ← normalizeFact u'])
          else normalizeFact pfSubTy
        let pfSub ← mkExpectedTypeHint pfSub pfSubTy
        let subU := pfSubTy.getArg! 2
        let facts := { facts with bounds := facts.bounds.push (pfSub, allowComp && !isIdFn subU) }
        if recurse then decomposeEncBound facts origPf pfSub size subU (depth - 1) allowComp
        else return facts
      if encWhnf.isAppOfArity `Turing.MultiTapeTM.encList 2 then
        unless env.contains encListLemma.name do
          if facts.unused.any fun (pf', l') => pf' == origPf && l'.name == encListLemma.name then
            return facts
          return { facts with unused := facts.unused.push (origPf, encListLemma) }
        let elemTy := encWhnf.getArg! 0
        let innerEnc := encWhnf.getArg! 1
        return ← pushSub facts
          (← mkAppOptM ``List.length #[some elemTy, some val])
          (← mkAppOptM encListLemma.name #[some elemTy, some innerEnc, some val]) false
      if encWhnf.isAppOfArity `Turing.MultiTapeTM.encPair 4 then
        unless env.contains `Turing.MultiTapeTM.length_le_encPair_left &&
            env.contains `Turing.MultiTapeTM.length_le_encPair_right do
          return facts
        let (α₁, α₂, e₁, e₂) :=
          (encWhnf.getArg! 0, encWhnf.getArg! 1, encWhnf.getArg! 2, encWhnf.getArg! 3)
        let v₁ := reduceProdProj (mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) α₁ α₂ val)
        let v₂ := reduceProdProj (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) α₁ α₂ val)
        let mut facts := facts
        for (lem, eSub, vSub) in
            #[(`Turing.MultiTapeTM.length_le_encPair_left, e₁, v₁),
              (`Turing.MultiTapeTM.length_le_encPair_right, e₂, v₂)] do
          let encVal ← mkAppM ``DFunLike.coe #[eSub, vSub]
          let hleBody ← mkAppOptM lem #[some α₁, some α₂, some e₁, some e₂, some val]
          facts ← pushSub facts (← mkAppM ``List.length #[encVal]) hleBody true
        return facts
      if encWhnf.isConstOf `Turing.MultiTapeTM.encUnary &&
          env.contains `Turing.MultiTapeTM.encUnary_apply then
        let repLen ← mkAppOptM ``List.length_replicate
          #[some (mkConst ``Bool), some val, some (mkConst ``Bool.true)]
        return ← pushSub facts val (← mkAppM ``Nat.le_of_eq #[← mkAppM ``Eq.symm #[repLen]]) false
      if encWhnf.isConstOf `Turing.MultiTapeTM.encBits &&
          env.contains `Turing.MultiTapeTM.encBits_apply then
        let sub ← mkAppM ``List.length #[val]
        return ← pushSub facts sub (← mkAppM ``Nat.le_refl #[sub]) false
      if let some (eFields, fieldsTuple, eqPf) ← structEncApply? encWhnf val then
        let encVal ← mkAppM ``DFunLike.coe #[eFields, fieldsTuple]
        let lenEq ← mkCongrArg (mkConst ``List.length [Level.zero] |>.app (mkConst ``Bool)) eqPf
        return ← pushSub facts (← mkAppM ``List.length #[encVal])
          (← mkAppM ``Nat.le_of_eq #[← mkAppM ``Eq.symm #[lenEq]]) true
      return facts
  catch _ =>
    return facts

/-- Record a pointwise `ℕ` inequality/equation hypothesis `pf : ∀ …, lhs ≤ rhs` or `lhs = rhs`
under the LHS head constant name or local variable. -/
private def addQuantifiedFact (facts : Facts) (pf ty : Expr) : Facts :=
  match boundSides? ty.getForallBody with
  | some (lhs, _, _) =>
    match lhs.getAppFn with
    | .const head _ =>
      let arr := facts.leBounds[head]?.getD #[]
      { facts with leBounds := facts.leBounds.insert head (arr.push pf) }
    | .fvar fid =>
      let arr := facts.leBoundsFVar[fid]?.getD #[]
      { facts with leBoundsFVar := facts.leBoundsFVar.insert fid (arr.push pf) }
    | _ => facts
  | none => facts

/-- Record `pf : ty` (originating from `origPf`), splitting conjunctions and unfolding definitions
until a `PolyBounded`, `Cslib.PolynomiallyBounded`, or pointwise `ℕ` bound appears, at most `depth`
steps deep. -/
private partial def addFact (facts : Facts) (origPf pf ty : Expr) (depth : Nat := 3) :
    MetaM Facts := do
  let ty ← whnfR (← instantiateMVars ty)
  if let some (size, _) := polyBoundedArgs? ty then
    let ty' ← normalizeFact ty
    let pf ← if (← inferType pf) == ty' then pure pf else mkExpectedTypeHint pf ty'
    let u' := ty'.getArg! 2
    let facts := { facts with bounds := facts.bounds.push (pf, !isIdFn u') }
    return ← decomposeEncBound facts origPf pf size u'
  if ty.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
    return { facts with polys := facts.polys.push (pf, ty.appArg!) }
  let facts := addQuantifiedFact facts pf ty
  if depth == 0 then return facts
  if ty.isAppOfArity ``And 2 then
    let facts ← addFact facts origPf (← mkAppM ``And.left #[pf]) ty.appFn!.appArg! (depth - 1)
    return ← addFact facts origPf (← mkAppM ``And.right #[pf]) ty.appArg! (depth - 1)
  if let some ty' ← unfoldDefinition? ty then
    return ← addFact facts origPf pf ty' (depth - 1)
  return facts

/-- The head constant of the type of the last explicit hypothesis of `lem`. -/
private def certificateHead? (lem : Name) : MetaM (Option Name) := do
  forallTelescopeReducing (← getConstInfo lem).type fun xs _ => do
    for x in xs.reverse do
      if (← x.fvarId!.getBinderInfo).isExplicit then
        return (← inferType x).getAppFn.constName?
    return none

/-- `lem` applied to `h` as its last explicit hypothesis, with every other argument determined by
unification up to reducible unfolding, or `none`. -/
private def applyCertificate? (lem : Name) (h : Expr) : MetaM (Option Expr) := do
  let c ← mkConstWithFreshMVarLevels lem
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := (List.range args.size).reverse.find? (binders[·]!.isExplicit) | return none
  unless ← withReducible (isDefEq (← inferType args[i]!) (← inferType h)) do return none
  args[i]!.mvarId!.assign h
  let pf ← instantiateMVars (mkAppN c args)
  return if pf.hasExprMVar then none else some pf

/-- The facts from the local context and the extra `hints`, with the bounds that certificates
give, following certificate lemmas at most two steps, plus sub-component leaves of the goal's
input size `size` when it is an encoded length. Certificates whose lemma is not in scope are
recorded in `unused`. -/
private def collectFacts (α size : Expr) (hints : Array Expr) : MetaM Facts := do
  let env ← getEnv
  let (present, absent) := certificateLemmas.partition (env.contains ·.name)
  let lemmas ← present.filterMapM fun l => return (← certificateHead? l.name).map (l.name, ·)
  let locals ← (← getLCtx).foldlM (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then pure acc else pure (acc.push decl.toExpr)
  let mut facts : Facts := {}
  -- Decompose the goal's own input size `size` when it is an encoded length.
  let selfPf ← mkAppOptM ``Turing.MultiTapeTM.PolyBounded.self #[some α, some size]
  facts ← decomposeEncBound facts selfPf selfPf size size (allowComp := false)
  let mut work := (hints ++ locals).map fun h => (h, h, 2)
  while !work.isEmpty do
    let (origPf, pf, depth) := work.back!
    work := work.pop
    let ty ← instantiateMVars (← inferType pf)
    unless ← isProp ty do continue
    facts ← addFact facts origPf pf ty (if depth == 2 then 3 else 0)
    if depth == 0 then continue
    let head := ty.getAppFn.constName?
    for (lem, lemHead) in lemmas do
      if head == some lemHead then
        if let some pf' ← applyCertificate? lem pf then
          work := work.push (origPf, pf', depth - 1)
    -- Name one missing module per certificate: the first matching lemma's, which is the specific
    -- one when there is one, and whose module imports the general lemma's.
    if let some l := absent.find? fun l => head == some l.head &&
        l.outEnc.all fun enc => ty.getAppArgs.back?.any (·.isConstOf enc) then
      unless facts.unused.any fun (pf', l') => pf' == origPf && l'.name == l.name do
        facts := { facts with unused := facts.unused.push (origPf, l) }
  return facts

/-- The core closure rule for `+`, `*`, or `^`. Other operations are registered via
`@[growth_poly]`. -/
private def coreOpRule? (body : Expr) : Option Name :=
  match body.getAppFn.constName?, body.getAppNumArgs with
  | some ``HAdd.hAdd, 6 => some ``Turing.MultiTapeTM.PolyBounded.add
  | some ``HMul.hMul, 6 => some ``Turing.MultiTapeTM.PolyBounded.mul
  | some ``HPow.hPow, 6 => some ``Turing.MultiTapeTM.PolyBounded.pow
  | _, _ => none

/-- The closure rule for a conditional expression, by head constant and arity. -/
private def condRule? (body : Expr) : Option Name :=
  match body.getAppFn.constName?, body.getAppNumArgs with
  | some ``_root_.ite, 5 => some ``Turing.MultiTapeTM.PolyBounded.ite
  | some ``_root_.cond, 4 => some ``Turing.MultiTapeTM.PolyBounded.cond
  | _, _ => none

/-- Rewrite a `dite` whose branches do not depend on the proof hypothesis to an `ite`. -/
private def nondepDiteToIte? (body : Expr) : MetaM (Option Expr) := do
  unless body.isAppOfArity ``_root_.dite 5 do return none
  let cProp := body.getArg! 1
  let inst := body.getArg! 2
  let tBranch ← withLocalDeclD `h cProp fun h => do
    let tb ← zetaHead ((body.getArg! 3).beta #[h])
    return if tb.containsFVar h.fvarId! then none else some tb
  let eBranch ← withLocalDeclD `hn (mkNot cProp) fun hn => do
    let eb ← zetaHead ((body.getArg! 4).beta #[hn])
    return if eb.containsFVar hn.fvarId! then none else some eb
  let (some tb, some eb) := (tBranch, eBranch) | return none
  return some (mkApp5 (mkConst ``_root_.ite [Level.one]) (mkConst ``Nat) cProp inst tb eb)

/-- Discharge remaining metavariable premises by typeclass synthesis or local assumption, optionally
leaving `PolyBounded` subgoals unassigned for the caller. Returns `false` if any non-`Prop`
metavariable remains unassigned. -/
private def dischargePremises (xs : Array Expr) (binders : Array BinderInfo)
    (allowPolySubgoals : Bool := false) : MetaM Bool := do
  for x in xs, binder in binders do
    let g := x.mvarId!
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if binder.isInstImplicit then
      g.assign (← synthInstance ty)
    else if allowPolySubgoals && (polyBoundedArgs? (← whnfR ty)).isSome then
      continue
    else if ← isProp ty then
      g.assumption
    else
      return false
  return true

/-- Apply a pointwise bound/equation proof `pf : ∀ …, lhs ≤ rhs` (or `lhs = rhs`) in `ℕ` to `body`,
returning `(rhs', hle)` where `hle : body ≤ rhs'` and `rhs' != body`. Any remaining `Prop`
premises must be discharged by local hypotheses; typeclass premises are synthesized. -/
private def applyPointwiseBound? (pf body : Expr) : MetaM (Option (Expr × Expr)) := do
  let saved ← saveState
  try
    let (xs, binders, concl) ← forallMetaTelescope (← instantiateMVars (← inferType pf))
    let some (lhs, rhs, isEq) := boundSides? concl | do saved.restore; return none
    unless ← withReducibleAndInstances (isDefEq lhs body) do
      saved.restore; return none
    unless ← dischargePremises xs binders do
      saved.restore; return none
    let pf' ← instantiateMVars (mkAppN pf xs)
    let rhs' ← instantiateMVars rhs
    if pf'.hasExprMVar || rhs'.hasExprMVar then
      saved.restore; return none
    let rhsRed := reduceProdProj rhs'
    if rhsRed == body then
      saved.restore; return none
    let hle ← if isEq then mkAppM ``Nat.le_of_eq #[pf'] else pure pf'
    return some (rhsRed, hle)
  catch _ =>
    saved.restore
    return none

/-- Reduce `List.length (DFunLike.coe enc arg)` for encodings whose length lemma is in scope
(`encPair`, `encUnary`, `encBool`, `encBits`, `encNat`, and `enc_structure` encodings), returning
`(rhs, hle)` where `hle : body ≤ rhs`. -/
private def encLengthBound? (body : Expr) : MetaM (Option (Expr × Expr)) := do
  unless body.isAppOfArity ``List.length 2 do return none
  let xs ← zetaHead (body.getArg! 1)
  let fromEq (eqPf : Expr) : MetaM (Option (Expr × Expr)) := do
    let eqTy ← inferType eqPf
    unless eqTy.isAppOfArity ``Eq 3 do return none
    unless ← withNewMCtxDepth (isDefEq body (eqTy.getArg! 1)) do return none
    let rhs := reduceProdProj (eqTy.getArg! 2)
    if rhs == body then return none
    return some (rhs, mkApp3 (mkConst ``Nat.le_of_eq) (eqTy.getArg! 1) (eqTy.getArg! 2) eqPf)
  if xs.isAppOfArity ``List.append 3 then
    return ← fromEq (← mkAppOptM ``List.length_append
      #[some (body.getArg! 0), some (xs.getArg! 1), some (xs.getArg! 2)])
  unless xs.isAppOfArity ``DFunLike.coe 6 do return none
  let encWhnf ← withReducible (whnf (← zetaHead (xs.getArg! 4)))
  let arg := xs.getArg! 5
  let env ← getEnv
  if encWhnf.isAppOfArity `Turing.MultiTapeTM.encPair 4 &&
      env.contains `Turing.MultiTapeTM.length_encPair then
    return ← fromEq (← mkAppOptM `Turing.MultiTapeTM.length_encPair
      #[some (encWhnf.getArg! 0), some (encWhnf.getArg! 1),
        some (encWhnf.getArg! 2), some (encWhnf.getArg! 3), some arg])
  if encWhnf.isConstOf `Turing.MultiTapeTM.encUnary &&
      env.contains `Turing.MultiTapeTM.encUnary_apply then
    return ← fromEq (← mkAppOptM ``List.length_replicate
      #[some (mkConst ``Bool), some arg, some (mkConst ``Bool.true)])
  if encWhnf.isConstOf `Turing.MultiTapeTM.encBool &&
      env.contains `Turing.MultiTapeTM.encBool_apply then
    return ← fromEq (← mkAppOptM ``List.length_singleton #[some (mkConst ``Bool), some arg])
  if encWhnf.isConstOf `Turing.MultiTapeTM.encBits &&
      env.contains `Turing.MultiTapeTM.encBits_apply then
    let rhs ← mkAppM ``List.length #[arg]
    return some (rhs, ← mkAppM ``Nat.le_refl #[rhs])
  if encWhnf.isConstOf `Turing.MultiTapeTM.encNat then
    if env.contains `Turing.MultiTapeTM.length_encNat_le_self then
      return some (arg, ← mkAppM `Turing.MultiTapeTM.length_encNat_le_self #[arg])
    if env.contains `Turing.MultiTapeTM.length_encNat_le_log2 then
      let pf ← mkAppM `Turing.MultiTapeTM.length_encNat_le_log2 #[← mkAppM ``Nat.le_refl #[arg]]
      if let some (_, rhs, false) := boundSides? (← inferType pf) then
        return some (rhs, pf)
  if let some (_, _, eqPf) ← structEncApply? encWhnf arg then
    return ← fromEq (← mkCongrArg (mkConst ``List.length [Level.zero] |>.app (mkConst ``Bool)) eqPf)
  return none

/-- Try matching a local or hinted pointwise `ℕ` bound from `facts.leBounds` or
`facts.leBoundsFVar`. -/
private def findLocalPointwiseBound? (facts : Facts) (body : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let pfs :=
    match body.getAppFn with
    | .const head _ => facts.leBounds[head]?.getD #[]
    | .fvar fid => facts.leBoundsFVar[fid]?.getD #[]
    | _ => #[]
  for pf in pfs do
    if let some res ← applyPointwiseBound? pf body then
      trace[growth_poly] "local/hint bound {pf}: {body} ≤ {res.1}"
      return some res
  return none

/-- Try matching a pointwise `ℕ` bound from local hypotheses, hints, or `@[growth_poly]`. -/
private def findPointwiseBound? (facts : Facts) (body : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some res ← findLocalPointwiseBound? facts body then return some res
  let cands ← (boundExt.getState (← getEnv)).getMatch body
  for rule in cands.reverse do
    if let some res ← applyPointwiseBound? (← mkConstWithFreshMVarLevels rule) body then
      trace[growth_poly] "registered bound {.ofConstName rule}: {body} ≤ {res.1}"
      return some res
  return none

/-- Reduce `b ^ e` when `b` does not depend on `a` and `e` does: split additive (`+`, `Nat.succ`),
constant-multiple (`c * e'`, `e' * c`), `min`, or locally bounded exponents. -/
private def powSplit? (facts : Facts) (a body : Expr) : MetaM (Option (Expr × Expr)) := do
  unless body.isAppOfArity ``HPow.hPow 6 do return none
  let b := body.getArg! 4
  let e := body.getArg! 5
  if b.containsFVar a.fvarId! || !e.containsFVar a.fvarId! then return none
  let fromEq (eqPf : Expr) : MetaM (Expr × Expr) := do
    let eqTy ← inferType eqPf
    let rhs := eqTy.getArg! 2
    return (rhs, mkApp3 (mkConst ``Nat.le_of_eq) (eqTy.getArg! 1) rhs eqPf)
  let eZ ← zetaHead e
  if eZ.isAppOfArity ``HAdd.hAdd 6 then
    return some (← fromEq (← mkAppM ``Nat.pow_add #[b, eZ.getArg! 4, eZ.getArg! 5]))
  if eZ.isAppOfArity ``Nat.succ 1 then
    return some (← fromEq (← mkAppM ``Nat.pow_succ #[b, eZ.getArg! 0]))
  if eZ.isAppOfArity ``HMul.hMul 6 then
    let e₁ := eZ.getArg! 4
    let e₂ := eZ.getArg! 5
    if !e₁.containsFVar a.fvarId! then
      return some (← fromEq (← mkAppM ``Nat.pow_mul' #[b, e₁, e₂]))
    if !e₂.containsFVar a.fvarId! then
      return some (← fromEq (← mkAppM ``Nat.pow_mul #[b, e₁, e₂]))
  if let some (k + 1) := b.nat? then
    let hpos ← mkExpectedTypeHint (mkApp (mkConst ``Nat.zero_lt_succ) (mkNatLit k))
      (← mkAppM ``LT.lt #[mkNatLit 0, b])
    if eZ.isAppOfArity ``Min.min 4 then
      let (e₁, e₂) := (eZ.getArg! 2, eZ.getArg! 3)
      let h1 ← mkAppM ``Nat.pow_le_pow_right #[hpos, ← mkAppM ``Nat.min_le_left #[e₁, e₂]]
      let h2 ← mkAppM ``Nat.pow_le_pow_right #[hpos, ← mkAppM ``Nat.min_le_right #[e₁, e₂]]
      let rhs ← mkAppM ``Min.min #[← mkAppM ``HPow.hPow #[b, e₁], ← mkAppM ``HPow.hPow #[b, e₂]]
      return some (rhs, ← mkAppM ``le_min #[h1, h2])
    if let some (e', hle) ← findLocalPointwiseBound? facts eZ then
      return some (← mkAppM ``HPow.hPow #[b, e'], ← mkAppM ``Nat.pow_le_pow_right #[hpos, hle])
  return none

/-- Try applying a registered `@[growth_poly]` closure rule from `closureExt` to `goalTy` without
mutating the metavariable context. Returns the first rule name that unifies with `goalTy`. -/
private def findClosureRule? (goalTy body : Expr) : MetaM (Option Name) := do
  let cands ← (closureExt.getState (← getEnv)).getMatch body
  for rule in cands.reverse do
    let fits ← withNewMCtxDepth do
      try
        let c ← mkConstWithFreshMVarLevels rule
        let (xs, binders, concl) ← forallMetaTelescopeReducing (← inferType c)
        unless ← isDefEq concl goalTy do return false
        dischargePremises xs binders (allowPolySubgoals := true)
      catch _ =>
        return false
    if fits then return some rule
  return none

/-- How `growth_poly` takes a goal apart. -/
private inductive Step where
  /-- Close the goal with this proof. -/
  | close (pf : Expr)
  /-- Apply this closure rule and continue with its `PolyBounded` subgoals. -/
  | apply (rule : Name)
  /-- Apply this rule to the fact `pf` and continue with the remaining `PolyBounded` subgoals. -/
  | applyTo (rule : Name) (pf : Expr)
  /-- Apply an already-instantiated rule proof and continue with its `PolyBounded` subgoals. -/
  | applyProof (rulePf : Expr)
  /-- Try proving the goal with `first`; if that fails, restore state and apply `second`. -/
  | applyFirst (first second : Name)
  /-- Continue with this definitionally equal bounded function. -/
  | change (u : Expr)
  /-- Reduce `u` to `u'` via a pointwise bound `∀ a, u a ≤ u' a`. -/
  | mono (u' hle : Expr)

/-- Is `e` a function from natural numbers to natural numbers? -/
private def isNatFun (e : Expr) : MetaM Bool := do
  match ← whnfR (← inferType e) with
  | .forallE _ d b _ => return d.isConstOf ``Nat && !b.hasLooseBVars && b.isConstOf ``Nat
  | _ => return false

/-- Prove `Cslib.PolynomiallyBounded p` by `fun_prop`, if it can. -/
private def polynomiallyBoundedByFunProp? (p : Expr) : MetaM (Option Expr) := do
  let hp ← mkFreshExprMVar (mkApp (mkConst ``Cslib.PolynomiallyBounded) p)
  try
    let gs ← (Tactic.run hp.mvarId! do evalTactic (← `(tactic| fun_prop))).run'
    unless gs.isEmpty do return none
    return some (← instantiateMVars hp)
  catch _ => return none

/-- `n` applied to `pf` as its first explicit argument, with metavariables for the arguments
before it; the remaining arguments stay for `MVarId.apply`. -/
private def applyTo (n : Name) (pf : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels n
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType c)
  let some i := binders.findIdx? (·.isExplicit) |
    throwError "growth_poly: {n} has no explicit argument"
  unless ← isDefEq (← inferType args[i]!) (← inferType pf) do
    throwError "growth_poly: {pf} does not fit {n}"
  args[i]!.mvarId!.assign pf
  return mkAppN c args[:i + 1]

/-- Expose tuple components `fun a => (?g₁ a, ?g₂ a)` when `β` is a `Prod`, so higher-order
unification can solve `v (g a) =?= u a` when `v` projects `g a` via `.1`/`.2`. -/
private partial def prepareProdArg (α β : Expr) : MetaM Expr := do
  let β' ← whnfR β
  if β'.isAppOfArity ``Prod 2 then
    let g₁ ← prepareProdArg α (β'.getArg! 0)
    let g₂ ← prepareProdArg α (β'.getArg! 1)
    withLocalDeclD `a α fun a => do
      mkLambdaFVars #[a] (← mkAppM ``Prod.mk #[mkApp g₁ a, mkApp g₂ a])
  else
    mkFreshExprMVar (← mkArrow α β)

/-- Reduce a single-alternative matcher on a `Prod` discriminant `s` to its body applied to
`s.1` and `s.2` (definitionally equal by `Prod` eta). -/
private def reduceProdMatch? (body : Expr) : MetaM (Option Expr) := do
  let some m ← matchMatcherApp? body | return none
  unless m.discrs.size == 1 && m.alts.size == 1 && m.remaining.isEmpty do return none
  let s := m.discrs[0]!
  let sTy ← whnfR (← inferType s)
  unless sTy.isAppOfArity ``Prod 2 do return none
  let .const _ [u₁, u₂] := sTy.getAppFn | return none
  let (α₁, α₂) := (sTy.getArg! 0, sTy.getArg! 1)
  let pair := mkApp4 (mkConst ``Prod.mk [u₁, u₂]) α₁ α₂
    (mkApp3 (mkConst ``Prod.fst [u₁, u₂]) α₁ α₂ s)
    (mkApp3 (mkConst ``Prod.snd [u₁, u₂]) α₁ α₂ s)
  let .reduced res ← reduceMatcher? { m with discrs := #[pair] }.toExpr | return none
  return some res.headBeta

/-- Try applying `PolyBounded.comp` to `pf : PolyBounded size' v` using map `g : α → β` for
`goalTy = PolyBounded size u`, rejecting self-reductions and unresolved metavariables. -/
private def tryCompWith? (pf goalTy α β size size' v g : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let comp ← mkAppOptM ``Turing.MultiTapeTM.PolyBounded.comp
      #[some α, some β, some size, some size', some v, some g, some pf]
    let .forallE _ subTy concl _ ← whnfR (← inferType comp) | do saved.restore; return none
    let conclRed := reduceProdProj (← Core.betaReduce concl)
    unless ← withReducible (isDefEq conclRed goalTy) do
      saved.restore; return none
    let g' ← instantiateMVars g
    if g'.hasExprMVar then
      saved.restore; return none
    let subTy' ← instantiateMVars subTy
    if ← withReducible (isDefEq subTy' goalTy) then
      saved.restore; return none
    return some (← instantiateMVars comp)
  catch _ =>
    saved.restore
    return none

/-- Try applying `PolyBounded.comp` to `pf : PolyBounded size' v` for `goalTy = PolyBounded size u`,
trying a single metavariable `g : α → β` first (matching `origin/main` so un-expanded `Prod`
projections and nested `Prod` abbreviations unify directly) and falling back to tuple component
splitting via `prepareProdArg` when needed. -/
private def tryComp? (pf goalTy α size : Expr) : MetaM (Option Expr) := do
  let pfTy ← whnfR (← inferType pf)
  let some (size', v) := polyBoundedArgs? pfTy | return none
  let β := pfTy.getArg! 0
  let gPlain ← mkFreshExprMVar (← mkArrow α β)
  if let some comp ← tryCompWith? pf goalTy α β size size' v gPlain then
    return some comp
  let βWhnf ← whnfR β
  unless βWhnf.isAppOfArity ``Prod 2 do return none
  let gProd ← prepareProdArg α βWhnf
  tryCompWith? pf goalTy α β size size' v gProd

/-- Drop an `id` at the head of `e`. -/
private def stripId (e : Expr) : Expr :=
  if e.isAppOfArity ``id 2 then e.appArg! else e

/-- Is `pf` a proof of `goalTy` up to reducible unfolding? -/
private def provesReducible (pf goalTy : Expr) : MetaM Bool := do
  withReducible <| withNewMCtxDepth <| isDefEq (← inferType pf) goalTy

/-- Unfold one non-internal head definition or non-class structure projection of `e`, followed by
local `let` and beta reduction. -/
private def unfoldStepOnce? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFn with
  | .proj .. =>
    let some f ← reduceProj? e.getAppFn | return none
    some <$> zetaHead (f.beta e.getAppArgs)
  | .const c _ =>
    let cPub := (privateToUserName? c).getD c
    if cPub.isInternal || c == ``List.length || c == ``DFunLike.coe then return none
    if let some info ← getProjectionFnInfo? c then
      if info.fromClass then return none
      let some e' ← unfoldDefinition? e | return none
      if let some f ← reduceProj? e'.getAppFn then
        return some (← zetaHead (f.beta e'.getAppArgs))
      return none
    let some e' ← unfoldDefinition? e | return none
    some <$> zetaHead e'
  | _ => return none

/-- Does `body` match a direct decomposition or leaf step of `chooseStep`? -/
private def stepHeadRecognized (facts : Facts) (goalTy size a body : Expr) : MetaM Bool := do
  let dependsOnInput (e : Expr) := e.containsFVar a.fvarId!
  if !dependsOnInput body then return true
  if ← withReducible (isDefEq body (stripId (size.beta #[a]).headBeta)) then return true
  if body.isAppOfArity ``Nat.succ 1 || body.isAppOfArity ``Min.min 4 then return true
  if let some rule := coreOpRule? body then
    if rule != ``Turing.MultiTapeTM.PolyBounded.pow || !dependsOnInput (body.getArg! 5) then
      return true
  if (condRule? body).isSome then return true
  if (← nondepDiteToIte? body).isSome then return true
  if (← powSplit? facts a body).isSome then return true
  let candGoal := mkAppN goalTy.getAppFn #[goalTy.getArg! 0, size, ← mkLambdaFVars #[a] body]
  if (← findClosureRule? candGoal body).isSome then return true
  if (← findPointwiseBound? facts body).isSome then return true
  if (← encLengthBound? body).isSome then return true
  facts.bounds.anyM fun (pf, _) => provesReducible pf candGoal

/-- Unfold definitions and structure projections at the head of `body` for at most `fuel` steps
until a directly recognized `growth_poly` step or leaf appears. -/
private partial def unfoldToRecognized? (facts : Facts) (goalTy size a body : Expr)
    (fuel : Nat := 6) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let some body' ← unfoldStepOnce? body | return none
  if ← stepHeadRecognized facts goalTy size a body' then
    return some body'
  unfoldToRecognized? facts goalTy size a body' (fuel - 1)

/-- Choose the next step for the goal `goalTy`, which is `PolyBounded size u`, or throw an error
naming the term that no rule bounds. -/
private def chooseStep (facts : Facts) (goalTy size u : Expr) : MetaM Step := do
  for (pf, _) in facts.bounds do
    if ← provesReducible pf goalTy then return .close pf
  let .forallE _ α _ _ ← whnfR (← inferType u) |
    throwError "growth_poly: {u} is not a function"
  withLocalDeclD `a α fun a => do
    let body₀ := (u.beta #[a]).headBeta
    let body ← zetaHead (← reduceComp body₀)
    let body ← match ← reduceProdMatch? body with
      | some body' => zetaHead (← reduceComp body')
      | none => pure body
    if body != body₀ then return .change (← mkLambdaFVars #[a] body)
    let dependsOnInput (e : Expr) := e.containsFVar a.fvarId!
    if !dependsOnInput body then return .apply ``Turing.MultiTapeTM.PolyBounded.const
    let sizeVal := stripId (size.beta #[a]).headBeta
    if ← withReducible (isDefEq body sizeVal) then
      return .apply ``Turing.MultiTapeTM.PolyBounded.self
    if !facts.polys.isEmpty && (← inferType sizeVal).isConstOf ``Nat then
      for (pf, p) in facts.polys do
        if ← withReducible <| withNewMCtxDepth <| isDefEq body ((p.beta #[sizeVal]).headBeta) then
          let cand ← mkAppOptM ``Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded
            #[some α, some size, some p, some pf]
          return .close (← mkExpectedTypeHint cand goalTy)
    let fail : MetaM Step := do
      let unused := facts.unused.toList.map fun (pf, l) =>
        m!"\nThe certificate `{pf}` gives no bound: `{l.name}` is not imported. \
          Import `{l.module}`."
      throwError "growth_poly: no rule or local fact bounds{indentExpr body}\n\
        by a polynomial in{indentExpr (size.beta #[a]).headBeta}\n\
        Add a `PolyBounded` fact or a certificate for it to the context, or pass one as \
        `growth_poly [h]`.{MessageData.joinSep unused ""}"
    let mkMono (rhs hleBody : Expr) : MetaM Step := do
      let u' ← mkLambdaFVars #[a] rhs
      let hle ← mkLambdaFVars #[a] hleBody
      let expectedLe ← mkForallFVars #[a] (← mkAppM ``LE.le #[mkApp u a, mkApp u' a])
      return .mono u' (← mkExpectedTypeHint hle expectedLe)
    if body.isAppOfArity ``Nat.succ 1 then
      return .change (← mkLambdaFVars #[a] (mkNatAdd body.appArg! (mkNatLit 1)))
    if body.isAppOfArity ``Min.min 4 then
      return .applyFirst ``Turing.MultiTapeTM.PolyBounded.min_left
        ``Turing.MultiTapeTM.PolyBounded.min_right
    let isVarPow := body.isAppOfArity ``HPow.hPow 6 && dependsOnInput (body.getArg! 5)
    if let some rule := coreOpRule? body then
      if !isVarPow then
        return .apply rule
    if let some rule := condRule? body then
      return .apply rule
    if let some iteExpr ← nondepDiteToIte? body then
      return .change (← mkLambdaFVars #[a] iteExpr)
    -- Pointwise `ℕ` inequalities/equations from context, hints, or `@[growth_poly]`.
    if let some (rhs, hleBody) ← findPointwiseBound? facts body then
      return ← mkMono rhs hleBody
    if isVarPow then
      if let some (rhs, hleBody) ← powSplit? facts a body then
        return ← mkMono rhs hleBody
    -- Registered `@[growth_poly]` closure rules.
    if let some rule ← findClosureRule? goalTy body then
      trace[growth_poly] "closure rule {.ofConstName rule}: {body}"
      return .apply rule
    -- Built-in encoding length bounds (`encPair`, `encUnary`, `encBool`, `encBits`, `encNat`, and
    -- `enc_structure` encodings).
    if let some (rhs, hleBody) ← encLengthBound? body then
      return ← mkMono rhs hleBody
    let natFunApp ← pure body.isApp <&&> pure !(dependsOnInput body.appFn!) <&&>
      isNatFun body.appFn!
    -- A polynomially bounded function of one natural number, known from the context.
    if natFunApp then
      for (pf, p) in facts.polys do
        if ← withReducible <| withNewMCtxDepth <| isDefEq body.appFn! p then
          return .applyTo ``Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp pf
    -- A bounded function applied to a function of the input (skipping self-reduction).
    for (pf, allowComp) in facts.bounds do
      unless allowComp do continue
      if let some comp ← tryComp? pf goalTy α size then
        return .applyProof comp
    -- Multi-step definition and structure-projection unfolding to a recognized step or leaf.
    if let some body' ← unfoldToRecognized? facts goalTy size a body then
      return .change (← mkLambdaFVars #[a] body')
    -- A polynomially bounded function of one natural number, by `fun_prop`.
    if natFunApp then
      if let some hp ← polynomiallyBoundedByFunProp? body.appFn! then
        return .applyTo ``Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded_comp hp
    fail

/-- Prove the `PolyBounded` goal `g` from `facts`, within `fuel` steps. -/
private partial def prove (facts : Facts) (g : MVarId) (fuel : Nat) : MetaM Unit :=
  g.withContext do
  if fuel == 0 then
    throwError "growth_poly: step limit reached at{indentExpr (← g.getType)}"
  let goalTy ← whnfR (← instantiateMVars (← g.getType))
  let some (size, u) := polyBoundedArgs? goalTy |
    throwError "growth_poly: expected a `PolyBounded` goal, got{indentExpr goalTy}"
  let applyRule (rule : Expr) : MetaM Unit := do
    let gs ← g.apply rule
    for g' in gs do
      unless ← g'.isAssigned do
        let ty ← whnfR (← instantiateMVars (← g'.getType))
        if (polyBoundedArgs? ty).isSome then
          prove facts g' (fuel - 1)
        else if ← isProp ty then
          try g'.assumption catch _ => pure ()
    for g' in gs do
      unless ← g'.isAssigned do
        throwError "growth_poly: could not determine{indentExpr (← g'.getType)}"
  match ← chooseStep facts goalTy size u with
  | .close pf => g.assign pf
  | .change u' =>
    let g' ← g.replaceTargetDefEq (mkAppN goalTy.getAppFn #[goalTy.getArg! 0, size, u'])
    prove facts g' (fuel - 1)
  | .mono u' hle =>
    let g' ← mkFreshExprMVar (mkAppN goalTy.getAppFn #[goalTy.getArg! 0, size, u'])
    g.assign (← mkAppM ``Turing.MultiTapeTM.PolyBounded.mono #[g', hle])
    prove facts g'.mvarId! (fuel - 1)
  | .apply rule => applyRule (← mkConstWithFreshMVarLevels rule)
  | .applyTo rule pf => applyRule (← applyTo rule pf)
  | .applyProof rulePf => applyRule rulePf
  | .applyFirst first second =>
    let saved ← saveState
    try
      applyRule (← mkConstWithFreshMVarLevels first)
    catch _ =>
      saved.restore
      applyRule (← mkConstWithFreshMVarLevels second)

elab_rules : tactic
  | `(tactic| growth_poly $[[$hints,*]]?) => focus do
    let goal ← getMainGoal
    let goalTy ← whnfR (← instantiateMVars (← goal.getType))
    if goalTy.isAppOfArity ``Cslib.PolynomiallyBounded 1 then
      evalTactic (← `(tactic| fun_prop))
      return
    goal.withContext do
      let some (size, _) := polyBoundedArgs? goalTy |
        throwError "growth_poly: expected a `PolyBounded` goal, got{indentExpr goalTy}"
      let hints ← ((hints.map (·.getElems)).getD #[]).mapM fun h => elabTerm h none
      prove (← collectFacts (goalTy.getArg! 0) size hints) goal 256
    replaceMainGoal []

end Cslib.Tactic.GrowthPoly

end
