/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.WramOmega.Init
public meta import Lean.Elab.Tactic.Omega

/-!
# Strided product, division, and power-of-two arithmetic for Word-RAM proofs

`omega` treats nonlinear products `a * s`, variable-divisor quotients/remainders `a / s` and
`a % s`, and powers `2 ^ e` as opaque atoms. Word-RAM developments constantly discharge local
nonlinear inequalities from the linear facts already in context:

* **2D / strided bounds** across a shared factor `s`: from `a < b`, deduce `a * s + s ≤ b * s`
  (covering both `a * s` and `s * a`), and from `a ≤ b`, deduce `a * s ≤ b * s`.
* **Strided injectivity / distinctness** across a shared factor `s`: when Phase 1 (non-branching)
  does not close the goal, add the three-way trichotomy on `(a, b)` for unordered pairs sharing a
  factor `s`, allowing `omega` to prove `a * s + r = b * s + r' → a = b ∧ r = r'` and
  `a * s + r ≠ b * s + r'` whenever `r < s` and `r' < s`.
* **Monotone powers of two `2 ^ e`** (and same-exponent powers `a ^ k`): for every `2 ^ e`, add
  `0 < 2 ^ e` and `e < 2 ^ e`; for pairs `(2 ^ e₁, 2 ^ e₂)`, compare `e₁` vs `e₂` linearly
  (including product facts just derived) and add `2 * 2 ^ e₁ ≤ 2 ^ e₂`, `2 ^ e₁ ≤ 2 ^ e₂`, or
  `2 ^ e₁ = 2 ^ e₂`.
* **Variable-divisor `div`/`mod` bounds**: `s * (a / s) + a % s = a`, `a / s ≤ a`, `a % s ≤ a`,
  `0 < s → a % s < s`, `(a * s + r) / s = a` and `(a * s + r) % s = r` when `r < s`,
  and monotonicity / comparison bridges `a / s < m ↔ a < m * s` and `m ≤ a / s ↔ m * s ≤ a`.

All candidate pairs are drawn strictly from the syntactic atoms present in the goal and arithmetic
hypotheses, with hard caps on atom/probe count and tight per-probe heartbeat budgets to avoid
quadratic blowups on large contexts. The tactic first tries unfolding `@[wram_arith]` definitions as
in `wram_omega`.

## Main definitions

* `stride_omega`: close a `ℕ`/`ℤ` arithmetic goal using linear arithmetic augmented with bounded
  strided-product, `div`/`mod`, and monotone `2 ^ k` preprocessing.
* `Cslib.Tactic.StrideOmega.prove?`: silent `MetaM` entry point returning `Option Expr` (no linter
  warnings, bounded heartbeats), used by `update_simp`.
-/

public section

namespace Cslib.Tactic.StrideOmega

/-- Step bound `a * s + s ≤ b * s` from `a < b`. -/
protected theorem mul_add_le_of_lt {a b s : ℕ} (h : a < b) : a * s + s ≤ b * s := by
  have h1 := Nat.mul_le_mul_right s h
  rwa [Nat.succ_mul] at h1

/-- Three-way step comparison for right-aligned products `a * s` and `b * s`. -/
protected theorem mul_trichotomy (a b s : ℕ) :
    (a < b ∧ a * s + s ≤ b * s) ∨ (a = b ∧ a * s = b * s) ∨ (b < a ∧ b * s + s ≤ a * s) := by
  rcases Nat.lt_trichotomy a b with h | rfl | h
  · exact Or.inl ⟨h, StrideOmega.mul_add_le_of_lt h⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨h, StrideOmega.mul_add_le_of_lt h⟩)

/-- Tight doubling bound `2 * 2 ^ e₁ ≤ 2 ^ e₂` from `e₁ < e₂`. -/
protected theorem two_mul_pow_le_of_lt {e₁ e₂ : ℕ} (h : e₁ < e₂) : 2 * 2 ^ e₁ ≤ 2 ^ e₂ := by
  have h1 : 2 ^ (e₁ + 1) ≤ 2 ^ e₂ := Nat.pow_le_pow_right (by decide) h
  rwa [Nat.pow_succ, Nat.mul_comm] at h1

/-- Three-way order comparison for `2 ^ e₁` and `2 ^ e₂`. -/
protected theorem two_pow_trichotomy (e₁ e₂ : ℕ) :
    (e₁ < e₂ ∧ 2 * 2 ^ e₁ ≤ 2 ^ e₂) ∨ (e₁ = e₂ ∧ 2 ^ e₁ = 2 ^ e₂) ∨
      (e₂ < e₁ ∧ 2 * 2 ^ e₂ ≤ 2 ^ e₁) := by
  rcases Nat.lt_trichotomy e₁ e₂ with h | rfl | h
  · exact Or.inl ⟨h, StrideOmega.two_mul_pow_le_of_lt h⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨h, StrideOmega.two_mul_pow_le_of_lt h⟩)

end Cslib.Tactic.StrideOmega

end

public meta section

namespace Cslib.Tactic.StrideOmega

open Lean Meta Elab Tactic
open Cslib.Tactic.WramOmega (Kind wramArithExt isPowerOfTwo)

/-- Maximum distinct syntactic product occurrences inspected per shared factor. -/
private def maxPerFactor : Nat := 8

/-- Maximum distinct shared factors processed. -/
private def maxFactors : Nat := 12

/-- Maximum distinct `2 ^ e` atoms collected. -/
private def maxPow2 : Nat := 24

/-- Maximum distinct same-exponent `a ^ k` atoms collected. -/
private def maxPowOther : Nat := 10

/-- Maximum distinct `a / s` or `a % s` atoms collected. -/
private def maxDivMod : Nat := 16

/-- Maximum `omega` probe calls per preprocessing category (`div`, `mul`, `pow2`). -/
private def maxProbes : Nat := 32

/-- Maximum trichotomy facts added in the branching fallback phase. -/
private def maxTrichotomies : Nat := 4

/-- Internal heartbeat limit (`1000` per option unit) for each side-condition probe. -/
private def probeMaxHeartbeats : Nat := 2_500_000

/-- Whether `omega` reads numbers of type `α`. -/
private def isNumberType (α : Expr) : Bool :=
  α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1

/-- Whether a hypothesis type is arithmetic (`ℕ`/`ℤ`/`Fin` comparisons, boolean connectives,
or `@[wram_arith]` predicates). -/
private partial def isArithmetic (tagged : NameMap Kind) (type : Expr) : Bool :=
  match_expr type with
  | Eq α _ _ => isNumberType α
  | Ne α _ _ => isNumberType α
  | LE.le α _ _ _ => isNumberType α
  | LT.lt α _ _ _ => isNumberType α
  | GE.ge α _ _ _ => isNumberType α
  | GT.gt α _ _ _ => isNumberType α
  | Dvd.dvd α _ _ _ => isNumberType α
  | Not p => isArithmetic tagged p
  | And p q => isArithmetic tagged p || isArithmetic tagged q
  | Or p q => isArithmetic tagged p || isArithmetic tagged q
  | Iff p q => isArithmetic tagged p || isArithmetic tagged q
  | _ =>
    match type with
    | .forallE _ p q _ =>
      !q.hasLooseBVars && (isArithmetic tagged p || isArithmetic tagged q)
    | .mdata _ b => isArithmetic tagged b
    | _ =>
      match type.getAppFn with
      | .const name _ => tagged.find? name == some .predicate
      | _ => false

/-- Whether `e` is a reducible alias of an arithmetic proposition. -/
private def readByOmega (tagged : NameMap Kind) (type : Expr) : MetaM Bool := do
  if isArithmetic tagged type then return true
  let .const name _ := type.getAppFn | return false
  unless ← isReducible name do return false
  return isArithmetic tagged (← whnfR type)

/-- Unfold reducible head definitions safely under binders. -/
private partial def unfoldReducibleHead (e : Expr) : MetaM Expr := do
  let .const name us := e.getAppFn | return e
  unless ← isReducible name do return e
  let info ← getConstInfo name
  unless info.hasValue && info.levelParams.length == us.length do return e
  unfoldReducibleHead ((← instantiateValueLevelParams info us).betaRev e.getAppRevArgs)

/-- Reduce a structure projection applied to a constructor (e.g. from unfolded `@[wram_arith]`). -/
private def reduceField? (t : Expr) : MetaM (Option Expr) := do
  let .const name _ := t.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  if info.fromClass then return none
  let args := t.getAppArgs
  let some struct := args[info.numParams]? | return none
  let some field ← projectCore? (← unfoldReducibleHead struct) info.i | return none
  return some (mkAppN field (args.extract (info.numParams + 1) args.size))

/-- Check if `e` mentions a definition in `defs` or a local binding in `locals`. -/
private def mentionsAny (defs : NameSet) (locals : FVarIdSet) (e : Expr) : Bool :=
  e.getUsedConstants.any defs.contains ||
    (!locals.isEmpty && e.hasAnyFVar locals.contains)

/-- Unfold tagged `@[wram_arith]` definitions, extra user-specified defs, and local definitions,
returning the transformed expression and whether anything changed. -/
private def unfoldDefs (defs : NameSet) (locals : FVarIdSet) (e : Expr) :
    MetaM (Expr × Bool) := do
  let changed ← IO.mkRef false
  let e ← Core.transform e
    (post := fun t => do
      let some t' ← reduceField? t | return .continue
      changed.set true
      return .visit t')
    (pre := fun t => do
      match t.getAppFn with
      | .fvar fvarId =>
        if locals.contains fvarId then
          if let some value ← fvarId.getValue? then
            changed.set true
            return .visit ((← instantiateMVars value).betaRev t.getAppRevArgs)
        return .continue
      | .const name us =>
        unless defs.contains name do return .continue
        let info ← getConstInfo name
        unless info.hasValue && info.levelParams.length == us.length do return .continue
        changed.set true
        let value ← instantiateValueLevelParams info us
        return .visit (value.betaRev t.getAppRevArgs (useZeta := true))
      | _ => return .continue)
  if (e.find? (·.isLet)).isSome then
    changed.set true
    return (← zetaReduce e (zetaDelta := false), true)
  return (e, ← changed.get)

/-- Match a `Nat` literal `OfNat.ofNat Nat n _` or `Nat.lit`. -/
private def isNatLit (e : Expr) : Bool :=
  e.nat?.isSome

/-- Match `Nat` addition `a + b`. -/
private def matchNatAdd? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | HAdd.hAdd α β γ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then some (a, b) else none
  | Nat.add a b => some (a, b)
  | _ => none

/-- Match `Nat` multiplication `a * b`. -/
private def matchNatMul? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | HMul.hMul α β γ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then some (a, b) else none
  | Nat.mul a b => some (a, b)
  | _ => none

/-- Match `Nat` division `a / b`. -/
private def matchNatDiv? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | HDiv.hDiv α β γ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then some (a, b) else none
  | Nat.div a b => some (a, b)
  | _ => none

/-- Match `Nat` modulo `a % b`. -/
private def matchNatMod? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | HMod.hMod α β γ _ a b =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then some (a, b) else none
  | Nat.mod a b => some (a, b)
  | _ => none

/-- Match `Nat` exponentiation `b ^ k`. -/
private def matchNatPow? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | HPow.hPow α β γ _ b k =>
    if α.isConstOf ``Nat && β.isConstOf ``Nat && γ.isConstOf ``Nat then some (b, k) else none
  | Nat.pow b k => some (b, k)
  | _ => none

/-- Match `Fin.val x` where `x : Fin n`. -/
private def matchFinVal? (e : Expr) : Option Expr :=
  match_expr e with
  | Fin.val _ x => some x
  | _ => none

/-- A `Nat` product indexed relative to a candidate shared factor `factor`. If `onRight` is `true`,
the original term is `coeff * factor`; otherwise `factor * coeff`. -/
private structure MulOcc where
  orig : Expr
  coeff : Expr
  onRight : Bool

private instance : Inhabited MulOcc :=
  ⟨{ orig := default, coeff := default, onRight := false }⟩

/-- Syntactic atoms extracted from the goal and arithmetic hypotheses. -/
private structure Atoms where
  /-- Products `(e, a, b)` where not both factors are numerals. -/
  muls : Array (Expr × Expr × Expr) := #[]
  /-- Exponents `e` for `2 ^ e` terms. -/
  pow2s : Array Expr := #[]
  /-- Other `(b, k)` pairs for `b ^ k` (`b ≠ 2`, non-literal `b`). -/
  powOthers : Array (Expr × Expr) := #[]
  /-- Variable-divisor divisions `(a, s)` where `s` is not a literal numeral. -/
  divs : Array (Expr × Expr) := #[]
  /-- Variable-divisor remainders `(a, s)` where `s` is not a literal numeral. -/
  mods : Array (Expr × Expr) := #[]
  /-- `x : Fin n` values occurring inside `Fin.val x`. -/
  fins : Array Expr := #[]
  /-- Standalone expressions compared with `a / s`. -/
  divCmps : Array (Expr × Expr × Expr) := #[]

private def pushUniq (arr : Array Expr) (x : Expr) : Array Expr :=
  if arr.contains x then arr else arr.push x

private def pushUniq2 (arr : Array (Expr × Expr)) (p : Expr × Expr) : Array (Expr × Expr) :=
  if arr.any (fun q => q.1 == p.1 && q.2 == p.2) then arr else arr.push p

private def pushUniq3 (arr : Array (Expr × Expr × Expr)) (p : Expr × Expr × Expr) :
    Array (Expr × Expr × Expr) :=
  if arr.any (fun q => q.1 == p.1 && q.2.1 == p.2.1 && q.2.2 == p.2.2) then arr else arr.push p

/-- Walk `es` in order (`es[0]` visited first so target atoms precede background hypotheses),
collecting closed product, power, div, mod, and `Fin.val` subterms. -/
private def collectAtoms (es : Array Expr) : Atoms := Id.run do
  let mut st : Atoms := {}
  let mut seen : Std.HashSet Expr := {}
  let mut work : Array Expr := es.reverse
  while !work.isEmpty do
    let e := work.back!
    work := work.pop
    if e.hasLooseBVars || seen.contains e then continue
    seen := seen.insert e
    if let some (a, b) := matchNatMul? e then
      if !(isNatLit a && isNatLit b) then
        if st.muls.size < 40 then
          st := { st with muls := pushUniq3 st.muls (e, a, b) }
    else if isPowerOfTwo e then
      if st.pow2s.size < maxPow2 then
        let k := e.appArg!
        if !k.hasLooseBVars then
          st := { st with pow2s := pushUniq st.pow2s k }
    else if let some (b, k) := matchNatPow? e then
      if b.nat? != some 2 && !isNatLit b && st.powOthers.size < maxPowOther then
        st := { st with powOthers := pushUniq2 st.powOthers (b, k) }
    else if let some (a, s) := matchNatDiv? e then
      if !isNatLit s && st.divs.size < maxDivMod then
        st := { st with divs := pushUniq2 st.divs (a, s) }
    else if let some (a, s) := matchNatMod? e then
      if !isNatLit s && st.mods.size < maxDivMod then
        st := { st with mods := pushUniq2 st.mods (a, s) }
    else if let some x := matchFinVal? e then
      if !x.hasLooseBVars && st.fins.size < 32 then
        st := { st with fins := pushUniq st.fins x }
    -- Detect comparisons like `a / s < m` or `m ≤ a / s` for `Nat.div_lt_iff_lt_mul`.
    if e.isAppOfArity ``LT.lt 4 then
      let args := e.getAppArgs
      if args[0]!.isConstOf ``Nat then
        if let some (a, s) := matchNatDiv? args[2]! then
          if !isNatLit s && st.divCmps.size < maxDivMod then
            st := { st with divCmps := pushUniq3 st.divCmps (a, s, args[3]!) }
        if let some (a, s) := matchNatDiv? args[3]! then
          if !isNatLit s && st.divCmps.size < maxDivMod then
            st := { st with divCmps := pushUniq3 st.divCmps (a, s, args[2]!) }
    else if e.isAppOfArity ``LE.le 4 then
      let args := e.getAppArgs
      if args[0]!.isConstOf ``Nat then
        if let some (a, s) := matchNatDiv? args[3]! then
          if !isNatLit s && st.divCmps.size < maxDivMod then
            st := { st with divCmps := pushUniq3 st.divCmps (a, s, args[2]!) }
    match e with
    | .app f a =>
      if !a.hasLooseBVars then work := work.push a
      if !f.hasLooseBVars then work := work.push f
    | .lam _ _ b _ =>
      if !b.hasLooseBVars then work := work.push b
    | .forallE _ d b _ =>
      if !d.hasLooseBVars then work := work.push d
      if !b.hasLooseBVars then work := work.push b
    | .letE _ _ v b _ =>
      if !v.hasLooseBVars then work := work.push v
      if !b.hasLooseBVars then work := work.push b
    | .mdata _ b =>
      if !b.hasLooseBVars then work := work.push b
    | .proj _ _ b =>
      if !b.hasLooseBVars then work := work.push b
    | _ => pure ()
  return st

/-- Make a `Nat` `<` expression `a < b`. -/
private def mkNatLt (a b : Expr) : MetaM Expr :=
  mkAppM ``LT.lt #[a, b]

/-- Make a `Nat` `≤` expression `a ≤ b`. -/
private def mkNatLe (a b : Expr) : MetaM Expr :=
  mkAppM ``LE.le #[a, b]

/-- Ground proof of `0 < (2 : ℕ)`. -/
private def mkTwoPos : MetaM Expr := do
  mkDecideProof (← mkNatLt (mkNatLit 0) (mkNatLit 2))

/-- Build `congrArg (· * s) h` for `h : a = b` on `ℕ`. -/
private def mkMulCongrLeft (s h : Expr) : MetaM Expr := do
  let f ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HMul.hMul #[x, s])
  mkCongrArg f h

/-- Build `congrArg (· / s) h` for `h : a = b` on `ℕ`. -/
private def mkDivCongrLeft (s h : Expr) : MetaM Expr := do
  let f ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HDiv.hDiv #[x, s])
  mkCongrArg f h

/-- Build `congrArg (· % s) h` for `h : a = b` on `ℕ`. -/
private def mkModCongrLeft (s h : Expr) : MetaM Expr := do
  let f ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HMod.hMod #[x, s])
  mkCongrArg f h

/-- Close `g` using `Omega.omega` with explicit `hyps`, wrapped in `mkAuxTheorem` (optional
heartbeat cap). Returns `none` on success, `some ex` on failure. -/
private def omegaClose? (g : MVarId) (hyps : Array Expr) (heartbeatCap? : Option Nat := none) :
    MetaM (Option Exception) := do
  let saved ← saveState
  let run : MetaM (Option Exception) := do
    let some g ← g.falseOrByContra | return none
    g.withContext do
      let type ← g.getType
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      let some neg := (← getLCtx).lastDecl | throwError "stride_omega: missing negated goal"
      let allHyps := (hyps.push neg.toExpr).toList
      Omega.omega allHyps proof.mvarId!
      g.assign (← mkAuxTheorem type (← instantiateMVars proof) (zetaDelta := true))
    return none
  tryCatchRuntimeEx
    (match heartbeatCap? with
     | some cap =>
       withCurrHeartbeats <|
         withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := cap }) run
     | none => run)
    (fun ex => do
      saved.restore
      return some ex)

/-- Try to prove `prop : Prop` using `Omega.omega` from `baseHyps` under a strict heartbeat cap. -/
private def probeLinear? (baseHyps : Array Expr) (prop : Expr)
    (probes : IO.Ref Nat) : MetaM (Option Expr) := do
  if (← probes.get) ≥ maxProbes then return none
  probes.modify (· + 1)
  let saved ← saveState
  let attempt : MetaM (Option Expr) := do
    let m ← mkFreshExprSyntheticOpaqueMVar prop
    let some g ← m.mvarId!.falseOrByContra | return some (← instantiateMVars m)
    g.withContext do
      let some neg := (← getLCtx).lastDecl | throwError "stride_omega: missing negated goal"
      let type ← g.getType
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      Omega.omega (baseHyps.push neg.toExpr).toList proof.mvarId!
      g.assign (← instantiateMVars proof)
    return some (← instantiateMVars m)
  tryCatchRuntimeEx
    (withCurrHeartbeats <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := probeMaxHeartbeats })
        attempt)
    (fun _ => do
      saved.restore
      return none)

/-- Direct lookup for `prop` in precomputed `(expr, type)` pairs before running `omega`. -/
private def findDirect? (hypsWithType : Array (Expr × Expr)) (prop : Expr) : Option Expr :=
  (hypsWithType.find? fun (_, t) => t == prop).map (·.1)

/-- Cheap literal / direct-hypothesis check before invoking `omega`. -/
private def probeLt? (baseHyps : Array Expr) (hypTypes : Array (Expr × Expr))
    (a b : Expr) (probes : IO.Ref Nat) : MetaM (Option Expr) := do
  if a == b then return none
  if let (some m, some n) := (a.nat?, b.nat?) then
    if m < n then
      return some (← mkDecideProof (← mkNatLt a b))
    else
      return none
  let p ← mkNatLt a b
  if let some h := findDirect? hypTypes p then return some h
  probeLinear? baseHyps p probes

private def probeLe? (baseHyps : Array Expr) (hypTypes : Array (Expr × Expr))
    (a b : Expr) (probes : IO.Ref Nat) : MetaM (Option Expr) := do
  if a == b then
    return some (← mkAppM ``Nat.le_refl #[a])
  if let (some m, some n) := (a.nat?, b.nat?) then
    if m ≤ n then
      return some (← mkDecideProof (← mkNatLe a b))
    else
      return none
  let p ← mkNatLe a b
  if let some h := findDirect? hypTypes p then return some h
  probeLinear? baseHyps p probes

private def probeEq? (baseHyps : Array Expr) (hypTypes : Array (Expr × Expr))
    (a b : Expr) (probes : IO.Ref Nat) : MetaM (Option Expr) := do
  if a == b then return some (← mkEqRefl a)
  if let (some m, some n) := (a.nat?, b.nat?) then
    if m == n then return some (← mkEqRefl a) else return none
  let p ← mkEq a b
  if let some h := findDirect? hypTypes p then return some h
  probeLinear? baseHyps p probes

/-- Safe proof-term builder wrapper that suppresses type mismatch exceptions. -/
private def tryMkProof (build : MetaM Expr) : MetaM (Option Expr) := do
  try
    return some (← build)
  catch _ =>
    return none

/-- Group products by shared non-literal factor `s`, storing how each occurrence appears. -/
private def groupByFactor (muls : Array (Expr × Expr × Expr)) :
    Array (Expr × Array MulOcc) := Id.run do
  let mut groups : Array (Expr × Array MulOcc) := #[]
  let addOcc (gs : Array (Expr × Array MulOcc)) (factor : Expr) (occ : MulOcc) :
      Array (Expr × Array MulOcc) :=
    if isNatLit factor then gs
    else
      match gs.findIdx? (fun g => g.1 == factor) with
      | some idx =>
        let (f, occs) := gs[idx]!
        let already := occs.any (fun o => o.orig == occ.orig && o.onRight == occ.onRight)
        if occs.size ≥ maxPerFactor || already then
          gs
        else
          gs.set! idx (f, occs.push occ)
      | none =>
        if gs.size ≥ maxFactors then gs else gs.push (factor, #[occ])
  for (orig, a, b) in muls do
    groups := addOcc groups b { orig, coeff := a, onRight := true }
    if a != b then
      groups := addOcc groups a { orig, coeff := b, onRight := false }
  return groups

/-- Build `(expr, type)` lookup table for fast syntactic hypothesis matching before `omega`. -/
private def annotateTypes (hyps : Array Expr) : MetaM (Array (Expr × Expr)) :=
  hyps.mapM fun h => do return (h, ← instantiateMVars (← inferType h))

/-- Add Euclidean quotient and remainder identities when `a` has the form `q * s + r`, `s * q + r`,
`r + q * s`, or `r + s * q` with `hr : r < s`. -/
private def pushEuclideanDivMod (facts : Array Expr) (q s r hr : Expr)
    (mulOnRight sumLeft : Bool) : MetaM (Array Expr) := do
  let pushFact (fs : Array Expr) (p? : Option Expr) : Array Expr :=
    match p? with | some p => fs.push p | none => fs
  let mut fs := facts
  let hs ← mkAppOptM ``Nat.zero_lt_of_lt #[some r, some s, some hr]
  fs := pushFact fs (← tryMkProof (mkAppOptM ``Nat.div_eq_of_lt #[some r, some s, some hr]))
  fs := pushFact fs (← tryMkProof (mkAppOptM ``Nat.mod_eq_of_lt #[some r, some s, some hr]))
  match sumLeft, mulOnRight with
  | false, true =>
    -- `r + q * s`
    fs := pushFact fs
      (← tryMkProof (mkAppOptM ``Nat.add_mul_div_right #[some r, some q, some s, some hs]))
    fs := pushFact fs (← tryMkProof (mkAppM ``Nat.add_mul_mod_self_right #[r, q, s]))
  | false, false =>
    -- `r + s * q`
    fs := pushFact fs
      (← tryMkProof (mkAppOptM ``Nat.add_mul_div_left #[some r, some q, some s, some hs]))
    fs := pushFact fs (← tryMkProof (mkAppM ``Nat.add_mul_mod_self_left #[r, s, q]))
  | true, false =>
    -- `s * q + r`
    fs := pushFact fs
      (← tryMkProof (mkAppOptM ``Nat.mul_add_div #[some s, some hs, some q, some r]))
    fs := pushFact fs (← tryMkProof (mkAppM ``Nat.mul_add_mod #[s, q, r]))
  | true, true =>
    -- `q * s + r`: commute sum to `r + q * s`
    let qMulS ← mkAppM ``HMul.hMul #[q, s]
    let hcomm ← mkAppM ``Nat.add_comm #[qMulS, r]
    fs := pushFact fs (← tryMkProof (mkDivCongrLeft s hcomm))
    fs := pushFact fs (← tryMkProof (mkModCongrLeft s hcomm))
    fs := pushFact fs
      (← tryMkProof (mkAppOptM ``Nat.add_mul_div_right #[some r, some q, some s, some hs]))
    fs := pushFact fs (← tryMkProof (mkAppM ``Nat.add_mul_mod_self_right #[r, q, s]))
  return fs

/-- Generate Phase-1 (non-branching) nonlinear facts and candidate Phase-2 trichotomies from
collected syntactic atoms. When `goalOnly` is `true`, only pairs involving at least one atom
from `goalAtoms` are probed (dramatically reducing heartbeat cost on huge contexts). -/
private def buildNonlinearFacts (atoms goalAtoms : Atoms) (seedHyps : Array Expr)
    (goalOnly : Bool := false) : MetaM (Array Expr × Array Expr) := do
  let divProbes ← IO.mkRef 0
  let mulProbes ← IO.mkRef 0
  let powProbesRef ← IO.mkRef 0
  let mut facts : Array Expr := #[]
  let mut mulBranch : Array Expr := #[]
  let mut powBranch : Array Expr := #[]
  let pushFact (fs : Array Expr) (p? : Option Expr) : Array Expr :=
    match p? with | some p => fs.push p | none => fs
  let inGoalMul (e : Expr) : Bool := goalAtoms.muls.any (fun p => p.1 == e)
  let inGoalPow2 (e : Expr) : Bool := goalAtoms.pow2s.contains e
  -- 0. `Fin.isLt` for every `x : Fin n` inside `Fin.val x`
  for x in atoms.fins do
    facts := pushFact facts (← tryMkProof (mkAppM ``Fin.isLt #[x]))
  -- 1. Baseline `2 ^ e` positivity (`0 < 2 ^ e`) and `e < 2 ^ e` (`Nat.lt_two_pow_self`)
  for e in atoms.pow2s do
    facts := pushFact facts (← tryMkProof (pure (mkApp (mkConst ``Nat.two_pow_pos) e)))
    facts := pushFact facts (← tryMkProof (mkAppOptM ``Nat.lt_two_pow_self #[some e]))
  -- 1b. Factor positivity `0 < l * r → 0 < l ∧ 0 < r` when `l` or `r` is a divisor in `divs`/`mods`
  let initForPos := seedHyps ++ facts
  let initTypes ← annotateTypes initForPos
  let isDivisor (s : Expr) : Bool :=
    atoms.divs.any (·.2 == s) || atoms.mods.any (·.2 == s) || atoms.divCmps.any (·.2.1 == s)
  for (orig, l, r) in atoms.muls do
    if isDivisor l || isDivisor r then
      if let some hmulPos ← probeLt? initForPos initTypes (mkNatLit 0) orig divProbes then
        if isDivisor r then
          facts := pushFact facts
            (← tryMkProof (mkAppOptM ``Nat.pos_of_mul_pos_left #[some l, some r, some hmulPos]))
        if isDivisor l then
          facts := pushFact facts
            (← tryMkProof (mkAppOptM ``Nat.pos_of_mul_pos_right #[some l, some r, some hmulPos]))
  let baseForProbes := seedHyps ++ facts
  let baseTypes ← annotateTypes baseForProbes
  -- 2. Div/Mod basic bounds (`s * (a / s) + a % s = a`, `a / s ≤ a`, `a % s ≤ a`, `a % s < s`,
  --    `(q * s + r) / s = q`, `(q * s + r) % s = r`)
  let mut seenDivMod : Array (Expr × Expr) := #[]
  for (a, s) in atoms.divs ++ atoms.mods do
    if seenDivMod.any (fun p => p.1 == a && p.2 == s) then continue
    seenDivMod := seenDivMod.push (a, s)
    facts := pushFact facts (← tryMkProof (mkAppM ``Nat.div_add_mod #[a, s]))
    facts := pushFact facts (← tryMkProof (mkAppM ``Nat.div_le_self #[a, s]))
    facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mod_le #[a, s]))
    if let some hpos ← probeLt? baseForProbes baseTypes (mkNatLit 0) s divProbes then
      facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mod_lt #[a, hpos]))
    -- Match Euclidean form `q * s + r`, `s * q + r`, `r + q * s`, `r + s * q`
    if let some (l, r) := matchNatAdd? a then
      if let some (q, s') := matchNatMul? l then
        if s' == s then
          if let some hr ← probeLt? baseForProbes baseTypes r s divProbes then
            facts ← pushEuclideanDivMod facts q s r hr (mulOnRight := true) (sumLeft := true)
        else if q == s then
          if let some hr ← probeLt? baseForProbes baseTypes r s divProbes then
            facts ← pushEuclideanDivMod facts s' s r hr (mulOnRight := false) (sumLeft := true)
      if let some (q, s') := matchNatMul? r then
        if s' == s then
          if let some hl ← probeLt? baseForProbes baseTypes l s divProbes then
            facts ← pushEuclideanDivMod facts q s l hl (mulOnRight := true) (sumLeft := false)
        else if q == s then
          if let some hl ← probeLt? baseForProbes baseTypes l s divProbes then
            facts ← pushEuclideanDivMod facts s' s l hl (mulOnRight := false) (sumLeft := false)
  -- Quotient monotonicity `a / s ≤ b / s` for shared `s`
  for i in [:atoms.divs.size] do
    let (a₁, s₁) := atoms.divs[i]!
    for j in [i + 1 : atoms.divs.size] do
      let (a₂, s₂) := atoms.divs[j]!
      if s₁ == s₂ then
        if let some h ← probeLe? baseForProbes baseTypes a₁ a₂ divProbes then
          facts := pushFact facts
            (← tryMkProof (mkAppOptM ``Nat.div_le_div_right #[some a₁, some a₂, some s₁, some h]))
        else if let some h ← probeLe? baseForProbes baseTypes a₂ a₁ divProbes then
          facts := pushFact facts
            (← tryMkProof (mkAppOptM ``Nat.div_le_div_right #[some a₂, some a₁, some s₁, some h]))
  -- Bridge `a / s < m ↔ a < m * s` / `m ≤ a / s ↔ m * s ≤ a` for comparisons in goal/hyps
  for (a, s, m) in atoms.divCmps do
    if let some hpos ← probeLt? baseForProbes baseTypes (mkNatLit 0) s divProbes then
      facts := pushFact facts
        (← tryMkProof (mkAppOptM ``Nat.div_lt_iff_lt_mul #[some s, some a, some m, some hpos]))
      facts := pushFact facts
        (← tryMkProof (mkAppOptM ``Nat.le_div_iff_mul_le #[some s, some m, some a, some hpos]))
      let mSucc ← mkAppM ``HAdd.hAdd #[m, mkNatLit 1]
      facts := pushFact facts
        (← tryMkProof (mkAppOptM ``Nat.le_div_iff_mul_le #[some s, some mSucc, some a, some hpos]))
      facts := pushFact facts (← tryMkProof (mkAppM ``Nat.add_one_mul #[m, s]))
      facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_comm #[m, s]))
  -- 3. Single-product simplifications: `(a + b) * s`, and for goal products `≤ 1`/`> 0`
  let singleProbes ← IO.mkRef 0
  for (orig, l, r) in atoms.muls do
    if !isNatLit r then
      if let some (x, y) := matchNatAdd? l then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.add_mul #[x, y, r]))
    if !isNatLit l then
      if let some (x, y) := matchNatAdd? r then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_add #[l, x, y]))
    if inGoalMul orig && !isNatLit r && !isNatLit l then
      if let some hle1 ← probeLe? baseForProbes baseTypes l (mkNatLit 1) singleProbes then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_le_mul_right #[r, hle1]))
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.one_mul #[r]))
      if let some hpos ← probeLt? baseForProbes baseTypes (mkNatLit 0) l singleProbes then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.le_mul_of_pos_left #[r, hpos]))
      if let some hle1 ← probeLe? baseForProbes baseTypes r (mkNatLit 1) singleProbes then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_le_mul_left #[l, hle1]))
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_one #[l]))
      if let some hpos ← probeLt? baseForProbes baseTypes (mkNatLit 0) r singleProbes then
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.le_mul_of_pos_right #[l, hpos]))
  -- 4. Pairwise strided bounds for products sharing a non-literal factor `s`
  let groups := groupByFactor atoms.muls
  for (s, occs) in groups do
    for i in [:occs.size] do
      let o₁ := occs[i]!
      for j in [i + 1 : occs.size] do
        let o₂ := occs[j]!
        if o₁.orig == o₂.orig then continue
        if goalOnly && !(inGoalMul o₁.orig || inGoalMul o₂.orig) then continue
        let a := o₁.coeff
        let b := o₂.coeff
        if !o₁.onRight then
          facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_comm #[s, a]))
        if !o₂.onRight then
          facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_comm #[s, b]))
        if a == b then continue
        let mut ordered := false
        if let some h ← probeLt? baseForProbes baseTypes a b mulProbes then
          ordered := true
          facts := pushFact facts
            (← tryMkProof
              (mkAppOptM ``StrideOmega.mul_add_le_of_lt #[some a, some b, some s, some h]))
        else if let some h ← probeLt? baseForProbes baseTypes b a mulProbes then
          ordered := true
          facts := pushFact facts
            (← tryMkProof
              (mkAppOptM ``StrideOmega.mul_add_le_of_lt #[some b, some a, some s, some h]))
        else if let some h ← probeEq? baseForProbes baseTypes a b mulProbes then
          ordered := true
          facts := pushFact facts (← tryMkProof (mkMulCongrLeft s h))
        else if let some h ← probeLe? baseForProbes baseTypes a b mulProbes then
          ordered := true
          facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_le_mul_right #[s, h]))
        else if let some h ← probeLe? baseForProbes baseTypes b a mulProbes then
          ordered := true
          facts := pushFact facts (← tryMkProof (mkAppM ``Nat.mul_le_mul_right #[s, h]))
        if !ordered && mulBranch.size < maxTrichotomies && !isNatLit a && !isNatLit b then
          mulBranch := pushFact mulBranch
            (← tryMkProof (mkAppM ``StrideOmega.mul_trichotomy #[a, b, s]))
  -- 5. Monotone `2 ^ e` (independent probe budget; fed product bounds derived above)
  let powSeed := seedHyps ++ facts
  let powTypes ← annotateTypes powSeed
  let twoPos ← mkTwoPos
  for e in atoms.pow2s do
    if inGoalPow2 e || !goalOnly then
      if let some hpos ← probeLt? powSeed powTypes (mkNatLit 0) e powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``Nat.pow_le_pow_right #[twoPos, hpos]))
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.pow_one #[mkNatLit 2]))
      if let some hle1 ← probeLe? powSeed powTypes e (mkNatLit 1) powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``Nat.pow_le_pow_right #[twoPos, hle1]))
        facts := pushFact facts (← tryMkProof (mkAppM ``Nat.pow_one #[mkNatLit 2]))
  for i in [:atoms.pow2s.size] do
    let e₁ := atoms.pow2s[i]!
    for j in [i + 1 : atoms.pow2s.size] do
      let e₂ := atoms.pow2s[j]!
      if e₁ == e₂ then continue
      if goalOnly && !(inGoalPow2 e₁ || inGoalPow2 e₂) then continue
      if let some h ← probeLt? powSeed powTypes e₁ e₂ powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``StrideOmega.two_mul_pow_le_of_lt #[h]))
      else if let some h ← probeLt? powSeed powTypes e₂ e₁ powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``StrideOmega.two_mul_pow_le_of_lt #[h]))
      else if let some h ← probeLe? powSeed powTypes e₁ e₂ powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``Nat.pow_le_pow_right #[twoPos, h]))
      else if let some h ← probeLe? powSeed powTypes e₂ e₁ powProbesRef then
        facts := pushFact facts
          (← tryMkProof (mkAppM ``Nat.pow_le_pow_right #[twoPos, h]))
      else if !goalOnly && powBranch.size < 2 then
        powBranch := pushFact powBranch
          (← tryMkProof (mkAppM ``StrideOmega.two_pow_trichotomy #[e₁, e₂]))
  -- 6. Monotone same-exponent powers `b₁ ^ k ≤ b₂ ^ k`
  for i in [:atoms.powOthers.size] do
    let (b₁, k₁) := atoms.powOthers[i]!
    for j in [i + 1 : atoms.powOthers.size] do
      let (b₂, k₂) := atoms.powOthers[j]!
      if k₁ == k₂ && b₁ != b₂ then
        if let some h ← probeLe? powSeed powTypes b₁ b₂ powProbesRef then
          facts := pushFact facts
            (← tryMkProof (mkAppM ``Nat.pow_le_pow_left #[h, k₁]))
        else if let some h ← probeLe? powSeed powTypes b₂ b₁ powProbesRef then
          facts := pushFact facts
            (← tryMkProof (mkAppM ``Nat.pow_le_pow_left #[h, k₁]))
  return (facts, mulBranch ++ powBranch)

/-- Compute active arithmetic hypotheses and local definitions in context. -/
private def collectContextArith (tagged : NameMap Kind) (defs : NameSet)
    (unfoldLocals : Bool) : MetaM (Array Expr × Array Expr × Bool) := do
  let mut locals : FVarIdSet := {}
  if unfoldLocals then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if d.value?.isSome then locals := locals.insert d.fvarId
  let mut hyps : Array Expr := #[]
  let mut types : Array Expr := #[]
  let mut anyUnfolded := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let type ← instantiateMVars d.type
    unless ← readByOmega tagged type do continue
    if mentionsAny defs locals type then
      let (uType, ch) ← unfoldDefs defs locals type
      if ch then anyUnfolded := true
      hyps := hyps.push (← mkExpectedTypeHint d.toExpr uType)
      types := types.push uType
    else
      hyps := hyps.push d.toExpr
      types := types.push type
  return (hyps, types, anyUnfolded)

/-- Core solver: attempt to close `g` using `stride_omega`.
`extraTerms` are additional proof terms passed in `[h₁, h₂]`.
`extraDefs` are extra constant names to unfold alongside `@[wram_arith]`.
When `heartbeatCap?` is set, caps the internal `omega` calls (for speculative callers like
`update_simp`). Returns `none` on success or an error message on failure. -/
def runOnGoal (g : MVarId) (extraTerms : Array Expr := #[]) (extraDefs : NameSet := {})
    (heartbeatCap? : Option Nat := none) (allowBroad : Bool := true) :
    MetaM (Option Exception) := g.withContext do
  let tagged := wramArithExt.getState (← getEnv)
  let mut defs : NameSet := extraDefs
  for (n, _) in tagged do
    defs := defs.insert n
  let origTarget ← instantiateMVars (← g.getType)
  let mut rawArithHyps : Array Expr := #[]
  let mut rawTypes : Array Expr := #[origTarget]
  for h in extraTerms do
    let t ← instantiateMVars (← inferType h)
    rawArithHyps := rawArithHyps.push h
    rawTypes := rawTypes.push t
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if ← readByOmega tagged t then
      rawArithHyps := rawArithHyps.push d.toExpr
      rawTypes := rawTypes.push t
  let tryTarget (tgt : Expr) (hyps : Array Expr) : MetaM (Option Exception) := do
    let saved ← saveState
    let m ← mkFreshExprSyntheticOpaqueMVar tgt
    match ← omegaClose? m.mvarId! hyps heartbeatCap? with
    | none =>
      g.assign (← mkExpectedTypeHint (← instantiateMVars m) origTarget)
      return none
    | some ex =>
      saved.restore
      return some ex
  -- Pass 0: plain `omega` as-is (fastest possible case; zero nonlinear work).
  if (← tryTarget origTarget rawArithHyps).isNone then
    return none
  -- Unfold `@[wram_arith]` + `extraDefs` + local `let` bindings into target, hints, and arith hyps.
  let mut allLocals : FVarIdSet := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.value?.isSome then allLocals := allLocals.insert d.fvarId
  let (uTarget, tCh) ← unfoldDefs defs allLocals origTarget
  let mut uHints : Array Expr := #[]
  let mut uHintTypes : Array Expr := #[]
  for h in extraTerms do
    let t ← instantiateMVars (← inferType h)
    let (ut, _) ← unfoldDefs defs allLocals t
    uHints := uHints.push (← mkExpectedTypeHint h ut)
    uHintTypes := uHintTypes.push ut
  let (uCtxHyps, uCtxTypes, hCh) ← collectContextArith tagged defs (unfoldLocals := true)
  let hasUnfolded := tCh || hCh || !extraDefs.isEmpty
  -- Pass 1 (unfolded `omega` alone, including `2 ^ e` positivity, like `wram_omega`).
  let uHyps := uHints ++ uCtxHyps
  let uTypes := #[uTarget] ++ uHintTypes ++ uCtxTypes
  let uAtoms := collectAtoms uTypes
  if hasUnfolded then
    let mut basicFacts : Array Expr := #[]
    for e in uAtoms.pow2s do
      basicFacts := basicFacts.push (mkApp (mkConst ``Nat.two_pow_pos) e)
    if (← tryTarget uTarget (uHyps ++ basicFacts)).isNone then
      return none
  -- Pass 2a: fast goal-anchored nonlinear facts (avoids quadratic probes on huge contexts).
  let tgt := if hasUnfolded then uTarget else origTarget
  let goalAtoms := collectAtoms (#[tgt] ++ uHintTypes)
  let (fastFacts, fastBr) ← buildNonlinearFacts uAtoms goalAtoms uHyps (goalOnly := true)
  if !fastFacts.isEmpty then
    if (← tryTarget tgt (uHyps ++ fastFacts)).isNone then
      return none
  if !fastBr.isEmpty then
    if (← tryTarget tgt (uHyps ++ fastFacts ++ fastBr)).isNone then
      return none
  -- Pass 2b: broader nonlinear facts across context pairs (transitive bridges).
  -- Skipped on oversized speculative contexts (`!allowBroad && uAtoms.muls.size > 16`).
  if allowBroad || uAtoms.muls.size ≤ 16 then
    let (nlFacts, brFacts) ← buildNonlinearFacts uAtoms goalAtoms uHyps (goalOnly := false)
    if !nlFacts.isEmpty then
      if (← tryTarget tgt (uHyps ++ nlFacts)).isNone then
        return none
    if !brFacts.isEmpty then
      if (← tryTarget tgt (uHyps ++ nlFacts ++ brFacts)).isNone then
        return none
  -- Fallback: folded atoms (preserves folded `@[wram_arith]` definitions, e.g. variable divisors).
  if hasUnfolded && (allowBroad || rawTypes.size ≤ 20) then
    let rAtoms := collectAtoms rawTypes
    let rGoalAtoms := collectAtoms #[origTarget]
    let (rNl, rBr) ← buildNonlinearFacts rAtoms rGoalAtoms rawArithHyps (goalOnly := false)
    if !rNl.isEmpty then
      if (← tryTarget origTarget (rawArithHyps ++ rNl)).isNone then
        return none
    if !rBr.isEmpty then
      if (← tryTarget origTarget (rawArithHyps ++ rNl ++ rBr)).isNone then
        return none
  -- Final failing call for an informative diagnostic message.
  let some ex ← tryTarget (if hasUnfolded then uTarget else origTarget) uHyps | return none
  return some ex

/-- Silent `MetaM` prover for arithmetic goals, used by `update_simp`. Does not emit linter
warnings and bounds every internal `omega` run by `heartbeatCap`. -/
def prove? (target : Expr) (extraDefs : NameSet := {})
    (extraHyps : Array Expr := #[]) (heartbeatCap : Nat := 15_000_000) :
    MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let saved ← saveState
  let attempt : MetaM (Option Expr) := do
    let m ← mkFreshExprSyntheticOpaqueMVar target
    match ← runOnGoal m.mvarId! extraHyps extraDefs
        (some heartbeatCap) (allowBroad := false) with
    | none => return some (← instantiateMVars m)
    | some _ =>
      saved.restore
      return none
  tryCatchRuntimeEx attempt fun _ => do
    saved.restore
    return none

/-- Prove an arithmetic goal by linear arithmetic augmented with bounded nonlinear preprocessing:
unfolds `@[wram_arith]` definitions and local bindings (like `wram_omega`), derives monotone
strided-product facts `a * s + s ≤ b * s` / `a * s ≤ b * s` / `mul_trichotomy` across shared
factors `s`, variable-divisor `div`/`mod` identities, and monotone `2 ^ e` / `a ^ k` bounds
strictly from syntactic atoms present in the goal and arithmetic hypotheses.

Optional `[h₁, h₂]` supplies extra hypothesis terms (like `wram_omega [h₁, h₂]`). -/
syntax (name := strideOmega) "stride_omega" (" [" term,* "]")? : tactic

@[inherit_doc strideOmega]
elab_rules : tactic
  | `(tactic| stride_omega $[[$args,*]]?) => do
    recordExtraModUse (isMeta := false) `Init.Omega
    recordExtraModUse (isMeta := false) `CslibFrontier.Tactic.StrideOmega
    let terms ← ((args.map (·.getElems)).getD #[]).mapM fun t =>
      withMainContext <| elabTerm t none
    liftMetaFinishingTactic fun g => do
      match ← runOnGoal g terms with
      | none => return
      | some ex =>
        throwError "stride_omega: could not close goal with `omega` after strided-product, \
          `div`/`mod`, and `2 ^ k` preprocessing.\n{ex.toMessageData}"

end Cslib.Tactic.StrideOmega

end
