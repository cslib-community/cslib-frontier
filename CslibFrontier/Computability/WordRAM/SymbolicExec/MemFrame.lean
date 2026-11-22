/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.RegisterFrame
public import CslibFrontier.Computability.WordRAM.SymbolicExec
public import CslibFrontier.Tactic.WramOmega
public import Mathlib.Data.Set.Function
public meta import Lean.Elab.Tactic.Omega

/-!
# Memory facts across calls

A proof about a word-RAM program carries memory invariants and cell values across calls: each
subprogram specification gives a result state `y` together with either a whole-memory equation
`y.mem = x.mem`, a *frame* `∀ a, P₁ a → … → y.mem a = x.mem a`, a `Set.EqOn y.mem x.mem R`, a
`Modifies writes x.mem y.mem`, or a store-free execution `Exec w c x y n` / `ExecWithin w c x y T`.
Writing frame chains by hand repeats arithmetic disjointness proofs (`by wram_omega`) and manual
`.trans` pipelines across intermediate states.

This file provides `Code.StoreFree` (kernel-decidable store-freeness giving `Exec.mem_eq` and
`ExecWithin.mem_eq`) and `mem_frame`, the memory-framing twin of `regs_frame`
(`CslibFrontier/Computability/WordRAM/SymbolicExec/Frame.lean`).

## Main definitions

* `Cslib.WordRAM.Op.StoreFree`, `Cslib.WordRAM.Code.StoreFree`: decidable predicates stating that
  an instruction or structured program contains no `Op.store`.
* `mem_frame`: the tactic proving whole-memory equations `z.mem = x.mem`, pointwise reads
  `z.mem a = v` / `z.mem a = x.mem a`, quantified frames `∀ a, P a → z.mem a = x.mem a`,
  `Set.EqOn`, `Modifies`, conjunctions, and `Prop`-valued structures (plus user-selected unfolded
  `Prop` definitions via `mem_frame [TableRep, ...]`).

## Main results

* `Cslib.WordRAM.Exec.mem_eq`, `Cslib.WordRAM.ExecWithin.mem_eq`: executions of store-free
  programs preserve memory identically.
* `Cslib.WordRAM.Op.storeFree_rename`, `Cslib.WordRAM.Code.storeFree_rename`: register renaming
  preserves store-freeness.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

/-! ## Store-free programs -/

/-- Whether a data instruction does not write to memory (is not `Op.store`). -/
def Op.StoreFree : Op B r → Prop
  | .store _ _ => False
  | _ => True

/-- Decidability of whether a data instruction is store-free. -/
instance Op.decidableStoreFree : (o : Op B r) → Decidable o.StoreFree
  | .const _ _ | .copy _ _ | .alu _ _ _ | .load _ _ => isTrue trivial
  | .store _ _ => isFalse id

/-- A binary operation instruction is store-free. -/
@[simp]
theorem Op.storeFree_bin (f : BinOp) (d i j : Fin r) : (Op.bin f d i j).StoreFree := trivial

/-- Reading the word width is store-free. -/
@[simp]
theorem Op.storeFree_width (d : Fin r) : (Op.width d).StoreFree := trivial

/-- An exact binary operation instruction is store-free. -/
@[simp]
theorem Op.storeFree_exactBin (f : BinOp) (d i j : Fin r) : (Op.exactBin f d i j).StoreFree :=
  trivial

/-- Reading the word width over `Basis.exact` is store-free. -/
@[simp]
theorem Op.storeFree_exactWidth (d : Fin r) : (Op.exactWidth d).StoreFree := trivial

/-- Register renaming preserves store-freeness of a data instruction. -/
@[simp]
theorem Op.storeFree_rename (f : Fin r → Fin r') (o : Op B r) :
    (o.rename f).StoreFree ↔ o.StoreFree := by
  cases o <;> rfl

/-- A structured program is *store-free* when no instruction inside it is `Op.store`. -/
def Code.StoreFree : Code B r → Prop
  | .op o => o.StoreFree
  | .seq c₁ c₂ => c₁.StoreFree ∧ c₂.StoreFree
  | .branch _ pos neg => pos.StoreFree ∧ neg.StoreFree
  | .loop _ body => body.StoreFree
  | .rand _ _ => True

/-- Decidability of whether a structured program is store-free. -/
instance Code.decidableStoreFree : (c : Code B r) → Decidable c.StoreFree
  | .op o => o.decidableStoreFree
  | .seq c₁ c₂ =>
    have := c₁.decidableStoreFree
    have := c₂.decidableStoreFree
    inferInstanceAs (Decidable (_ ∧ _))
  | .branch _ pos neg =>
    have := pos.decidableStoreFree
    have := neg.decidableStoreFree
    inferInstanceAs (Decidable (_ ∧ _))
  | .loop _ body => body.decidableStoreFree
  | .rand _ _ => isTrue trivial

/-- Register renaming preserves store-freeness of a structured program. -/
@[simp]
theorem Code.storeFree_rename (f : Fin r → Fin r') (c : Code B r) :
    (c.rename f).StoreFree ↔ c.StoreFree := by
  induction c with
  | op o => exact Op.storeFree_rename f o
  | seq _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | branch _ _ _ ihp ihn => exact and_congr ihp ihn
  | loop _ _ ih => exact ih
  | rand _ _ => rfl

/-- A renamed store-free program is store-free. -/
theorem Code.StoreFree.rename {f : Fin r → Fin r'} {c : Code B r} (h : c.StoreFree) :
    (c.rename f).StoreFree :=
  (Code.storeFree_rename f c).2 h

private theorem Op.mem_eq {w : ℕ} {o : Op B r} {x y : Data r} (ho : o.StoreFree)
    (h : o.eval w x = some y) : y.mem = x.mem := by
  cases o with
  | const =>
    obtain ⟨-, rfl⟩ := Data.put_eq_some.1 h
    rfl
  | copy | load => cases h; rfl
  | alu =>
    obtain ⟨_, -, -, rfl⟩ := Op.eval_alu_eq_some.1 h
    rfl
  | store => exact ho.elim

/-- **Memory preservation.** A store-free structured program leaves memory unchanged. -/
theorem Exec.mem_eq {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ}
    (h : Exec w c x y n) (hc : c.StoreFree) : y.mem = x.mem := by
  induction h with
  | op ho => exact Op.mem_eq hc ho
  | seq _ _ ih₁ ih₂ => exact (ih₂ hc.2).trans (ih₁ hc.1)
  | branch_pos _ _ ih => exact ih hc.1
  | branch_neg _ _ ih => exact ih hc.2
  | loop_exit _ => rfl
  | loop_iter _ _ _ ihb ihl => exact (ihl hc).trans (ihb hc)

/-- Any store-free structured program leaves memory unchanged across a bounded execution. -/
theorem ExecWithin.mem_eq {w T : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecWithin w c x y T) (hc : c.StoreFree) : y.mem = x.mem :=
  let ⟨_, _, he⟩ := h
  he.mem_eq hc

end Cslib.WordRAM

end

public section

namespace Cslib.WordRAM

namespace MemFrame

open Lean Meta Elab Tactic

/-- A memory map (`ℕ → ℕ`) equality `m₁ = m₂`. -/
private meta structure WholeEq where
  /-- The proof of `lhs = rhs`. -/
  proof : Expr
  /-- The target memory map `rhs`. -/
  rhs : Expr
  /-- Whether this edge is oriented in its hypothesis direction (`false` means reversed `.symm`). -/
  forward : Bool
  /-- How error messages name the equality. -/
  name : MessageData

/-- A pointwise memory frame: `∀ xs, m' a = m a`, or a `Set.EqOn` / `Modifies` frame. -/
private meta structure Frame where
  /-- The proof term of the frame. -/
  proof : Expr
  /-- The type of `proof`, of the form `∀ xs, m' pat = m pat`. -/
  type : Expr
  /-- How error messages name the frame. -/
  name : MessageData

/-- An execution hypothesis `he : J ...` providing a lazy whole-memory frame via `J.mem_eq`. -/
private meta structure ExecFrame where
  /-- The proof function `hc ↦ J.mem_eq he hc` (or direct proof if no premise). -/
  proof : Expr
  /-- Its type, e.g. `c.StoreFree → y.mem = x.mem` or `y.mem = x.mem`. -/
  type : Expr
  /-- How error messages name the frame. -/
  name : MessageData

/-- A concrete cell equation `m a = v`. -/
private meta structure CellVal where
  /-- The address `a : ℕ`. -/
  addr : Expr
  /-- The value `v : ℕ`. -/
  val : Expr
  /-- The proof of `m addr = val`. -/
  proof : Expr
  /-- How error messages name the fact. -/
  name : MessageData

/-- A universally quantified slice value equation `∀ xs, m addrExpr = valExpr`. -/
private meta structure SliceVal where
  /-- The proof term. -/
  proof : Expr
  /-- Its type `∀ xs, m addrExpr = valExpr`. -/
  type : Expr
  /-- How error messages name the fact. -/
  name : MessageData

/-- Collected memory facts in a local context. -/
private meta structure Facts where
  /-- Whole-memory equalities `m' = m`, keyed by canonical `m'`. -/
  wholeEqs : Std.HashMap Expr (Array WholeEq) := {}
  /-- Lazy execution-based whole-memory frames (`J.mem_eq`), keyed by canonical `y.mem`. -/
  execFrames : Std.HashMap Expr (Array ExecFrame) := {}
  /-- Pointwise frames `∀ xs, m' pat = m pat`, keyed by canonical `m'`. -/
  frames : Std.HashMap Expr (Array Frame) := {}
  /-- Polymorphic / parametric frames from user hints `mem_frame [...]`. -/
  patternFrames : Array Frame := #[]
  /-- Concrete cell values `m a = v`, keyed by canonical `m`. -/
  cellVals : Std.HashMap Expr (Array CellVal) := {}
  /-- Quantified slice value equations `∀ xs, m addrExpr = valExpr`, keyed by canonical `m`. -/
  sliceVals : Std.HashMap Expr (Array SliceVal) := {}
  /-- All bare memory maps (`ℕ → ℕ`) that appear in collected facts. -/
  knownMems : Std.HashSet Expr := {}
  /-- Constant names to unfold during fact/goal decomposition and state stepping. -/
  unfoldDefs : NameSet := {}
  /-- Extra hint proof expressions (used when discharging arithmetic bounds). -/
  arithHints : Array Expr := #[]

/-- Mutable caches scoped to a single local context (per subgoal). -/
private meta structure Cache where
  /-- Cached `discharge` results: `p ↦ some proof` or `none` (failed). -/
  disch : Std.HashMap Expr (Option Expr) := {}
  /-- Cached `proveStoreFree?` results for code terms `c`. -/
  storeFree : Std.HashMap Expr (Option Expr) := {}
  /-- Extra arithmetic note proofs extracted from the current local context
  (e.g. `a ∉ b.footprint` → `¬(b.base ≤ a ∧ a < b.base + b.length)`). -/
  derivedArith : Array Expr := #[]
  /-- Reads/memories where search could not advance, for diagnostics. -/
  stuck : Array (Expr × Array (MessageData × Expr)) := #[]

/-- Whether `ty` is syntactically `ℕ → ℕ` (up to reducible unfolding / metadata). -/
private meta def isMemType (ty : Expr) : MetaM Bool := do
  let ty := ty.cleanupAnnotations
  if let .forallE _ d b _ := ty then
    if !b.hasLooseBVars && d.isConstOf ``Nat && b.isConstOf ``Nat then
      return true
  let ty' ← whnfR ty
  if let .forallE _ d b _ := ty' then
    return !b.hasLooseBVars && d.isConstOf ``Nat && b.isConstOf ``Nat
  return false

/-- Normalize `Prod.fst` / `Prod.snd` applications and `.proj` nodes to canonical form,
reducing `(a, b).1 ↦ a` and `(a, b).2 ↦ b`. Every step is definitionally equal (`rfl`). -/
private meta partial def normData (d : Expr) : Expr :=
  let d := d.cleanupAnnotations.headBeta
  if d.isAppOfArity ``Prod.fst 3 then
    let p := d.getArg! 2 |>.cleanupAnnotations.headBeta
    if p.isAppOfArity ``Prod.mk 4 then normData (p.getArg! 2)
    else .proj ``Prod 0 p
  else if d.isAppOfArity ``Prod.snd 3 then
    let p := d.getArg! 2 |>.cleanupAnnotations.headBeta
    if p.isAppOfArity ``Prod.mk 4 then normData (p.getArg! 3)
    else .proj ``Prod 1 p
  else match d with
  | .proj ``Prod 0 p =>
    let p := p.cleanupAnnotations.headBeta
    if p.isAppOfArity ``Prod.mk 4 then normData (p.getArg! 2) else .proj ``Prod 0 p
  | .proj ``Prod 1 p =>
    let p := p.cleanupAnnotations.headBeta
    if p.isAppOfArity ``Prod.mk 4 then normData (p.getArg! 3) else .proj ``Prod 1 p
  | _ => d

/-- Strip `rfl`-equivalent memory wrappers from a memory expression `m : ℕ → ℕ`:
`(x.set i v).mem ↦ x.mem`, `(x.comap f).mem ↦ x.mem`, `(y.extend f x).mem ↦ y.mem`,
and normalize `Prod.fst` / `Prod.snd` projections. Every step is definitionally equal (`rfl`). -/
private meta partial def stripMemWrappers (m : Expr) : Expr :=
  let m := m.cleanupAnnotations.headBeta
  match_expr m with
  | Data.mem r d =>
    let d' := normData d
    match_expr d' with
    | Data.set _ x _ _ => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r x)
    | Data.comap _ r' _ x => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r' x)
    | Data.extend r₀ _ _ y _ => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r₀ y)
    | _ => mkApp2 (mkConst ``Data.mem) r d'
  | _ =>
    match m with
    | .proj ``Data 1 d =>
      let d' := normData d
      match_expr d' with
      | Data.set r x _ _ => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r x)
      | Data.comap _ r' _ x => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r' x)
      | Data.extend r₀ _ _ y _ => stripMemWrappers (mkApp2 (mkConst ``Data.mem) r₀ y)
      | _ => .proj ``Data 1 d'
    | _ => m

/-- Canonical lookup key for a memory expression `m : ℕ → ℕ`. Strips `rfl`-equivalent
wrappers and erases `r` in `Data.mem r d` so `Data.mem rLP x` and `Data.mem 24 x` share one
key (`r` is uniquely fixed by `d`'s type). -/
private meta def memKey (m : Expr) : Expr :=
  let m' := stripMemWrappers m.cleanupAnnotations
  match_expr m' with
  | Data.mem _ d => mkApp2 (mkConst ``Data.mem) (mkRawNatLit 0) d
  | _ =>
    match m' with
    | .proj ``Data 1 d => mkApp2 (mkConst ``Data.mem) (mkRawNatLit 0) d
    | _ => m'

/-- Canonicalize the head of a memory expression `m`, unfolding no `let` bindings yet. -/
private meta def canonMem (m : Expr) : Expr :=
  stripMemWrappers m.cleanupAnnotations

/-- Recognize a `Data.mem r s`, `.proj ``Data 1 s`, or `Function.update ...` term. -/
private meta def isIntrinsicMem (m : Expr) : Bool :=
  let m := m.cleanupAnnotations
  m.isAppOfArity ``Data.mem 2 ||
    (match m with | .proj ``Data 1 _ => true | _ => false) ||
    (m.isAppOfArity ``Function.update 6 && (m.getArg! 0).isConstOf ``Nat)

/-- Whether `m` is recognized as a memory map (`Data.mem`, `Function.update`, or tracked in `F`). -/
private meta def isTrackedMem (F : Facts) (m : Expr) : Bool :=
  let m' := canonMem m
  isIntrinsicMem m' || F.knownMems.contains (memKey m) ||
    F.knownMems.contains m.cleanupAnnotations

/-- Split an explicit/known memory read `e = m a` into `(m, a)`.
When `onlyTracked` is true, `m` must be `Data.mem`, `Function.update`, or in `F.knownMems`. -/
private meta def readMem? (F : Facts) (e : Expr) (onlyTracked : Bool := true) :
    Option (Expr × Expr) := do
  let e := e.cleanupAnnotations
  let .app m a := e | none
  if !onlyTracked || isTrackedMem F m then
    return (m, a)
  else
    none

/-- Step `(x.havoc c v mem).mem = mem` when `SymbolicExec.Havoc` is in the environment. -/
private meta def stepHavocMem? (m : Expr) : MetaM (Option (Expr × Expr)) := do
  unless (← getEnv).contains `Cslib.WordRAM.Data.havoc_mem do return none
  let d? : Option Expr := match_expr m.cleanupAnnotations with
    | Data.mem _ d => some d
    | _ => match m.cleanupAnnotations with | .proj ``Data 1 d => some d | _ => none
  let some d := d? | return none
  let d := d.cleanupAnnotations
  unless d.isAppOfArity `Cslib.WordRAM.Data.havoc 6 do return none
  let args := d.getAppArgs
  let pf := mkAppN (mkConst `Cslib.WordRAM.Data.havoc_mem)
    #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!]
  return some (args[5]!, pf)

/-- Unfold a single application of `name` at the head of `e` when `name` is transparent. -/
private meta def unfoldHeadDef? (names : NameSet) (e : Expr) : MetaM (Option Expr) := do
  let .const n us := e.getAppFn | return none
  unless names.contains n do return none
  let info ← getConstInfo n
  unless info.hasValue && info.levelParams.length == us.length do return none
  let val ← instantiateValueLevelParams info us
  return some (val.betaRev e.getAppRevArgs (useZeta := true))

/-- Repeatedly unfold transparent constants from `names` at the head of `e` (bounded). -/
private meta def unfoldHeadDefs (names : NameSet) (e : Expr) (fuel : ℕ := 4) : MetaM Expr := do
  if names.isEmpty then return e
  let mut cur := e.cleanupAnnotations
  for _ in [:fuel] do
    let some nxt ← unfoldHeadDef? names cur | break
    cur := nxt.cleanupAnnotations.headBeta
  return cur

/-- Head-reduce `let` expressions (replacing `let x := v; body` with `body[v/x]`). -/
private meta partial def headZeta (e : Expr) : Expr :=
  match e.cleanupAnnotations with
  | .letE _ _ v b _ => headZeta (b.instantiate1 v)
  | e => e

/-- Unfold a `Data.mem r s` whose `s` is either a `let`-bound `fvar` or a `unfoldDefs` def. -/
private meta def stepStateDef? (unfoldDefs : NameSet) (m : Expr) : MetaM (Option Expr) := do
  let m := m.cleanupAnnotations
  if m.isFVar then
    if let some val ← m.fvarId!.getValue? then
      return some (← instantiateMVars val)
  if let some m' ← unfoldHeadDef? unfoldDefs m then
    return some m'
  let_expr Data.mem r d := m | return none
  let d := d.cleanupAnnotations
  if let .fvar fv := d then
    if let some val ← fv.getValue? then
      return some (mkApp2 (mkConst ``Data.mem) r (← instantiateMVars val))
  if let some d' ← unfoldHeadDef? unfoldDefs d then
    return some (mkApp2 (mkConst ``Data.mem) r d')
  let d' ← whnfR d
  if d' != d then
    return some (mkApp2 (mkConst ``Data.mem) r d')
  return none

/-- Prove a closed proposition `p` by evaluating its `Decidable` instance in the kernel.
On kernel rejection, restores the environment so no axiom leaks. -/
private meta def decideKernel? (p : Expr) : MetaM (Option Expr) := do
  if p.hasFVar || p.hasMVar || p.hasLevelParam then return none
  let some inst ← synthInstance? (mkApp (mkConst ``Decidable) p) | return none
  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let saved ← saveState
  try
    return some (mkConst (← withOptions (Elab.async.set · false) <| mkAuxLemma [] p pf))
  catch _ =>
    saved.restore
    return none

/-- Structurally prove `Op.StoreFree o`, unfolding transparent definitions around `o`. -/
private meta partial def proveOpStoreFree? (o : Expr) : MetaM (Option Expr) := do
  let o' ← withAtLeastTransparency .default <| whnf o
  match o'.getAppFn.constName? with
  | some ``Op.const | some ``Op.copy | some ``Op.alu | some ``Op.load =>
    return some (mkConst ``True.intro)
  | some ``Op.rename =>
    let args := o'.getAppArgs
    if args.size == 5 then
      let inner := args[4]!
      if let some h ← proveOpStoreFree? inner then
        let tgt ← mkAppM ``Op.StoreFree #[o]
        return some (← mkExpectedTypeHint h tgt)
    return none
  | some ``Op.store => return none
  | _ =>
    WP.Exec.assumption? (← mkAppM ``Op.StoreFree #[o])

/-- Prove `Code.StoreFree c`: first fast kernel decision if `c` is closed, otherwise structural
recursion handling parameterized programs (`const d k`, `Code.rename`, `seq`, `branch`, `loop`,
`rand`), and falling back to an assumption in the local context. -/
private meta partial def proveStoreFree? (c : Expr) : MetaM (Option Expr) := do
  let c ← instantiateMVars c
  let goal ← mkAppM ``Code.StoreFree #[c]
  if let some h ← WP.Exec.assumption? goal then return some h
  if !c.hasFVar && !c.hasMVar && !c.hasLevelParam then
    if let some h ← decideKernel? goal then
      return some h
    return none
  let c' ← withAtLeastTransparency .default <| whnf c
  match_expr c' with
  | Code.op _ _ o =>
    let some h ← proveOpStoreFree? o | return none
    return some (← mkExpectedTypeHint h goal)
  | Code.seq _ _ c₁ c₂ =>
    let some h₁ ← proveStoreFree? c₁ | return none
    let some h₂ ← proveStoreFree? c₂ | return none
    let pf ← mkAppM ``And.intro #[h₁, h₂]
    return some (← mkExpectedTypeHint pf goal)
  | Code.branch _ _ _ pos neg =>
    let some h₁ ← proveStoreFree? pos | return none
    let some h₂ ← proveStoreFree? neg | return none
    let pf ← mkAppM ``And.intro #[h₁, h₂]
    return some (← mkExpectedTypeHint pf goal)
  | Code.loop _ _ _ body =>
    let some h ← proveStoreFree? body | return none
    return some (← mkExpectedTypeHint h goal)
  | Code.rand _ _ _ _ =>
    return some (← mkExpectedTypeHint (mkConst ``True.intro) goal)
  | Code.rename _ _ _ f body =>
    let some h ← proveStoreFree? body | return none
    let pf ← mkAppM ``Code.StoreFree.rename #[f, h]
    return some (← mkExpectedTypeHint pf goal)
  | _ => return none

/-- Cached wrapper around `proveStoreFree?`. -/
private meta def proveStoreFreeCached? (cache : IO.Ref Cache) (c : Expr) :
    MetaM (Option Expr) := do
  let c ← instantiateMVars c
  if let some r := (← cache.get).storeFree[c]? then
    return r
  let r ← proveStoreFree? c
  cache.modify fun st => { st with storeFree := st.storeFree.insert c r }
  return r

/-- Split a `Finset` / `Set` union expression (`Union.union` or `Max.max`). -/
private meta def unionParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  if e.isAppOfArity ``Union.union 4 || e.isAppOfArity ``Max.max 4 then
    some (e.getArg! 2, e.getArg! 3)
  else none

/-- Build `lo ≤ a ∧ a < hi` for `ℕ` bounds. -/
private meta def mkNatIcoProp (lo hi a : Expr) : MetaM Expr := do
  let p1 ← mkAppM ``LE.le #[lo, a]
  let p2 ← mkAppM ``LT.lt #[a, hi]
  mkAppM ``And #[p1, p2]

/-- Match `Finset.Ico lo hi` over `ℕ` (unfolding local `let` bindings) without requiring
`Finset.Ico` to be imported here. -/
private meta def finsetIcoNat? (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut s := s.cleanupAnnotations
  if let .fvar fv := s then
    if let some val ← fv.getValue? then
      s := (← instantiateMVars val).cleanupAnnotations
  if s.isAppOfArity `Finset.Ico 5 && (s.getArg! 0).isConstOf ``Nat then
    return some (s.getArg! 3, s.getArg! 4)
  return none

/-- Build `Finset.mem_Ico` over `ℕ` when `Finset.mem_Ico` is in the environment. -/
private meta def mkFinsetMemIco? (lo hi a : Expr) : MetaM (Option Expr) := do
  unless (← getEnv).contains `Finset.mem_Ico do return none
  return some (← mkAppOptM `Finset.mem_Ico
    #[some (mkConst ``Nat), none, none, some lo, some hi, some a])

/-- Instantiate an `Iff` theorem `lem` against `lhs ↔ rhs`, synthesizing any typeclass binders. -/
private meta def mkIffByConst (lem : Name) (lhs rhs : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels lem
  let (xs, _, concl) ← forallMetaTelescope (← inferType c)
  let expected := mkApp2 (mkConst ``Iff) lhs rhs
  unless ← isDefEq concl expected do
    throwError "MemFrame: `{lem}` did not match `{expected}`"
  for x in xs do
    let x' ← instantiateMVars x
    if x'.isMVar then
      let xty ← instantiateMVars (← inferType x')
      if (← isClass? xty).isSome then
        x'.mvarId!.assign (← synthInstance xty)
  instantiateMVars (mkAppN c xs)

/-- Recursively unpack arithmetic consequences from `h : a ∉ F` (`Block.footprint`, `Finset.Ico`,
`∪`, `{b}`) using Mathlib / `Heap` `Iff` lemmas directly. -/
private meta partial def unpackNotMem (h inner : Expr) (out : Array Expr) : MetaM (Array Expr) := do
  let_expr Membership.mem _ _ _ fp a := inner | return out
  if let some (f₁, f₂) := unionParts? fp then
    if (← inferType f₁).isAppOfArity ``Finset 1 then
      let m₁ ← mkAppM ``Membership.mem #[f₁, a]
      let m₂ ← mkAppM ``Membership.mem #[f₂, a]
      let iffU ← mkIffByConst ``Finset.notMem_union (mkNot inner)
        (← mkAppM ``And #[mkNot m₁, mkNot m₂])
      let conj ← mkAppM ``Iff.mp #[iffU, h]
      let h₁ ← mkAppM ``And.left #[conj]
      let h₂ ← mkAppM ``And.right #[conj]
      let out ← unpackNotMem h₁ m₁ out
      return ← unpackNotMem h₂ m₂ out
    return out
  if let some (lo, hi) ← finsetIcoNat? fp then
    if let some iffIco ← mkFinsetMemIco? lo hi a then
      let mpr ← mkAppM ``Iff.mpr #[iffIco]
      let icoProp ← mkNatIcoProp lo hi a
      let pf ← mkExpectedTypeHint (← mkAppM ``mt #[mpr, h]) (mkNot icoProp)
      return out.push pf
    return out
  match_expr fp with
  | Block.footprint b =>
    let iffFp ← mkAppOptM ``Block.mem_footprint #[some b, some a]
    let mpr ← mkAppM ``Iff.mpr #[iffFp]
    let base ← mkAppM ``Block.base #[b]
    let len ← mkAppM ``Block.length #[b]
    let hi ← mkAppM ``HAdd.hAdd #[base, len]
    let ownsProp ← mkNatIcoProp base hi a
    let pf ← mkExpectedTypeHint (← mkAppM ``mt #[mpr, h]) (mkNot ownsProp)
    return out.push pf
  | Singleton.singleton _ _ _ b =>
    if (← inferType fp).isAppOfArity ``Finset 1 then
      let iffS ← mkIffByConst ``Finset.notMem_singleton (mkNot inner) (← mkAppM ``Ne #[a, b])
      return out.push (← mkAppM ``Iff.mp #[iffS, h])
    return out
  | _ => return out

/-- Extract arithmetic facts from local hypotheses involving `Block.footprint`, `Finset.Ico`,
`Finset`, and `Set.Ico`, so `omega` / `wram_omega` can see them directly without mutating the
context. -/
private meta def collectDerivedArith : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).cleanupAnnotations
    if (← whnfR ty).isAppOfArity ``Fin 1 then
      out := out.push (← mkAppM ``Fin.isLt #[d.toExpr])
    match_expr ty with
    | Not inner =>
      out ← unpackNotMem d.toExpr inner out
    | Membership.mem _ _ _ s a =>
      if let some (lo, hi) ← finsetIcoNat? s then
        if let some iffIco ← mkFinsetMemIco? lo hi a then
          out := out.push (← mkAppM ``Iff.mp #[iffIco, d.toExpr])
      match_expr s with
      | Block.footprint b =>
        let iffFp ← mkAppOptM ``Block.mem_footprint #[some b, some a]
        let base ← mkAppM ``Block.base #[b]
        let len ← mkAppM ``Block.length #[b]
        let hi ← mkAppM ``HAdd.hAdd #[base, len]
        let ownsProp ← mkNatIcoProp base hi a
        let pf ← mkExpectedTypeHint (← mkAppM ``Iff.mp #[iffFp, d.toExpr]) ownsProp
        out := out.push pf
      | Set.Ico _ _ _ _ =>
        if (← inferType a).isConstOf ``Nat then
          out := out.push (← mkAppM ``And.left #[d.toExpr])
          out := out.push (← mkAppM ``And.right #[d.toExpr])
      | _ => pure ()
    | _ => pure ()
  return out

/-- Whether `p` looks like a proposition that `omega` / `wram_omega` has a chance to solve. -/
private meta partial def looksArith (tagged : NameMap Cslib.Tactic.WramOmega.Kind) (p : Expr) :
    Bool :=
  let p := p.cleanupAnnotations
  match_expr p with
  | Eq α _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | Ne α _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | LE.le α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | LT.lt α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | GE.ge α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | GT.gt α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  | Dvd.dvd α _ _ _ => α.isConstOf ``Nat || α.isConstOf ``Int
  | Not q => looksArith tagged q
  | And q r => looksArith tagged q || looksArith tagged r
  | Or q r => looksArith tagged q || looksArith tagged r
  | Iff q r => looksArith tagged q || looksArith tagged r
  | True => true
  | False => true
  | _ =>
    match p.getAppFn with
    | .const n _ => tagged.find? n == some .predicate
    | _ => false

/-- Close the goal `g` with `Omega.omega`, returning `true` on success. -/
private meta def runOmegaWith (g : MVarId) (extra : Array Expr) : MetaM Bool := do
  let saved ← saveState
  try
    let some g ← g.falseOrByContra | return true
    g.withContext do
      let type ← g.getType
      let proof ← mkFreshExprSyntheticOpaqueMVar type
      let hyps ← getLocalHyps
      Omega.omega (hyps ++ extra).toList proof.mvarId!
      g.assign (← mkAuxTheorem type (← instantiateMVars proof) (zetaDelta := true))
    return true
  catch _ =>
    saved.restore
    return false

/-- Close `p` via fast plain `omega`, quick negation refutation, or silent heartbeat-bounded
`Cslib.Tactic.WramOmega.tryProve`. -/
private meta def tryWramOmega (p : Expr) (extra : Array Expr) : MetaM (Option Expr) := do
  let tagged := Cslib.Tactic.WramOmega.wramArithExt.getState (← getEnv)
  unless looksArith tagged p do return none
  let g ← mkFreshExprSyntheticOpaqueMVar p
  let addPows (e : Expr) (acc : Array Expr × Std.HashSet Expr) : Array Expr × Std.HashSet Expr :=
    let rec go (e : Expr) (acc : Array Expr × Std.HashSet Expr) :=
      if Cslib.Tactic.WramOmega.isPowerOfTwo e && !e.hasLooseBVars && !acc.2.contains e then
        (acc.1.push (mkApp (mkConst ``Nat.two_pow_pos) e.appArg!), acc.2.insert e)
      else
        match e with
        | .app f a => go a (go f acc)
        | .mdata _ b => go b acc
        | _ => acc
    go e acc
  let (powFacts, _) := addPows p (#[], {})
  if ← runOmegaWith g.mvarId! (extra ++ powFacts) then
    return some (← instantiateMVars g)
  -- Quick refutation check: if plain `omega` already proves `¬p` (for `a = b` / `a ≠ b`),
  -- skip unfolding the context for `wram_omega`.
  let pc := p.cleanupAnnotations
  if let some (α, a, b) := pc.eq? then
    if α.isConstOf ``Nat then
      let gNeg ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[a, b])
      if ← runOmegaWith gNeg.mvarId! (extra ++ powFacts) then return none
  else if pc.isAppOfArity ``Ne 3 && (pc.getArg! 0).isConstOf ``Nat then
    let gNeg ← mkFreshExprSyntheticOpaqueMVar (← mkEq (pc.getArg! 1) (pc.getArg! 2))
    if ← runOmegaWith gNeg.mvarId! (extra ++ powFacts) then return none
  let g2 ← mkFreshExprSyntheticOpaqueMVar p
  if ← Cslib.Tactic.WramOmega.tryProve g2.mvarId! (extra := extra) then
    return some (← instantiateMVars g2)
  return none

/-- Prove a premise `p`:
1. `Code.StoreFree` / `Op.StoreFree` (kernel decision or structural check)
2. syntactic hypothesis match (incl. `Ne.symm` for `a ≠ b` / `b ≠ a`)
3. closed decidable evaluation (`decideClosed?`, also after `zetaReduce`)
4. `Block.footprint` / `Finset.Ico` / `Set.Ico` / `Set.Iio` / `Set.Ici` / `Finset` conversion
5. `omega` and silent `wram_omega`. -/
private meta partial def discharge (F : Facts) (cache : IO.Ref Cache) (p : Expr) :
    MetaM (Option Expr) := do
  let p ← instantiateMVars p
  if p.hasExprMVar then return none
  let key := p.cleanupAnnotations
  if let some hit := (← cache.get).disch[key]? then
    return hit
  let save (res : Option Expr) : MetaM (Option Expr) := do
    cache.modify fun st => { st with disch := st.disch.insert key res }
    return res
  if key.isAppOf ``Code.StoreFree then
    let c := key.appArg!
    return ← save (← proveStoreFreeCached? cache c)
  if key.isAppOf ``Op.StoreFree then
    let o := key.appArg!
    return ← save (← proveOpStoreFree? o)
  if key.isTrue then return ← save (some (mkConst ``True.intro))
  if let some (_, a, b) := key.eq? then
    if ← withReducible (isDefEq a b) then
      return ← save (some (← mkEqRefl a))
  if let some h ← WP.Exec.assumption? key then
    return ← save (some h)
  if key.isAppOfArity ``Ne 3 then
    let a := key.getArg! 1
    let b := key.getArg! 2
    let eqAB ← mkEq a b
    let eqBA ← mkEq b a
    if let some h ← WP.Exec.assumption? (mkNot eqAB) then return ← save (some h)
    for q in [← mkAppM ``Ne #[b, a], mkNot eqBA] do
      if let some h ← WP.Exec.assumption? q then
        return ← save (some (← mkAppM ``Ne.symm #[h]))
  else if key.isAppOfArity ``Not 1 && key.appArg!.isAppOfArity ``Eq 3 then
    let a := key.appArg!.getArg! 1
    let b := key.appArg!.getArg! 2
    for q in [← mkAppM ``Ne #[a, b]] do
      if let some h ← WP.Exec.assumption? q then return ← save (some h)
    for q in [← mkAppM ``Ne #[b, a], mkNot (← mkEq b a)] do
      if let some h ← WP.Exec.assumption? q then
        return ← save (some (← mkAppM ``Ne.symm #[h]))
  match ← WP.Exec.decideClosed? key with
  | some (some h) => return ← save (some h)
  | some none => return ← save none
  | none =>
    if !key.hasFVar && !key.hasMVar then
      let q ← Core.betaReduce (← zetaReduce key)
      if q != key then
        if let some (some h) ← WP.Exec.decideClosed? q then
          return ← save (some (← mkExpectedTypeHint h p))
  match_expr key with
  | Not inner =>
    if let some (b, a) := (do
      let_expr Membership.mem _ _ _ fp a := inner | none
      let_expr Block.footprint b := fp | none
      return (b, a)) then
      let base ← mkAppM ``Block.base #[b]
      let len ← mkAppM ``Block.length #[b]
      let hi ← mkAppM ``HAdd.hAdd #[base, len]
      let arithGoal := mkNot (← mkNatIcoProp base hi a)
      if let some h ← discharge F cache arithGoal then
        let iffFp ← mkAppOptM ``Block.mem_footprint #[some b, some a]
        let mp ← mkAppM ``Iff.mp #[iffFp]
        return ← save (some (← mkExpectedTypeHint (← mkAppM ``mt #[mp, h]) p))
    if let some (lo, hi, a) ← (do
      let_expr Membership.mem _ _ _ fp a := inner | return none
      let some (lo, hi) ← finsetIcoNat? fp | return none
      return some (lo, hi, a)) then
      let arithGoal := mkNot (← mkNatIcoProp lo hi a)
      if let some h ← discharge F cache arithGoal then
        if let some iffIco ← mkFinsetMemIco? lo hi a then
          let mp ← mkAppM ``Iff.mp #[iffIco]
          return ← save (some (← mkExpectedTypeHint (← mkAppM ``mt #[mp, h]) p))
    if let some (s, t, a) := (do
      let_expr Membership.mem _ _ _ u a := inner | none
      let (s, t) ← unionParts? u
      return (s, t, a)) then
      if (← inferType s).isAppOfArity ``Finset 1 then
        let p1 := mkNot (← mkAppM ``Membership.mem #[s, a])
        let p2 := mkNot (← mkAppM ``Membership.mem #[t, a])
        if let (some h1, some h2) := (← discharge F cache p1, ← discharge F cache p2) then
          let iffU ← mkIffByConst ``Finset.notMem_union key (← mkAppM ``And #[p1, p2])
          let pf ← mkAppM ``Iff.mpr #[iffU, ← mkAppM ``And.intro #[h1, h2]]
          return ← save (some (← mkExpectedTypeHint pf p))
    if let some (x, a) := (do
      let_expr Membership.mem _ _ _ fp a := inner | none
      let_expr Singleton.singleton _ _ _ x := fp | none
      return (x, a)) then
      if (← inferType x).isConstOf ``Nat then
        let pne ← mkAppM ``Ne #[a, x]
        if let some hne ← discharge F cache pne then
          if let some pf ← observing? (do
              let iffS ← mkIffByConst ``Finset.notMem_singleton key pne
              mkExpectedTypeHint (← mkAppM ``Iff.mpr #[iffS, hne]) p) then
            return ← save (some pf)
  | Membership.mem _ _ _ s a =>
    if let some (lo, hi) ← finsetIcoNat? s then
      let arithGoal ← mkNatIcoProp lo hi a
      if let some h ← discharge F cache arithGoal then
        if let some iffIco ← mkFinsetMemIco? lo hi a then
          return ← save (some (← mkExpectedTypeHint (← mkAppM ``Iff.mpr #[iffIco, h]) p))
    match_expr s with
    | Block.footprint b =>
      let base ← mkAppM ``Block.base #[b]
      let len ← mkAppM ``Block.length #[b]
      let hi ← mkAppM ``HAdd.hAdd #[base, len]
      let arithGoal ← mkNatIcoProp base hi a
      if let some h ← discharge F cache arithGoal then
        let iffFp ← mkAppOptM ``Block.mem_footprint #[some b, some a]
        return ← save (some (← mkExpectedTypeHint (← mkAppM ``Iff.mpr #[iffFp, h]) p))
    | Set.Ico _ _ lo hi =>
      let p1 ← mkAppM ``LE.le #[lo, a]
      let p2 ← mkAppM ``LT.lt #[a, hi]
      if let (some h1, some h2) := (← discharge F cache p1, ← discharge F cache p2) then
        return ← save (some (← mkExpectedTypeHint (← mkAppM ``And.intro #[h1, h2]) p))
    | Set.Iio _ _ hi =>
      let p1 ← mkAppM ``LT.lt #[a, hi]
      if let some h1 ← discharge F cache p1 then
        return ← save (some (← mkExpectedTypeHint h1 p))
    | Set.Ici _ _ lo =>
      let p1 ← mkAppM ``LE.le #[lo, a]
      if let some h1 ← discharge F cache p1 then
        return ← save (some (← mkExpectedTypeHint h1 p))
    | Set.ofPred _ pred =>
      let q ← Core.betaReduce (mkApp pred a)
      if let some h ← discharge F cache q then
        return ← save (some (← mkExpectedTypeHint h p))
    | _ => pure ()
  | And q r =>
    if let (some hq, some hr) := (← discharge F cache q, ← discharge F cache r) then
      return ← save (some (← mkAppM ``And.intro #[hq, hr]))
  | _ => pure ()
  let extra := (← cache.get).derivedArith ++ F.arithHints
  if let some h ← tryWramOmega key extra then
    return ← save (some (← mkExpectedTypeHint h p))
  let pZeta ← Core.betaReduce (← zetaReduce key)
  if pZeta != key then
    if let some h ← tryWramOmega pZeta extra then
      return ← save (some (← mkExpectedTypeHint h p))
  return ← save none

/-- The frame `J.mem_eq he` of an execution hypothesis `he : J ...`, such as `Exec` or
`ExecWithin`, when the lemma `J.mem_eq` exists in the environment. -/
private meta def execFrame? (he ty : Expr) (J : Name) : MetaM (Option (Expr × ExecFrame)) := do
  let lemmaName := J ++ `mem_eq
  unless (← getEnv).contains lemmaName do return none
  withNewMCtxDepth do
    let c ← mkConstWithFreshMVarLevels lemmaName
    let (xs, bis, _) ← forallMetaTelescope (← inferType c)
    let some idx := bis.findIdx? (· == .default) | return none
    unless ← isDefEq (← inferType xs[idx]!) ty do return none
    unless ← isDefEq xs[idx]! he do return none
    let proof := (← abstractMVars (mkAppN c xs) (levels := false)).expr
    if proof.hasMVar then return none
    let pTy ← inferType proof
    let body := pTy.getForallBody
    let some (α, lhs, _) := body.eq? | return none
    if ← isMemType α then
      return some (memKey lhs, { proof, type := pTy, name := m!"{he}.mem_eq" })
    else if α.isConstOf ``Nat then
      let .app m' _ := lhs.cleanupAnnotations | return none
      if m'.hasLooseBVars then return none
      return some (memKey m', { proof, type := pTy, name := m!"{he}.mem_eq" })
    else
      return none

/-- Recognize whether `ty` is a pointwise memory frame `∀ xs, m' pat = m pat` with `pat` involving
at least one bound variable of `ty` and neither `m'` nor `m` depending on `xs`. -/
private meta def frameHead? (ty : Expr) : Option (Expr × Expr) := do
  guard ty.isForall
  let (α, lhs, rhs) ← ty.getForallBody.cleanupAnnotations.eq?
  guard (α.isConstOf ``Nat)
  let .app m' aL := lhs.cleanupAnnotations | none
  let .app m aR := rhs.cleanupAnnotations | none
  guard (aL == aR && aL.hasLooseBVars && !m'.hasLooseBVars && !m.hasLooseBVars && m' != m)
  return (m', m)

/-- Recognize whether `ty` is a quantified slice equation `∀ xs, m pat = val` with `m` not
depending on `xs`. -/
private meta def sliceHead? (ty : Expr) : Option Expr := do
  guard ty.isForall
  let (α, lhs, rhs) ← ty.getForallBody.cleanupAnnotations.eq?
  guard (α.isConstOf ``Nat)
  let .app m addr := lhs.cleanupAnnotations | none
  guard (addr.hasLooseBVars && !m.hasLooseBVars)
  guard (rhs.find? (· == lhs) |>.isNone)
  return m

/-- Check if `h : ty` is a `Data r` equality `s₁ = s₂`. -/
private meta def dataEqParts? (ty : Expr) : Option (Expr × Expr × Expr) := do
  let (α, lhs, rhs) ← ty.cleanupAnnotations.eq?
  guard (α.isAppOfArity ``Data 1)
  return (α.appArg!, lhs.cleanupAnnotations, rhs.cleanupAnnotations)

/-- Record `h : ty` into `Facts`. -/
private meta partial def addFact (h ty : Expr) (name : MessageData)
    (depth : ℕ := 0) (isHint : Bool := false) : StateT Facts MetaM Unit := do
  let ty := headZeta ty.cleanupAnnotations.headBeta
  let registerMem (m : Expr) : StateT Facts MetaM Unit := do
    let mc := memKey m
    modify fun F => { F with knownMems := (F.knownMems.insert mc).insert m.cleanupAnnotations }
  let addWhole (mL mR proof : Expr) (fwd : Bool) (nm : MessageData) : StateT Facts MetaM Unit := do
    let kL := memKey mL
    let kR := memKey mR
    if kL == kR then return
    registerMem mL
    registerMem mR
    let eq : WholeEq := { proof, rhs := mR, forward := fwd, name := nm }
    modify fun F => { F with wholeEqs := F.wholeEqs.insert kL ((F.wholeEqs.getD kL #[]).push eq) }
  let addFrame (m' : Expr) (f : Frame) : StateT Facts MetaM Unit := do
    let k := memKey m'
    registerMem m'
    modify fun F => { F with frames := F.frames.insert k ((F.frames.getD k #[]).push f) }
  let addCell (m addr val proof : Expr) (nm : MessageData) : StateT Facts MetaM Unit := do
    let k := memKey m
    registerMem m
    let cv : CellVal := { addr, val, proof, name := nm }
    modify fun F => { F with cellVals := F.cellVals.insert k ((F.cellVals.getD k #[]).push cv) }
  let addSlice (m : Expr) (sv : SliceVal) : StateT Facts MetaM Unit := do
    let k := memKey m
    registerMem m
    modify fun F => { F with sliceVals := F.sliceVals.insert k ((F.sliceVals.getD k #[]).push sv) }
  if let some (α, lhs, rhs) := ty.eq? then
    let lhs := lhs.cleanupAnnotations
    let rhs := rhs.cleanupAnnotations
    if lhs == rhs then return
    if ← isMemType α then
      if (rhs.find? (· == lhs)).isNone then
        addWhole lhs rhs h true name
      if (lhs.find? (· == rhs)).isNone then
        addWhole rhs lhs (← mkEqSymm h) false m!"{name}.symm"
      return
    if let some (r, s₁, s₂) := dataEqParts? ty then
      let m₁ := mkApp2 (mkConst ``Data.mem) r s₁
      let m₂ := mkApp2 (mkConst ``Data.mem) r s₂
      let pf ← mkAppM ``congrArg #[mkApp (mkConst ``Data.mem) r, h]
      if (s₂.find? (· == s₁)).isNone then
        addWhole m₁ m₂ pf true name
      if (s₁.find? (· == s₂)).isNone then
        addWhole m₂ m₁ (← mkEqSymm pf) false m!"{name}.symm"
      return
    if α.isConstOf ``Nat then
      let defs := (← get).unfoldDefs
      let lhsU ← unfoldHeadDefs defs lhs
      let rhsU ← unfoldHeadDefs defs rhs
      let mut handledLhs := false
      if let .app m a := lhsU then
        let mTy ← inferType m
        if (isIntrinsicMem m || (← get).knownMems.contains (memKey m) ||
            (m.isFVar && (← isMemType mTy))) &&
            (rhsU.find? (· == lhsU)).isNone then
          let h' ← if lhsU == lhs && rhsU == rhs then pure h
            else mkExpectedTypeHint h (← mkEq lhsU rhsU)
          addCell m a rhsU h' name
          if let .app mR aR := rhsU then
            if isIntrinsicMem mR || (← get).knownMems.contains (memKey mR) then
              registerMem mR
              if aR == a && (lhsU.find? (· == rhsU)).isNone then
                addCell mR a lhsU (← mkEqSymm h') m!"{name}.symm"
          handledLhs := true
      if !handledLhs then
        if let .app m a := rhsU then
          if isIntrinsicMem m && (lhsU.find? (· == rhsU)).isNone then
            let h' ← if lhsU == lhs && rhsU == rhs then pure h
              else mkExpectedTypeHint h (← mkEq lhsU rhsU)
            addCell m a lhsU (← mkEqSymm h') m!"{name}.symm"
      return
    return
  if ty.isAppOfArity ``Modifies 3 then
    let writes := ty.getArg! 0
    let before := ty.getArg! 1
    let after := ty.getArg! 2
    registerMem before
    registerMem after
    let writes' := writes.cleanupAnnotations
    if writes'.isAppOfArity ``Block.footprint 1 then
      let b := writes'.appArg!
      let pf ← mkAppOptM ``Iff.mp #[none, none,
        some (← mkAppOptM ``Modifies.block_iff #[some b, some before, some after]), some h]
      addFrame after { proof := pf, type := ← inferType pf, name }
    else
      let ty' := (← withAtLeastTransparency .default <| unfoldDefinition? ty).getD (← whnf ty)
      addFrame after { proof := h, type := ty', name }
    return
  if ty.isAppOfArity ``Set.EqOn 5 then
    let f₁ := ty.getArg! 2
    let f₂ := ty.getArg! 3
    if (← isMemType (← inferType f₁)) then
      let ty' := (← withAtLeastTransparency .default <| unfoldDefinition? ty).getD (← whnf ty)
      registerMem f₁
      registerMem f₂
      addFrame f₁ { proof := h, type := ty', name }
      let hSymm ← mkAppM ``Set.EqOn.symm #[h]
      let tySymm ← inferType hSymm
      let tySymm' :=
        (← withAtLeastTransparency .default <| unfoldDefinition? tySymm).getD (← whnf tySymm)
      addFrame f₂ { proof := hSymm, type := tySymm', name := m!"{name}.symm" }
      return
  if ty.isForall then
    if let some (m', m) := frameHead? ty then
      let isMem ← do
        if isIntrinsicMem m' || isIntrinsicMem m then pure true
        else isMemType (← inferType m')
      if isMem then
        registerMem m'
        registerMem m
        addFrame m' { proof := h, type := ty, name }
        return
    if let some m := sliceHead? ty then
      let isMem := isIntrinsicMem m || (← get).knownMems.contains (memKey m) ||
        (m.isFVar && (← isMemType (← inferType m)))
      if isMem then
        addSlice m { proof := h, type := ty, name }
        return
    if isHint then
      if let some (α, lhs, _) := ty.getForallBody.cleanupAnnotations.eq? then
        if α.isConstOf ``Nat && lhs.isApp then
          modify fun F =>
            { F with patternFrames := F.patternFrames.push { proof := h, type := ty, name } }
    return
  if let some (p, q) := ty.and? then
    addFact (mkApp3 (mkConst ``And.left) p q h) p name depth isHint
    addFact (mkApp3 (mkConst ``And.right) p q h) q name depth isHint
    return
  let .const c _ := ty.getAppFn | return
  if let some (mk, ef) ← execFrame? h ty c then
    modify fun F =>
      { F with
        knownMems := F.knownMems.insert mk
        execFrames := F.execFrames.insert mk ((F.execFrames.getD mk #[]).push ef) }
    return
  if (← get).unfoldDefs.contains c && depth < 4 then
    if let some ty' ← unfoldHeadDef? (← get).unfoldDefs ty then
      addFact h ty' name (depth + 1) isHint
      return
  if (← isMatcher c) && depth < 4 then
    let ty' ← withAtLeastTransparency .default <| whnf ty
    if ty' != ty then
      addFact h ty' name (depth + 1) isHint
      return
  let env ← getEnv
  unless depth < 3 && isStructure env c && !isClass env c && c != ``Iff do return
  let some info := env.find? c | return
  unless info.type.getForallBody.isProp do return
  for field in getStructureFields env c do
    let some proj := getProjFnForField? env c field | continue
    let p ← mkAppOptM proj ((ty.getAppArgs.map some).push (some h))
    addFact p (← inferType p) m!"{name}.{field}" (depth + 1) isHint

/-- Two-pass scan over the local context plus explicit hints. -/
private meta def scan (unfoldDefs : NameSet) (hints : Array (Expr × MessageData × Bool)) :
    MetaM Facts := do
  let mut F : Facts := { unfoldDefs }
  let registerFromType (ty : Expr) (F : Facts) : MetaM Facts := do
    let ty := headZeta ty.cleanupAnnotations.headBeta
    if let some (α, lhs, rhs) := ty.eq? then
      if ← isMemType α then
        let mut s := F.knownMems
        s := s.insert (memKey lhs) |>.insert lhs.cleanupAnnotations
        s := s.insert (memKey rhs) |>.insert rhs.cleanupAnnotations
        return { F with knownMems := s }
    if ty.isAppOfArity ``Modifies 3 then
      let b := ty.getArg! 1; let a := ty.getArg! 2
      return { F with knownMems := F.knownMems |>.insert (memKey b) |>.insert (memKey a) }
    if ty.isAppOfArity ``Set.EqOn 5 then
      let f₁ := ty.getArg! 2; let f₂ := ty.getArg! 3
      if ← isMemType (← inferType f₁) then
        return { F with knownMems := F.knownMems |>.insert (memKey f₁) |>.insert (memKey f₂) }
    if let some (m', m) := frameHead? ty then
      return { F with knownMems := F.knownMems |>.insert (memKey m') |>.insert (memKey m) }
    return F
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isMemType ty then
      F := { F with knownMems := F.knownMems.insert d.toExpr }
    F ← registerFromType ty F
  for (h, _, _) in hints do
    F ← registerFromType (← instantiateMVars (← inferType h)) F
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    (_, F) ← (addFact d.toExpr ty m!"{d.toExpr}").run F
  let mut arithHints : Array Expr := #[]
  for (h, nm, isHint) in hints do
    let ty ← instantiateMVars (← inferType h)
    (_, F) ← (addFact h ty nm (isHint := isHint)).run F
    unless ty.isForall do
      arithHints := arithHints.push h
  return { F with arithHints }

/-- Apply a pointwise frame `f` to the memory read `e = m' a`. -/
private meta def applyFrame (F : Facts) (cache : IO.Ref Cache) (f : Frame) (e : Expr) :
    MetaM (Except (Option Expr) (Expr × Expr)) :=
  withNewMCtxDepth do
    let (xs, _, body) ← forallMetaTelescopeReducing f.type
    let some (_, lhs, rhs) := body.cleanupAnnotations.eq? | return .error none
    let ok ← withReducible (isDefEq lhs e)
    let ok ← if ok then pure true else
      match lhs.cleanupAnnotations, e.cleanupAnnotations with
      | .app mL aL, .app mE aE =>
        if memKey mL == memKey mE || (← isDefEq (canonMem mL) (canonMem mE)) then
          withReducible (isDefEq aL aE)
        else pure false
      | _, _ => pure false
    if ok then
      for x in xs do
        let x' ← instantiateMVars x
        unless x'.isMVar do continue
        let p ← instantiateMVars (← inferType x')
        unless ← isProp p do return .error none
        let some h ← discharge F cache p | return .error (some p)
        x'.mvarId!.assign h
      let pf ← instantiateMVars (mkAppN f.proof xs)
      let rhs' ← instantiateMVars rhs
      return .ok (rhs', ← mkExpectedTypeHint pf (← mkEq e rhs'))
    -- Special case: `lhs` is `mL (base + ?k)` and `e` is `mE base` (`?k := 0`, `Nat.add_zero`).
    let .app mL larg := lhs.cleanupAnnotations | return .error none
    let .app mE earg := e.cleanupAnnotations | return .error none
    unless larg.isAppOfArity ``HAdd.hAdd 6 do return .error none
    let base := larg.getArg! 4
    let k := larg.getArg! 5
    unless k.isMVar &&
        (memKey mL == memKey mE || (← isDefEq (canonMem mL) (canonMem mE))) &&
        (← withReducible (isDefEq base earg)) do
      return .error none
    k.mvarId!.assign (mkNatLit 0)
    for x in xs do
      let x' ← instantiateMVars x
      unless x'.isMVar do continue
      let p ← instantiateMVars (← inferType x')
      unless ← isProp p do return .error none
      let some h ← discharge F cache p | return .error (some p)
      x'.mvarId!.assign h
    let pfRaw ← instantiateMVars (mkAppN f.proof xs)
    let .app rfn _ := (← instantiateMVars rhs).cleanupAnnotations | return .error none
    let lhsZero ← mkAppM ``Nat.add_zero #[earg]
    let p1 ← mkCongrArg mE (← mkEqSymm lhsZero)
    let p3 ← mkCongrArg rfn lhsZero
    let pf ← mkEqTrans p1 (← mkEqTrans (← mkExpectedTypeHint pfRaw
      (← mkEq (mkApp mE (← mkAppM ``HAdd.hAdd #[earg, mkNatLit 0]))
        (mkApp rfn (← mkAppM ``HAdd.hAdd #[earg, mkNatLit 0])))) p3)
    return .ok (mkApp rfn earg, ← mkExpectedTypeHint pf (← mkEq e (mkApp rfn earg)))

/-- Try to activate an `ExecFrame` (`J.mem_eq he`). -/
private meta def applyExecFrame (F : Facts) (cache : IO.Ref Cache) (ef : ExecFrame) :
    MetaM (Except (Option Expr) (Expr × Expr)) :=
  withNewMCtxDepth do
    let (xs, _, body) ← forallMetaTelescopeReducing ef.type
    let some (α, _, rhs) := body.cleanupAnnotations.eq? | return .error none
    unless ← isMemType α do return .error none
    for x in xs do
      let x' ← instantiateMVars x
      unless x'.isMVar do continue
      let p ← instantiateMVars (← inferType x')
      unless ← isProp p do return .error none
      let some h ← discharge F cache p | return .error (some p)
      x'.mvarId!.assign h
    let pf ← instantiateMVars (mkAppN ef.proof xs)
    return .ok (← instantiateMVars rhs, pf)

/-- Record a stuck read and the failed frame premises for error reporting. -/
private meta def recordStuck (cache : IO.Ref Cache) (e : Expr)
    (failed : Array (MessageData × Expr)) : MetaM Unit :=
  cache.modify fun st =>
    if st.stuck.any (·.1 == e) then st else { st with stuck := st.stuck.push (e, failed) }

/-- Try to connect two whole memory expressions `m₁ m₂ : ℕ → ℕ` using `Data.set`, `Data.comap`,
`Data.extend`, `Data.havoc`, `let`-bindings, `unfoldDefs`, `WholeEq`, and `ExecFrame` (`J.mem_eq`).
Returns a proof of `m₁ = m₂`. -/
private meta def findWholeMemEq? (F : Facts) (cache : IO.Ref Cache) (m₁ m₂ : Expr) :
    MetaM (Option Expr) := do
  let expand (root : Expr) : MetaM (Array (Expr × Expr) × Std.HashMap Expr (Expr × Expr)) := do
    let initProof ← mkEqRefl root
    let mut visited : Std.HashMap Expr (Expr × Expr) := {}
    visited := visited.insert (memKey root) (root, initProof)
    let mut queue : Array (Expr × Expr) := #[(root, initProof)]
    let mut idx := 0
    while idx < queue.size && visited.size < 64 do
      let (cur, pCur) := queue[idx]!
      idx := idx + 1
      let mCanon := canonMem cur
      let key := memKey cur
      let push (nxt : Expr) (stepPf : Expr)
          (visited : Std.HashMap Expr (Expr × Expr)) (queue : Array (Expr × Expr)) :
          MetaM (Std.HashMap Expr (Expr × Expr) × Array (Expr × Expr)) := do
        let nKey := memKey nxt
        if visited.contains nKey then return (visited, queue)
        let pNew ← mkEqTrans pCur stepPf
        return (visited.insert nKey (nxt, pNew), queue.push (nxt, pNew))
      if let some (nxt, pf) ← stepHavocMem? mCanon then
        let step ← mkExpectedTypeHint pf (← mkEq cur nxt)
        (visited, queue) ← push nxt step visited queue
      if let some nxt ← stepStateDef? F.unfoldDefs mCanon then
        let nKey := memKey nxt
        unless visited.contains nKey do
          let step ← mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur nxt)
          (visited, queue) ← push nxt step visited queue
      let weqs := (F.wholeEqs.getD key #[]).reverse
      for we in weqs do
        if we.forward then
          let nKey := memKey we.rhs
          unless visited.contains nKey do
            let step ← mkExpectedTypeHint we.proof (← mkEq cur we.rhs)
            (visited, queue) ← push we.rhs step visited queue
      let mut failed : Array (MessageData × Expr) := #[]
      for ef in (F.execFrames.getD key #[]).reverse do
        match ← applyExecFrame F cache ef with
        | .ok (rhs, pf) =>
          let nKey := memKey rhs
          unless visited.contains nKey do
            let step ← mkExpectedTypeHint pf (← mkEq cur rhs)
            (visited, queue) ← push rhs step visited queue
        | .error (some p) => failed := failed.push (ef.name, p)
        | .error none => pure ()
      if !failed.isEmpty then
        recordStuck cache cur failed
      for we in weqs do
        if !we.forward then
          let nKey := memKey we.rhs
          unless visited.contains nKey do
            let step ← mkExpectedTypeHint we.proof (← mkEq cur we.rhs)
            (visited, queue) ← push we.rhs step visited queue
    return (queue, visited)
  if !m₁.hasExprMVar && !m₂.hasExprMVar then
    if ← withReducible (isDefEq m₁ m₂) then
      return some (← mkEqRefl m₁)
  let (q₁, v₁) ← expand m₁
  if let some (mHit, p₁) := v₁[memKey m₂]? then
    if ← isDefEq mHit m₂ then
      return some (← mkExpectedTypeHint p₁ (← mkEq m₁ m₂))
  let (q₂, _) ← expand m₂
  for (mB, pB) in q₂ do
    if let some (mA, pA) := v₁[memKey mB]? then
      if ← isDefEq mA mB then
        let pf ← mkEqTrans pA (← mkEqSymm pB)
        return some (← mkExpectedTypeHint pf (← mkEq m₁ m₂))
  for (mA, pA) in q₁ do
    for (mB, pB) in q₂ do
      if !mA.hasExprMVar && !mB.hasExprMVar then
        if ← withReducible (isDefEq mA mB) then
          let pf ← mkEqTrans pA (← mkEqSymm pB)
          return some (← mkExpectedTypeHint pf (← mkEq m₁ m₂))
  return none

/-- Single deterministic reduction across `Data.write` / `Function.update` at a concrete read
`m a`, using `Function.update_self` and `Function.update_of_ne` directly. -/
private meta def stepWrite? (F : Facts) (cache : IO.Ref Cache) (m a : Expr) :
    MetaM (Except (MessageData × Expr) (Option (Expr × Expr × Bool))) := do
  let m' := m.cleanupAnnotations
  let_expr Data.mem r d := m'
    | if m'.isAppOfArity ``Function.update 6 && (m'.getArg! 0).isConstOf ``Nat then
        let α := m'.getArg! 0
        let β := m'.getArg! 1
        let inst := m'.getArg! 2
        let m₀ := m'.getArg! 3
        let b := m'.getArg! 4
        let v := m'.getArg! 5
        if a == b || (← withReducible (isDefEq a b)) then
          let pf ← mkAppOptM ``Function.update_self #[some α, some β, some inst, some b, some v,
            some m₀]
          return .ok (some (v, ← mkExpectedTypeHint pf (← mkEq (mkApp m a) v), true))
        let neProp ← mkAppM ``Ne #[a, b]
        if let some hne ← discharge F cache neProp then
          let pf ← mkAppOptM ``Function.update_of_ne
            #[some α, some β, some inst, some a, some b, some hne, some v, some m₀]
          return .ok (some (mkApp m₀ a, ← mkExpectedTypeHint pf (← mkEq (mkApp m a) (mkApp m₀ a)),
            false))
        let eqProp ← mkEq a b
        if let some heq ← discharge F cache eqProp then
          let p1 ← mkCongrArg m' heq
          let p2 ← mkAppOptM ``Function.update_self #[some α, some β, some inst, some b, some v,
            some m₀]
          let pf ← mkEqTrans p1 p2
          return .ok (some (v, ← mkExpectedTypeHint pf (← mkEq (mkApp m a) v), true))
        return .error (m!"write at {b}", neProp)
      return .ok none
  let_expr Data.write _ x b v := d.cleanupAnnotations | return .ok none
  if a == b || (← withReducible (isDefEq a b)) then
    let pf := mkApp4 (mkConst ``Data.write_mem_self) r x b v
    return .ok (some (v, ← mkExpectedTypeHint pf (← mkEq (mkApp m a) v), true))
  let neProp ← mkAppM ``Ne #[a, b]
  if let some hne ← discharge F cache neProp then
    let pf := mkAppN (mkConst ``Data.write_mem_of_ne) #[r, x, b, a, hne, v]
    return .ok (some (mkApp2 (mkConst ``Data.mem) r x |>.app a, pf, false))
  let eqProp ← mkEq a b
  if let some heq ← discharge F cache eqProp then
    let pf := mkAppN (mkConst ``Data.write_mem_of_eq) #[r, x, b, a, heq, v]
    return .ok (some (v, pf, true))
  return .error (m!"write at {b}", neProp)

/-- Result of expanding all memory reads reachable from `start = m₀ a`. -/
private meta structure Reach where
  /-- Reachable reads: canonical `(m, a)` → `(expr, proof : start = expr)`. -/
  reads : Std.HashMap Expr (Expr × Expr) := {}
  /-- Ordered list of visited read expressions `(m, a, fullExpr, proof)`. -/
  readList : Array (Expr × Expr × Expr × Expr) := #[]
  /-- Discovered non-read values `(val, proof : start = val)`. -/
  values : Array (Expr × Expr) := #[]

/-- Check a concrete `CellVal` list against read `m a`. If `arith := false`, checks only syntactic /
reducible defeq address matches (fast, no `omega`). If `arith := true`, checks the remaining
entries via `discharge` of `a = cv.addr`. -/
private meta def matchingCellVals (F : Facts) (cache : IO.Ref Cache) (m a : Expr)
    (arith : Bool) : MetaM (Array (Expr × Expr)) := do
  let cvs := (F.cellVals.getD (memKey m) #[]).reverse
  let mut hits : Array (Expr × Expr) := #[]
  let read := mkApp m a
  for cv in cvs do
    let isExact := a == cv.addr || (← withReducible (isDefEq a cv.addr))
    if !arith then
      if isExact then
        let pf ← mkExpectedTypeHint cv.proof (← mkEq read cv.val)
        hits := hits.push (cv.val, pf)
    else if !isExact then
      let eqProp ← mkEq a cv.addr
      if let some heq ← discharge F cache eqProp then
        let congrPf ← mkCongrArg m heq
        let pf ← mkEqTrans congrPf (← mkExpectedTypeHint cv.proof (← mkEq (mkApp m cv.addr) cv.val))
        hits := hits.push (cv.val, pf)
  return hits

/-- Check indexed slice equations `∀ xs, m pat = val` against read `m a`. -/
private meta def matchingSliceVals (F : Facts) (cache : IO.Ref Cache) (m a : Expr) :
    MetaM (Array (Expr × Expr) × Array (MessageData × Expr)) := do
  let svs := (F.sliceVals.getD (memKey m) #[]).reverse
  let mut hits : Array (Expr × Expr) := #[]
  let mut failed : Array (MessageData × Expr) := #[]
  let read := mkApp m a
  for sv in svs do
    let res ← withNewMCtxDepth do
      let (xs, _, body) ← forallMetaTelescopeReducing sv.type
      let some (_, lhs, rhs) := body.cleanupAnnotations.eq? | return Except.error none
      let ok ← withReducible (isDefEq lhs read)
      let ok ← if ok then pure true else
        match lhs.cleanupAnnotations with
        | .app mL aL =>
          if memKey mL == memKey m || (← isDefEq (canonMem mL) (canonMem m)) then
            withReducible (isDefEq aL a)
          else pure false
        | _ => pure false
      unless ok do return Except.error none
      for x in xs do
        let x' ← instantiateMVars x
        unless x'.isMVar do continue
        let p ← instantiateMVars (← inferType x')
        unless ← isProp p do return Except.error none
        let some h ← discharge F cache p | return Except.error (some p)
        x'.mvarId!.assign h
      let pf ← instantiateMVars (mkAppN sv.proof xs)
      let rhs' ← instantiateMVars rhs
      return Except.ok (rhs', ← mkExpectedTypeHint pf (← mkEq read rhs'))
    match res with
    | .ok hit => hits := hits.push hit
    | .error (some p) => failed := failed.push (sv.name, p)
    | .error none => pure ()
  return (hits, failed)

/-- Explore memory reads reachable from `start = m₀ a₀` with bounded BFS. -/
private meta def exploreRead (F : Facts) (cache : IO.Ref Cache) (m₀ a₀ : Expr)
    (target? : Option Expr := none) (maxReads : ℕ := 64) : MetaM (Option Expr × Reach) := do
  let start := mkApp m₀ a₀
  let initPf ← mkEqRefl start
  let mut reach : Reach := {}
  let keyOf (m a : Expr) : Expr := mkApp (memKey m) a.cleanupAnnotations
  let k0 := keyOf m₀ a₀
  reach := { reach with
    reads := reach.reads.insert k0 (start, initPf)
    readList := #[(m₀, a₀, start, initPf)] }
  let checkTarget (e pf : Expr) : MetaM (Option Expr) := do
    let some tgt := target? | return none
    if ← withReducible (isDefEq e tgt) then
      return some (← mkExpectedTypeHint pf (← mkEq start tgt))
    return none
  let mut qIdx := 0
  while qIdx < reach.readList.size && reach.readList.size ≤ maxReads do
    let (m, a, cur, pCur) := reach.readList[qIdx]!
    qIdx := qIdx + 1
    let mCanon := canonMem m
    let mKey := memKey m
    let mut advanced := false
    let mut failed : Array (MessageData × Expr) := #[]
    let enqueueVal (v stepPf : Expr) (r : Reach) : MetaM (Option Expr × Reach) := do
      let pTotal ← mkEqTrans pCur stepPf
      if let some hit ← checkTarget v pTotal then return (some hit, r)
      let r' :=
        if let some (m', a') := readMem? F v then
          let k := keyOf m' a'
          if r.reads.contains k then r
          else
            { r with
              reads := r.reads.insert k (v, pTotal)
              readList := r.readList.push (m', a', v, pTotal) }
        else
          { r with values := r.values.push (v, pTotal) }
      return (none, r')
    let enqueueRead (m' a' stepPf : Expr) (r : Reach) : MetaM (Option Expr × Reach) := do
      let m' := canonMem m'
      let k := keyOf m' a'
      if r.reads.contains k then return (none, r)
      let nxt := mkApp m' a'
      let stepPf ← mkExpectedTypeHint stepPf (← mkEq cur nxt)
      let pTotal ← mkEqTrans pCur stepPf
      if let some hit ← checkTarget nxt pTotal then return (some hit, r)
      let r' := { r with
        reads := r.reads.insert k (nxt, pTotal)
        readList := r.readList.push (m', a', nxt, pTotal) }
      return (none, r')
    -- 1. Concrete `CellVal` equations `m b = v` (exact address match only; arithmetic deferred)
    for (v, step) in ← matchingCellVals F cache mCanon a false do
      let step' ← mkExpectedTypeHint step (← mkEq cur v)
      let (hit?, r') ← enqueueVal v step' reach
      reach := r'
      if hit?.isSome then return (hit?, reach)
      advanced := true
    -- 2. Quantified `SliceVal` equations `∀ xs, m pat = v`
    let (sliceHits, sliceFailed) ← matchingSliceVals F cache mCanon a
    for (v, step) in sliceHits do
      let step' ← mkExpectedTypeHint step (← mkEq cur v)
      let (hit?, r') ← enqueueVal v step' reach
      reach := r'
      if hit?.isSome then return (hit?, reach)
      advanced := true
    failed := failed ++ sliceFailed
    -- 3. `Data.write` / `Function.update`
    match ← stepWrite? F cache mCanon a with
    | .ok (some (rhs, step, isVal)) =>
      let step' ← mkExpectedTypeHint step (← mkEq cur rhs)
      let (hit?, r') ← if isVal then enqueueVal rhs step' reach else
        match rhs.cleanupAnnotations with
        | .app m' a' => enqueueRead m' a' step' reach
        | _ => enqueueVal rhs step' reach
      reach := r'
      if hit?.isSome then return (hit?, reach)
      advanced := true
    | .ok none => pure ()
    | .error f => failed := failed.push f
    -- 4. `Data.havoc` memory unwrap `(x.havoc c v mem).mem = mem`
    if let some (mNext, pf) ← stepHavocMem? mCanon then
      let step ← mkCongrFun (← mkExpectedTypeHint pf (← mkEq mCanon mNext)) a
      let step' ← mkExpectedTypeHint step (← mkEq cur (mkApp mNext a))
      let (hit?, r') ← enqueueRead mNext a step' reach
      reach := r'
      if hit?.isSome then return (hit?, reach)
      advanced := true
    -- 5. `WholeEq` edges (forward first)
    let weqs := (F.wholeEqs.getD mKey #[]).reverse
    for we in weqs do
      if we.forward then
        let step ← mkCongrFun (← mkExpectedTypeHint we.proof (← mkEq mCanon we.rhs)) a
        let step' ← mkExpectedTypeHint step (← mkEq cur (mkApp we.rhs a))
        let (hit?, r') ← enqueueRead we.rhs a step' reach
        reach := r'
        if hit?.isSome then return (hit?, reach)
        advanced := true
    -- 6. Lazy `ExecFrame` (`J.mem_eq` for store-free code)
    for ef in (F.execFrames.getD mKey #[]).reverse do
      match ← applyExecFrame F cache ef with
      | .ok (mNext, pf) =>
        let step ← mkCongrFun (← mkExpectedTypeHint pf (← mkEq mCanon mNext)) a
        let step' ← mkExpectedTypeHint step (← mkEq cur (mkApp mNext a))
        let (hit?, r') ← enqueueRead mNext a step' reach
        reach := r'
        if hit?.isSome then return (hit?, reach)
        advanced := true
      | .error (some p) => failed := failed.push (ef.name, p)
      | .error none => pure ()
    -- 7. Pointwise `Frame`s `∀ xs, m' pat = m pat`
    for f in (F.frames.getD mKey #[]).reverse do
      match ← applyFrame F cache f (mkApp mCanon a) with
      | .ok (rhs, step) =>
        let step' ← mkExpectedTypeHint step (← mkEq cur rhs)
        let (hit?, r') ← match rhs.cleanupAnnotations with
          | .app m' a' => enqueueRead m' a' step' reach
          | _ => enqueueVal rhs step' reach
        reach := r'
        if hit?.isSome then return (hit?, reach)
        advanced := true
      | .error (some p) => failed := failed.push (f.name, p)
      | .error none => pure ()
    -- 8. User-supplied polymorphic pattern frames (from `mem_frame [lem]`)
    for f in F.patternFrames do
      match ← applyFrame F cache f (mkApp mCanon a) with
      | .ok (rhs, step) =>
        let step' ← mkExpectedTypeHint step (← mkEq cur rhs)
        let (hit?, r') ← match rhs.cleanupAnnotations with
          | .app m' a' => enqueueRead m' a' step' reach
          | _ => enqueueVal rhs step' reach
        reach := r'
        if hit?.isSome then return (hit?, reach)
        advanced := true
      | .error (some p) => failed := failed.push (f.name, p)
      | .error none => pure ()
    -- 9. Unfold `let` / `unfoldDefs` / `Prod` projection on state `s` or memory `m`
    if let some m' ← stepStateDef? F.unfoldDefs mCanon then
      let nxt := mkApp m' a
      let step ← mkExpectedTypeHint (← mkEqRefl cur) (← mkEq cur nxt)
      let (hit?, r') ← enqueueRead m' a step reach
      reach := r'
      if hit?.isSome then return (hit?, reach)
      advanced := true
    -- 10. Reverse `WholeEq` edges (lower priority)
    for we in weqs do
      if !we.forward then
        let step ← mkCongrFun (← mkExpectedTypeHint we.proof (← mkEq mCanon we.rhs)) a
        let step' ← mkExpectedTypeHint step (← mkEq cur (mkApp we.rhs a))
        let (hit?, r') ← enqueueRead we.rhs a step' reach
        reach := r'
        if hit?.isSome then return (hit?, reach)
        advanced := true
    if !advanced then
      recordStuck cache cur failed
    else if !failed.isEmpty && reach.readList.size == qIdx && reach.values.isEmpty then
      recordStuck cache cur failed
  -- Deferred pass: `CellVal` equations whose address requires `omega`/`wram_omega` (`a = cv.addr`).
  let baseReads := reach.readList
  for (m, a, cur, pCur) in baseReads do
    let mCanon := canonMem m
    for (v, step) in ← matchingCellVals F cache mCanon a true do
      let step' ← mkExpectedTypeHint step (← mkEq cur v)
      let pTotal ← mkEqTrans pCur step'
      if let some hit ← checkTarget v pTotal then return (some hit, reach)
      reach := { reach with values := reach.values.push (v, pTotal) }
  return (none, reach)

/-- Try to connect two Nat expressions `lhs` and `rhs` when at least one is a memory read. -/
private meta def solveNatEq? (F : Facts) (cache : IO.Ref Cache) (lhs rhs : Expr) :
    MetaM (Option Expr) := do
  let lhs0 := lhs
  let rhs0 := rhs
  let lhs ← unfoldHeadDefs F.unfoldDefs lhs
  let rhs ← unfoldHeadDefs F.unfoldDefs rhs
  let finish (pf : Expr) : MetaM (Option Expr) := do
    return some (← mkExpectedTypeHint pf (← mkEq lhs0 rhs0))
  if !lhs.hasExprMVar && !rhs.hasExprMVar then
    if ← isDefEq lhs rhs then
      return ← finish (← mkEqRefl lhs)
  let lRead? := readMem? F lhs
  let rRead? := readMem? F rhs
  match lRead?, rRead? with
  | some (mL, aL), some (mR, aR) =>
    let tgtR? := if rhs.hasExprMVar then none else some rhs
    let (hit?, rL) ← exploreRead F cache mL aL (target? := tgtR?)
    if let some pf := hit? then return ← finish pf
    let tgtL? := if lhs.hasExprMVar then none else some lhs
    let (hitR?, rR) ← exploreRead F cache mR aR (target? := tgtL?)
    if let some pf := hitR? then return ← finish (← mkEqSymm pf)
    for (m1, a1, _, p1) in rL.readList do
      for (m2, a2, _, p2) in rR.readList do
        let eqMem := memKey m1 == memKey m2
        if eqMem || (!m1.hasExprMVar && !m2.hasExprMVar &&
            (← withReducible (isDefEq (canonMem m1) (canonMem m2)))) then
          if a1 == a2 || (← withReducible (isDefEq a1 a2)) then
            let p1' ← mkExpectedTypeHint p1 (← mkEq lhs (mkApp m1 a1))
            let p2' ← mkExpectedTypeHint p2 (← mkEq rhs (mkApp m1 a1))
            return ← finish (← mkEqTrans p1' (← mkEqSymm p2'))
          else
            let eqProp ← mkEq a1 a2
            if let some ha ← discharge F cache eqProp then
              let mid ← mkCongrArg (canonMem m1) ha
              let p1' ← mkExpectedTypeHint p1 (← mkEq lhs (mkApp (canonMem m1) a1))
              let p2' ← mkExpectedTypeHint p2 (← mkEq rhs (mkApp (canonMem m1) a2))
              return ← finish (← mkEqTrans p1' (← mkEqTrans mid (← mkEqSymm p2')))
    for (v1, p1) in rL.values do
      for (v2, p2) in rR.values do
        if !v1.hasExprMVar && !v2.hasExprMVar then
          if ← isDefEq v1 v2 then
            return ← finish (← mkEqTrans p1 (← mkEqSymm p2))
    return none
  | some (mL, aL), none =>
    let isOpenMVar := rhs.cleanupAnnotations.isMVar
    let target? := if rhs.hasExprMVar then none else some rhs
    let (hit?, rL) ← exploreRead F cache mL aL (target? := target?)
    if let some pf := hit? then return ← finish pf
    for (v, p) in rL.values do
      if isOpenMVar || !rhs.hasExprMVar then
        if ← isDefEq v rhs then
          return ← finish (← mkExpectedTypeHint p (← mkEq lhs rhs))
    if !rhs.hasExprMVar then
      for (v, p) in rL.values do
        if let some hv ← discharge F cache (← mkEq v rhs) then
          return ← finish (← mkEqTrans p hv)
      for (_, _, e, p) in rL.readList do
        if ← isDefEq e rhs then
          return ← finish (← mkExpectedTypeHint p (← mkEq lhs rhs))
    return none
  | none, some (mR, aR) =>
    let isOpenMVar := lhs.cleanupAnnotations.isMVar
    let target? := if lhs.hasExprMVar then none else some lhs
    let (hit?, rR) ← exploreRead F cache mR aR (target? := target?)
    if let some pf := hit? then return ← finish (← mkEqSymm pf)
    for (v, p) in rR.values do
      if isOpenMVar || !lhs.hasExprMVar then
        if ← isDefEq v lhs then
          return ← finish (← mkEqSymm (← mkExpectedTypeHint p (← mkEq rhs lhs)))
    if !lhs.hasExprMVar then
      for (v, p) in rR.values do
        if let some hv ← discharge F cache (← mkEq lhs v) then
          return ← finish (← mkEqTrans hv (← mkEqSymm p))
    return none
  | none, none => return none

/-- Single-path `simp` step used when memory reads/maps occur *inside* a compound expression
(e.g. `some (y.mem a) = some (x.mem a)` or `TableRep ... y.mem`). -/
private meta def frameSimpStep (F : Facts) (cache : IO.Ref Cache) (e : Expr) :
    SimpM Simp.Step := do
  if (← isMemType (← inferType e)) && isTrackedMem F e then
    let mut cur := e
    let mut proof? : Option Expr := none
    let mut visited : Std.HashSet Expr := {}
    let mut changed := false
    let push (proof? : Option Expr) (h : Expr) : MetaM (Option Expr) :=
      match proof? with
      | none => return some h
      | some p => return some (← mkEqTrans p h)
    repeat
      let k := canonMem cur
      if k != cur.cleanupAnnotations then
        cur := k
        changed := true
      let mK := memKey cur
      if visited.contains mK then break
      visited := visited.insert mK
      if let some (nxt, pf) ← stepHavocMem? cur then
        proof? ← push proof? (← mkExpectedTypeHint pf (← mkEq cur nxt))
        cur := nxt
        continue
      if let some we := (F.wholeEqs.getD mK #[]).reverse.find? (·.forward) then
        proof? ← push proof? (← mkExpectedTypeHint we.proof (← mkEq cur we.rhs))
        cur := we.rhs
        continue
      let mut execNext? := none
      for ef in (F.execFrames.getD mK #[]).reverse do
        match ← applyExecFrame F cache ef with
        | .ok (rhs, pf) => execNext? := some (rhs, pf); break
        | .error _ => pure ()
      if let some (rhs, pf) := execNext? then
        proof? ← push proof? (← mkExpectedTypeHint pf (← mkEq cur rhs))
        cur := rhs
        continue
      if let some nxt ← stepStateDef? F.unfoldDefs cur then
        cur := nxt
        changed := true
        continue
      break
    if proof?.isNone && !changed then return .continue
    return .visit { expr := cur, proof? }
  let some (m, a) := readMem? F e | return .continue
  let (_, r) ← exploreRead F cache m a
  if let some (v, pf) := r.values[0]? then
    return .done { expr := v, proof? := some pf }
  if !r.readList.isEmpty then
    let (lastM, lastA, lastE, lastPf) := r.readList.back!
    let canonE := mkApp (canonMem lastM) lastA
    if canonE != e then
      let pf ← if canonE == lastE then pure lastPf
        else mkExpectedTypeHint lastPf (← mkEq e canonE)
      return .done { expr := canonE, proof? := some pf }
  return .continue

/-- Decompose a goal through `And`, `Prop`-valued structures, and user-selected `unfoldDefs`
`Prop` definitions, plus `Modifies` / `Set.EqOn` / universal quantifiers. -/
meta partial def decompose (unfoldDefs : NameSet) (g : MVarId) :
    MetaM (Array MVarId) := g.withContext do
  let (_, g) ← g.intros
  g.withContext do
    let tgt0 ← instantiateMVars (← g.getType)
    let tgtZ := headZeta tgt0
    let g ← if tgtZ != tgt0 then g.replaceTargetDefEq tgtZ else pure g
    let tgt ← instantiateMVars (← g.getType)
    if tgt.isAppOfArity ``Modifies 3 then
      if let some tgt' ← withAtLeastTransparency .default <| unfoldDefinition? tgt then
        return ← decompose unfoldDefs (← g.replaceTargetDefEq tgt')
    if tgt.isAppOfArity ``Set.EqOn 5 then
      if let some tgt' ← withAtLeastTransparency .default <| unfoldDefinition? tgt then
        return ← decompose unfoldDefs (← g.replaceTargetDefEq tgt')
    if let .const c _ := tgt.getAppFn then
      if ← isMatcher c then
        let tgt' ← withAtLeastTransparency .default <| whnf tgt
        if tgt' != tgt then
          return ← decompose unfoldDefs (← g.replaceTargetDefEq tgt')
    if let .const c _ := tgt.getAppFn then
      if unfoldDefs.contains c then
        if let some tgt' ← unfoldHeadDef? unfoldDefs tgt then
          return ← decompose unfoldDefs (← g.replaceTargetDefEq tgt')
    let tgtW ← whnfR tgt
    let .const c _ := tgtW.getAppFn | return #[g]
    let env ← getEnv
    if c == ``And then
      let some gs ← observing? g.constructor | return #[g]
      return (← gs.toArray.mapM (decompose unfoldDefs)).flatten
    unless c != ``Iff && isStructure env c && !isClass env c do return #[g]
    let some info := env.find? c | return #[g]
    unless info.type.getForallBody.isProp do return #[g]
    let some gs ← observing? g.constructor | return #[g]
    return (← gs.toArray.mapM (decompose unfoldDefs)).flatten

/-- Try to close a single atomic subgoal `g`. Returns `none` on success or `some (orig, left)`
plus stuck entries for diagnostics. -/
meta partial def closeAtomic (unfoldDefs : NameSet)
    (hints : Array (Expr × MessageData × Bool)) (g : MVarId) :
    MetaM (Option (Expr × Expr × Array (Expr × Array (MessageData × Expr)))) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let F ← scan unfoldDefs hints
  let derived ← collectDerivedArith
  let cache ← IO.mkRef ({ derivedArith := derived } : Cache)
  if let some h ← WP.Exec.assumption? tgt then
    g.assign h
    return none
  if let some (α, lhs, rhs) := tgt.cleanupAnnotations.eq? then
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if ← isMemType α then
      if let some pf ← findWholeMemEq? F cache lhs rhs then
        g.assign (← mkExpectedTypeHint pf tgt)
        return none
      let saved ← saveState
      if let some gBody ← observing? (do
        let [g1] ← g.apply (mkConst ``funext [Level.one, Level.one]) | failure
        let (_, g1') ← g1.intro1
        return g1') then
        if (← closeAtomic unfoldDefs hints gBody).isNone then
          return none
      saved.restore
      return some (tgt, tgt, (← cache.get).stuck)
    if α.isConstOf ``Nat then
      if let some pf ← solveNatEq? F cache lhs rhs then
        g.assign (← mkExpectedTypeHint pf tgt)
        return none
  let ctx ← Simp.mkContext (config := { maxSteps := 20000 })
    (congrTheorems := ← getSimpCongrTheorems)
  let res := (← Simp.main tgt ctx (methods := { pre := frameSimpStep F cache })).1
  let left := (← instantiateMVars res.expr).cleanupAnnotations
  if left != tgt.cleanupAnnotations then
    let g' ← applySimpResultToTarget g tgt res
    let tgt' ← instantiateMVars (← g'.getType)
    if let some h ← WP.Exec.assumption? tgt' then
      g'.assign h
      return none
    if let some (_, a, b) := tgt'.cleanupAnnotations.eq? then
      if ← isDefEq a b then
        g'.assign (← mkEqRefl a)
        return none
    if let some (α, _, _) := tgt'.cleanupAnnotations.eq? then
      if α.isConstOf ``Nat then
        if let some h ← discharge F cache tgt' then
          g'.assign h
          return none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← withReducible (isDefEq d.type tgt') then
        g'.assign d.toExpr
        return none
    return some (tgt, tgt', (← cache.get).stuck)
  if let some (α, lhs, rhs) := tgt.cleanupAnnotations.eq? then
    if α.isConstOf ``Nat then
      let bestL ← match readMem? F lhs with
        | some (m, a) =>
          let (_, r) ← exploreRead F cache m a
          pure (if let some (v, _) := r.values[0]? then v else (r.readList.back!.2.2.1))
        | none => pure lhs
      let bestR ← match readMem? F rhs with
        | some (m, a) =>
          let (_, r) ← exploreRead F cache m a
          pure (if let some (v, _) := r.values[0]? then v else (r.readList.back!.2.2.1))
        | none => pure rhs
      if bestL != lhs || bestR != rhs then
        return some (tgt, ← mkEq bestL bestR, (← cache.get).stuck)
  return some (tgt, tgt, (← cache.get).stuck)

/-- Attempt to close `g` with `mem_frame`, restoring the state and returning `false` on failure. -/
meta def tryProve (g : MVarId) (unfoldDefs : NameSet := {})
    (hints : Array (Expr × MessageData × Bool) := #[]) : MetaM Bool := do
  let saved ← saveState
  let ok ← try
    let subgoals ← decompose unfoldDefs g
    let mut good := true
    for sg in subgoals do
      if (← closeAtomic unfoldDefs hints sg).isSome then
        good := false
        break
    pure good
  catch _ => pure false
  unless ok do saved.restore
  return ok

/-- Elaborate user-supplied `mem_frame [t₁, ...]` items into definition names to unfold and
explicit proof terms / polymorphic lemmas. -/
private meta def elabHints (args : Array Term) :
    TacticM (NameSet × Array (Expr × MessageData × Bool)) := do
  let mut defs : NameSet := {}
  let mut terms : Array (Expr × MessageData × Bool) := #[]
  let env ← getEnv
  for stx in args do
    let raw := stx.raw
    if raw.isIdent then
      let n ← try
        realizeGlobalConstNoOverloadWithInfo raw
      catch _ => pure Name.anonymous
      if n != Name.anonymous then
        if let some info := env.find? n then
          match info with
          | .defnInfo _ | .opaqueInfo _ =>
            defs := defs.insert n
            continue
          | .thmInfo _ =>
            let c ← mkConstWithFreshMVarLevels n
            terms := terms.push (c, m!"{.ofConstName n}", true)
            continue
          | _ => pure ()
    let e ← withMainContext <| elabTerm stx none
    let e ← instantiateMVars e
    terms := terms.push (e, m!"{stx}", true)
  return (defs, terms)

end MemFrame

/-- `mem_frame` proves a fact about memory after a sequence of stores or calls from the frames
among the hypotheses:

* an exact memory equality `z.mem = x.mem` (or `y.mem = m`);
* a single cell read `z.mem a = v`, `z.mem a = x.mem a`, or `z.mem a = ?v` (inferring `?v`);
* a quantified frame `∀ a, P₁ a → … → z.mem a = x.mem a`, `Set.EqOn z.mem x.mem R`, or
  `Modifies F x.mem z.mem`;
* an indexed slice equality `∀ i, P i → z.mem (base + i) = f i`;
* a conjunction or `Prop`-valued structure of any of the above (splitting fields recursively).

Optional hints `mem_frame [h₁, h₂, DefName]` supply either extra fact terms / polymorphic frame
lemmas (such as `insertMem_of_outside`) or `def` names to unfold when splitting goals and
hypotheses (such as `TableRep` or `restoreAfterHashInitData`).

It follows each memory map or read back through:

* whole-memory equations `h : y.mem = x.mem` and state equations `h : y = x`;
* store-free execution hypotheses `he : Exec w c x y n` / `ExecWithin w c x y T` (or any `J`
  with a `J.mem_eq` lemma), deciding `Code.StoreFree c` in the kernel when `c` is closed and
  structurally when `c` contains parameters;
* pointwise frames `∀ a, P a → y.mem a = x.mem a`, `Set.EqOn`, and `Modifies`;
* `Data.set`, `Data.comap`, `Data.extend`, `Data.havoc`, `Data.write`, `Function.update`, and
  `let`-bound states;
* concrete cell values `h : x.mem a = v` and indexed slice equations
  `∀ i, P i → x.mem (base + i) = f i`.

Frame premises (`a ≠ b`, `a < base ∨ base + n ≤ a`, `a ∉ b.footprint`, `a ∉ Finset.Ico l u`,
`a ∈ Set.Ico l u`, …) are discharged by closed evaluation, hypotheses, `omega`, and silent
`@[wram_arith]` unfolding without triggering `linter.unnecessaryWramOmega`. -/
syntax (name := memFrame) "mem_frame" (" [" term,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| mem_frame $[[$args,*]]?) => withMainContext do
    recordExtraModUse (isMeta := false) `Init.Omega
    let argArr := (args.map (·.getElems)).getD #[]
    let (unfoldDefs, hints) ← MemFrame.elabHints argArr
    let g0 ← getMainGoal
    let subgoals ← MemFrame.decompose unfoldDefs g0
    let mut failures :
        Array (MVarId × Expr × Expr × Array (Expr × Array (MessageData × Expr))) := #[]
    for g in subgoals do
      if let some (orig, left, stuck) ← MemFrame.closeAtomic unfoldDefs hints g then
        failures := failures.push (g, orig, left, stuck)
    unless failures.isEmpty do
      let mut msg := m!"mem_frame: could not prove"
      for (g, orig, left, stuck) in failures do
        let part ← g.withContext do
          let mut sub := indentExpr orig
          unless left == orig do
            sub := sub ++ m!"\nFollowing the frames leaves{indentExpr left}"
          for (e, failed) in stuck do
            if failed.isEmpty then
              sub := sub ++ m!"\nNo hypothesis gives `{e}` or a frame of its memory."
            else
              for (f, p) in failed do
                sub := sub ++ m!"\n`{f}` does not give `{e}`: it needs{indentExpr p}"
          addMessageContext sub
        msg := msg ++ part
      throwError msg
    replaceMainGoal []

end Cslib.WordRAM

end
