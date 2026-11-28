/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Consequence

/-!
# The `realize` tactic

The tactic is available inside `Cslib.WordRAM`, or after `open Cslib.WordRAM` or
`open scoped Cslib.WordRAM`. Importing this module alone does not activate its syntax.

`realize` proves a goal `Realizes B p input output safe work` for a memory client `p`. Its core
lowering engine (`Cslib.Tactic.Realize.elabRealize`) is parameterized by a `Combinators` record so
`CslibFrontier.Computability.WordRAM.Realization.BoundedTactic` synthesizes `RealizesBounded`
certificates directly in one pass without post-hoc proof translation. It walks the client syntax,
unfolding definitions, with one rule per form:

* `bind`: compose the component work at the actual reply and next memory, absorbing fixed
  control work. After each bind the live words are the previous ones followed by the answer's
  encoding (`WordEncoding`); `realize` keeps this layout itself.
* `f <$> p` or `p.map f`: over a `bind`, `pure`, `if` or another map, the map is pushed into
  the client (`PFunctor.FreeM.map_bind`), so that only returned values are mapped and the answer
  of `p` needs no word encoding. Over a linked client it moves into the source
  (`PFunctor.FreeM.liftM_map`), where the same rules apply. Over any other client (a certified
  method, a query, a loop) it is certified as `do let a ← p; return f a`, reusing the certificate
  for `p`.
* `pure`: `Realizes.pure₀`, with each result word certified by a `GlueComputable` proof assembled
  from the closure rules of `CslibFrontier.Computability.WordRAM.Glue`: projections, constants, and
  the exact- or standard-basis arithmetic and bitwise operations. Conditional values, natural
  minima/maxima and Boolean decisions are lifted to paid branches, including inside returned
  constructors; only the selected alternative contributes fit and definedness conditions.
* the four memory queries: `Realizes.read`, `write`, `alloc` and `allocDirty`.
* `DataStructure.link` / `PFunctor.FreeM.liftM`: lowers linked free-monad source programs
  incrementally, matching local certificates on linked sub-calls before unfolding them, distributing
  monadic binds, result maps and conditional branches, and reducing record layout addresses to word
  arithmetic. A map in the source is pushed into it like a map of a memory client; over a
  certified sub-call, a source operation or an opaque source it moves out of the link
  (`PFunctor.FreeM.liftM_map`) and is certified as a bind.
* a method with a local certificate: `Realizes.reindex`, selecting its arguments from live words
  before unfolding its implementation (across tuples, data structures, and finite word vectors).
  Non-live scalar coordinates inside composite arguments are staged individually by certified glue;
  other computed arguments fall back to whole-argument staging in the method's input encoding,
  retaining the method's work.
* `if` on natural `=`, `≠`, `<`, `≤`, `>` or `≥`, combined with `¬`, `∧` and `∨`:
  `Realizes.branch` (`branch₀` for zero component work), retaining short-circuiting.
  Named guards unfold to these forms.
* `match` on an optional word or word pair: the client equals the branch on its presence tag
  (`Realizes.congr`, proved by cases).
* `iterate step D n a`: `Realizes.iterateRuntime`, after adapting `D` and any captured live words
  to the whole environment. The source and reached-state domain and `iterationWork` are transported
  back to the client's original loop.
* `boundedWhile G step D n a`: `Realizes.whileBounded`. The guard `G D r` may be `a = b`, `a < b`,
  `a > b`, `a ≠ 0` (tested as `0 < a`), or `a + 1 ≤ b` (tested as `a < b`), with any decidability
  instance, over the live words and the state's words. An operand independent of the state is
  computed before the loop. The cutoff `n` is a ghost bound and is not computed.
  The certificate is transported to the client's guard, step and `D` (`boundedWhile_congr`,
  `whileSafe_imp`), so the loop's domain is `whileSafe G step …` in the client's terms, under
  the loop's valid history (`Realizes.consequence_valid`), ready for `whileSafe_of_measure`.

Operands are located among the live words by definitional equality. An operand that is not a
live word is first computed by an inserted `pure`, preserving the program by a checked equality.

Exact subtraction, division and remainder add their definedness conditions to the visible
domain. The common glue envelope is the maximum of every intermediate value; `realize` proves
that it fits from the fit of the live words, from the domain, and from the fit of the values it
cannot derive, which become the visible fit conditions. A value is derived when another fitting
value dominates it, for example `a - b` and `b` by `a`, or the summands by a sum.

Fixed glue and finite control work is absorbed (`Realizes.mono_mul`). Called methods retain
their work; binds sum it and branches select only the reached alternative's work. Loops retain
`iterationWork` or `whileWork`, including one control unit per reached iteration. A zero-work
body that begins with a query keeps the existing query-paid rule (`iterate₀` or `while₀`).
Intermediate domains and grades are stated in the client's own terms, with the replies of
earlier queries written as `s.mem a`, `s.frontier`, updated memories, or the interpreter's result
of a called method; a loop contributes its `iterationSafe` or `whileSafe` domain.

After composition, `realize` introduces `w d s hwords hmem h`: the word width, the environment,
memory, input fits, memory well-formedness and the goal's domain. Nonzero generated work also
adds the client's valid history as `hv`. It splits conjunctions and `if`s of the domain, then leaves
the generated work's comparison with the requested budget under the same entry assumptions.
Zero work and definitionally matching budgets close automatically. Local method certificates
are tried in context order; the remaining rule selection follows the client syntax, without
searching for bounds. An unsupported form is reported with its subterm.

`realize [certificate₁, …]` first adds the supplied proof terms as local facts in list order,
then runs the same tactic. Existing local certificates retain priority.

Each certificate is stated for the client form as written, with its domain in the client's terms
(`certify`), so certificates compose syntactically. A bind's continuation domain is stated at the
first client's reply and next memory in closed form (`Realizes.bind₀_of_run`), not at the
interpreter's run. The kernel checks, locally at each form, that the rule's statement agrees.

## Main definitions

* `Cslib.Tactic.Realize.Combinators`: proof-combinator bundle for a realization judgment.
* `Cslib.Tactic.Realize.elabRealize`: judgment-parametric elaboration entry point.
* `realize`: the tactic.
-/

public meta section

namespace Cslib.Tactic.Realize

open Lean Meta Elab Tactic Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- Proof-combinator names parameterizing `elabRealize` over `Realizes` or `RealizesBounded`. -/
structure Combinators where
  /-- Display label for error messages (`"Realizes"` or `"RealizesBounded"`). -/
  label : String
  /-- The 10-argument realization predicate. -/
  cert : Name
  /-- Consequence, congruence, reindexing and constant-factor absorption rules. -/
  (consequenceWork consequenceValid congr reindex monoMul : Name)
  /-- Pure return and monadic bind rules. -/
  (pure0 bind0OfRun bind : Name)
  /-- Primitive memory-operation rules. -/
  (read write alloc allocDirty : Name)
  /-- Conditional branch rules. -/
  (branch0 branch : Name)
  /-- Bounded iteration and `boundedWhile` loop rules. -/
  (iterate0 iterateRuntime while0 whileBounded : Name)

/-- Combinator bundle for ordinary `Realizes` goals. -/
private def unboundedCombinators : Combinators where
  label := "Realizes"
  cert := ``Realizes
  consequenceWork := ``Realizes.consequence_work
  consequenceValid := ``Realizes.consequence_valid
  congr := ``Realizes.congr
  reindex := ``Realizes.reindex
  monoMul := ``Realizes.mono_mul
  pure0 := ``Realizes.pure₀
  bind0OfRun := ``Realizes.bind₀_of_run
  bind := ``Realizes.bind
  read := ``Realizes.read
  write := ``Realizes.write
  alloc := ``Realizes.alloc
  allocDirty := ``Realizes.allocDirty
  branch0 := ``Realizes.branch₀
  branch := ``Realizes.branch
  iterate0 := ``Realizes.iterate₀
  iterateRuntime := ``Realizes.iterateRuntime
  while0 := ``Realizes.while₀
  whileBounded := ``Realizes.whileBounded

/-- Run `act`, rolling back state and returning `none` on `none` or non-interrupt errors. -/
private def tryBacktrack? {m : Type → Type} {s α : Type} [Monad m] [MonadExcept Exception m]
    [MonadBacktrack s m] (act : m (Option α)) : m (Option α) := do
  let saved ← saveState
  try
    let res ← act
    if res.isNone then restoreState saved
    return res
  catch ex =>
    if ex.isInterrupt then throw ex
    restoreState saved
    return none

/-- The live words of a realization environment. -/
private structure Env where
  /-- The environment type. -/
  ty : Expr
  /-- The number of live words. -/
  k : Nat
  /-- The encoding `ty ↪ (Fin k → ℕ)`. -/
  input : Expr
  /-- `atoms[i]` is `fun d => input d i` in weak-head normal form. -/
  atoms : Array Expr

/-- A certificate built by `realize`. -/
private structure Out where
  /-- A proof of the active realization predicate on `(B, prog, input, output, safe, work)`. -/
  proof : Expr
  /-- The output encoding. -/
  output : Expr
  /-- The domain `fun w d s => …`, in the client's terms, definitionally equal to the proof's. -/
  safe : Expr
  /-- The local work in the client's terms, definitionally equal to the proof's. -/
  work : Expr

/-- `(i : Fin n)` as a numeral. -/
private def finLit (n i : Nat) : MetaM Expr :=
  mkNumeral (mkApp (mkConst ``Fin) (mkNatLit n)) i

/-- Evaluate a literal `Fin` index to `Nat` when concrete. -/
private def evalFinLit? (idx : Expr) : MetaM (Option Nat) := do
  if idx.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (idx.getArg! 1).rawNatLit? then return some n
  let idx' ← whnf idx
  if idx'.isAppOfArity ``Fin.mk 3 then
    return ← (evalNat (idx'.getArg! 1)).run
  return none

/-- Extract the `j`-th element of a `Matrix.vecCons` spine `![x₀, …, x_{k-1}]`. -/
private def extractVecElem? (vec : Expr) : Nat → Option Expr
  | 0 => if vec.isAppOfArity ``Matrix.vecCons 4 then some (vec.getArg! 2) else none
  | j + 1 =>
    if vec.isAppOfArity ``Matrix.vecCons 4 then extractVecElem? (vec.getArg! 3) j else none

/-- Reduce a single `(![x₀, …, x_{k-1}] j)` application when `j` is a concrete `Fin` index. -/
private def reduceVecApp? (sub : Expr) : MetaM (Option Expr) := do
  unless sub.isApp do return none
  let fn := sub.appFn!
  unless fn.isAppOfArity ``Matrix.vecCons 4 do return none
  let some j ← evalFinLit? sub.appArg! | return none
  return extractVecElem? fn j

/-- Reduce `(![x₀, …, x_{k-1}] j)` applications on concrete `Fin` indices. -/
private def reduceFinVecApps (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun sub => do
    if let some elem ← reduceVecApp? sub then return .done elem
    return .continue)

/-- The number of words of an encoding `α ↪ (Fin l → ℕ)`. -/
private def encodingWidth (enc : Expr) : MetaM Nat := do
  let ty ← instantiateMVars (← inferType enc)
  let some (_, tgt) := ty.app2? ``Function.Embedding
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let .forallE _ dom _ _ ← whnf tgt
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let some n := (← whnf dom).app1? ``Fin
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let n ← instantiateMVars n
  if let some l ← (evalNat n).run then return l
  let some l ← (evalNat (← whnf n)).run
    | throwError "realize: the encoding width is not a numeral in{indentExpr ty}"
  return l

/-- The atoms of `enc x`, for `x` an expression in the environment variable. -/
private def encodingAtoms (enc x : Expr) (l : Nat) : MetaM (Array Expr) :=
  (Array.range l).mapM fun j => do
    whnf (mkApp (← mkAppM ``DFunLike.coe #[enc, x]) (← finLit l j))

/-- Locate an expression among the live words: syntactically after `whnf`, as the live words are
themselves in weak-head normal form, and otherwise by definitional equality. -/
private def findAtom (atoms : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  if let some i := atoms.findIdx? (· == e') then return some i
  for h : i in [0:atoms.size] do
    if ← withNewMCtxDepth (isDefEq e' atoms[i]) then return some i
  return none

/-- Extract field `idx` when `target` is a full application of constructor `ctorName`. -/
private def ctorField? (env : Environment) (ctorName : Name) (idx : Nat)
    (target : Expr) : Option Expr := do
  guard (target.getAppFn.isConstOf ctorName)
  let .ctorInfo ci ← env.find? ctorName | none
  let args := target.getAppArgs
  guard (args.size == ci.numParams + ci.numFields && ci.numParams + idx < args.size)
  some args[ci.numParams + idx]!

/-- Reduce structure projections on constructors and literal `Matrix.vecCons` lookups everywhere. -/
private def reduceProjections (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun sub => do
    if let .proj s i target := sub then
      if isStructure env s then
        if let some field := ctorField? env (getStructureCtor env s).name i target then
          return .done field
    if let some fnName := sub.getAppFn.constName? then
      if let some info := env.getProjectionFnInfo? fnName then
        if !info.fromClass && sub.getAppNumArgs ≥ info.numParams + 1 then
          let subArgs := sub.getAppArgs
          if let some field := ctorField? env info.ctorName info.i subArgs[info.numParams]! then
            return .done (mkAppN field (subArgs.extract (info.numParams + 1) subArgs.size))
    if let some elem ← reduceVecApp? sub then return .done elem
    return .continue)

/-- Extract the base expression `x` if `fieldExpr` is the `idx`-th projection of structure `s`
from `x`. -/
private def structProjBase? (env : Environment) (s : Name) (ctorName : Name)
    (numParams idx : Nat) (fieldExpr : Expr) : Option Expr :=
  let fieldExpr := fieldExpr.consumeMData
  match fieldExpr with
  | .proj s' i base => if s' == s && i == idx then some base.consumeMData else none
  | _ =>
    if let some fnName := fieldExpr.getAppFn.constName? then
      if let some info := env.getProjectionFnInfo? fnName then
        if !info.fromClass && info.ctorName == ctorName && info.i == idx &&
            fieldExpr.getAppNumArgs == numParams + 1 then
          some fieldExpr.appArg!.consumeMData
        else none
      else none
    else none

/-- Rewrite raw `Expr.proj` nodes into named projection functions and eta-contract
`Ctor.mk params (proj₀ x) … (proj_{m-1} x)` back to `x` in one bottom-up pass so syntactic tactics
such as `omega` see the same projection terms as user hypotheses. -/
private def etaContractStructures (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun sub => do
    if let .proj s idx base := sub then
      if let some sInfo := getStructureInfo? env s then
        if h : idx < sInfo.fieldNames.size then
          if let some projFn := getProjFnForField? env s sInfo.fieldNames[idx] then
            if let some pInfo := env.getProjectionFnInfo? projFn then
              if !pInfo.fromClass then
                if let some fnApp ← tryBacktrack? (do
                    let fnApp ← mkAppM projFn #[base]
                    if ← withNewMCtxDepth (isDefEq sub fnApp) then return some fnApp
                    return none) then
                  return .done fnApp
    if let some ctorName := sub.getAppFn.constName? then
      if let some (.ctorInfo ci) := env.find? ctorName then
        if isStructure env ci.induct && ci.induct != ``Prod && ci.induct != ``Sigma &&
            ci.numFields > 0 then
          let args := sub.getAppArgs
          if args.size == ci.numParams + ci.numFields then
            if let some base := structProjBase? env ci.induct ctorName ci.numParams 0
                args[ci.numParams]! then
              let allMatch := (List.range ci.numFields).all fun i =>
                structProjBase? env ci.induct ctorName ci.numParams i
                  args[ci.numParams + i]! == some base
              if allMatch then
                if ← withNewMCtxDepth (isDefEq sub base) then
                  return .done base
    return .continue)

/-- `φ₀ ∧ (φ₁ ∧ … φₙ)`, or `True`. -/
private def conj : List Expr → Expr
  | [] => mkConst ``True
  | [f] => f
  | f :: fs => mkAnd f (conj fs)

/-- Project the conjunct at `pos` out of a proof of `conj` of `size` facts. -/
private def conjunct (h : Expr) (size pos : Nat) : MetaM Expr := do
  let mut h := h
  for _ in [0:pos] do h ← mkAppM ``And.right #[h]
  if pos + 1 == size then return h
  mkAppM ``And.left #[h]

/-! ### Word glue -/

/-- The supported glue operations. -/
private inductive GOp
  | add | sub | mul | div | mod | and | or | xor | shiftLeft | shiftRight

/-- The glue rule name for an operation in the exact or standard basis. -/
private def GOp.rule (exact : Bool) : GOp → Name
  | .add => if exact then ``GlueComputable.add else ``GlueComputable.add_standard
  | .sub => if exact then ``GlueComputable.sub else ``GlueComputable.sub_standard
  | .mul => if exact then ``GlueComputable.mul else ``GlueComputable.mul_standard
  | .div => if exact then ``GlueComputable.div else ``GlueComputable.div_standard
  | .mod => if exact then ``GlueComputable.mod else ``GlueComputable.mod_standard
  | .and => if exact then ``GlueComputable.and else ``GlueComputable.and_standard
  | .or => if exact then ``GlueComputable.or else ``GlueComputable.or_standard
  | .xor => if exact then ``GlueComputable.xor else ``GlueComputable.xor_standard
  | .shiftLeft =>
    if exact then ``GlueComputable.shiftLeft else ``GlueComputable.shiftLeft_standard
  | .shiftRight =>
    if exact then ``GlueComputable.shiftRight else ``GlueComputable.shiftRight_standard

/-- The operator's heterogeneous-operation function. -/
private def GOp.fn : GOp → Name
  | .add => ``HAdd.hAdd | .sub => ``HSub.hSub | .mul => ``HMul.hMul | .div => ``HDiv.hDiv
  | .mod => ``HMod.hMod | .and => ``HAnd.hAnd | .or => ``HOr.hOr | .xor => ``HXor.hXor
  | .shiftLeft => ``HShiftLeft.hShiftLeft | .shiftRight => ``HShiftRight.hShiftRight

/-- Whether the result is at most the left operand. -/
private def GOp.belowLeft : GOp → Bool
  | .sub | .div | .mod | .and | .shiftRight => true
  | _ => false

/-- A glue expression over the live words. -/
private inductive GNode
  /-- A live word. -/
  | reg (i : Nat) (user : Expr)
  /-- A value independent of the environment. -/
  | const (c : Expr) (zero : Bool)
  /-- A binary operation. -/
  | bin (op : GOp) (user : Expr) (a b : GNode)

/-- The expression in the client's terms. -/
private def GNode.user : GNode → Expr
  | .reg _ u | .const u _ | .bin _ u _ _ => u

/-- Recognize a binary operation on natural numbers. -/
private def binOp? (e : Expr) : Option (GOp × Expr × Expr) :=
  [GOp.add, .sub, .mul, .div, .mod, .and, .or, .xor, .shiftLeft, .shiftRight].findSome? fun op =>
    if e.isAppOfArity op.fn 6 && (e.getArg! 0).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5)
    else none

/-- Parse a word-valued expression over the live words. -/
private partial def analyze (atoms : Array Expr) (d : Expr) (e : Expr) : MetaM GNode := do
  if let some i ← findAtom atoms e then return .reg i e
  if !e.containsFVar d.fvarId! then
    return .const e (← withNewMCtxDepth (isDefEq e (mkNatLit 0)))
  if let some (op, a, b) := binOp? e then
    return .bin op e (← analyze atoms d a) (← analyze atoms d b)
  let e' ← whnfR e
  if e' != e then return ← analyze atoms d e'
  throwError "realize: cannot compute{indentExpr e}\nfrom the live words{indentD
    (MessageData.joinSep (atoms.toList.map fun a => m!"{a}") ", ")}"

/-- A glue node numbered in depth-first order, with its value over the word vector. -/
private inductive ANode
  /-- A live word. -/
  | reg (idx : Nat) (val : Expr) (i : Nat)
  /-- A constant. -/
  | const (idx : Nat) (val : Expr) (zero : Bool)
  /-- A binary operation; `dom` numbers its definedness condition, if any. -/
  | bin (idx : Nat) (val : Expr) (op : GOp) (dom : Option Nat) (a b : ANode)

/-- The value over the word vector. -/
private def ANode.val : ANode → Expr
  | .reg _ v _ | .const _ v _ | .bin _ v .. => v

/-- The values of all nodes in depth-first order and the definedness conditions, over the word
vector and in the client's terms. -/
private structure Annot where
  /-- Node values over the word vector. -/
  vals : Array Expr := #[]
  /-- Definedness conditions over the word vector. -/
  domV : Array Expr := #[]
  /-- Definedness conditions in the client's terms. -/
  domU : Array Expr := #[]

/-- Number the nodes and compute their values over the word vector `v`. -/
private partial def annotate (exact : Bool) (k : Nat) (v : Expr) : GNode → StateT Annot MetaM ANode
  | .reg i _ => do
    let val := mkApp v (← finLit k i)
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push val }
    return .reg idx val i
  | .const c zero => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push c }
    return .const idx c zero
  | .bin op _ a b => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push default }
    let a' ← annotate exact k v a
    let b' ← annotate exact k v b
    let val ← mkAppM op.fn #[a'.val, b'.val]
    modify fun st => { st with vals := st.vals.set! idx val }
    let dom? ← if exact then
        match op with
        | .sub => pure (some (← mkAppM ``LE.le #[b'.val, a'.val],
            ← mkAppM ``LE.le #[b.user, a.user]))
        | .div | .mod => pure (some (← mkAppM ``Ne #[b'.val, mkNatLit 0],
            ← mkAppM ``Ne #[b.user, mkNatLit 0]))
        | _ => pure none
      else pure none
    let dom ← match dom? with
      | some (fv, fu) => do
        let n := (← get).domV.size
        modify fun st => { st with domV := st.domV.push fv, domU := st.domU.push fu }
        pure (some n)
      | none => pure none
    return .bin idx val op dom a' b'

/-- The node's value in the client's terms, by depth-first number. -/
private partial def userVals (g : GNode) (acc : Array Expr := #[]) : Array Expr :=
  match g with
  | .reg _ u => acc.push u
  | .const c _ => acc.push c
  | .bin _ u a b => userVals b (userVals a (acc.push u))

/-- The nodes whose fit is a visible condition: `covered` says that a dominating value fits. -/
private partial def needNodes (exact : Bool) (n : ANode) (covered : Bool)
    (acc : Array Nat := #[]) : Array Nat :=
  match n with
  | .reg .. => acc
  | .const idx _ zero => if zero || covered then acc else acc.push idx
  | .bin idx _ op _ a b =>
    let acc := if op.belowLeft || covered then acc else acc.push idx
    match op with
    | .add | .or =>
      needNodes exact b true (needNodes exact a true acc)
    | .shiftLeft => needNodes exact b false (needNodes exact a true acc)
    | .sub => needNodes exact b exact (needNodes exact a false acc)
    | _ => needNodes exact b false (needNodes exact a false acc)

/-- Fit proofs of all nodes, indexed by depth-first number, mirroring `needNodes`. `self?` is the
node's fit from a dominating value. -/
private partial def fitProofs (exact : Bool) (k : Nat) (w hregs hdom hneed : Expr) (ndom : Nat)
    (needIdx : Array Nat) (n : ANode) (self? : Option Expr) :
    StateT (Array Expr) MetaM Expr := do
  let fitNeed (idx : Nat) : MetaM Expr := do
    let some pos := needIdx.findIdx? (· == idx) | throwError "realize: internal fit error"
    conjunct hneed needIdx.size pos
  let fitLe (p h : Expr) : MetaM Expr := mkAppM ``Cslib.WordRAM.Fits.of_le #[p, h]
  let record (idx : Nat) (p : Expr) : StateT (Array Expr) MetaM Expr := do
    modify fun acc => acc.set! idx p
    return p
  match n with
  | .reg idx _ i => record idx (mkApp hregs (← finLit k i))
  | .const idx _ zero =>
    if zero then
      record idx (← mkAppM ``Cslib.WordRAM.fits_zero #[w])
    else match self? with
      | some p => record idx p
      | none => record idx (← fitNeed idx)
  | .bin idx _ op dom a b =>
    if op.belowLeft then
      let pa ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
      let pbDom ← match op, dom with
        | .sub, some di => pure (some (← fitLe pa (← conjunct hdom ndom di)))
        | _, _ => pure none
      let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b pbDom
      let le ← match op with
        | .sub => mkAppM ``Nat.sub_le #[a.val, b.val]
        | .div => mkAppM ``Nat.div_le_self #[a.val, b.val]
        | .mod => mkAppM ``Nat.mod_le #[a.val, b.val]
        | .and => mkAppOptM ``Nat.and_le_left #[a.val, b.val]
        | _ => mkAppM ``Nat.shiftRight_le #[a.val, b.val]
      record idx (← fitLe pa le)
    else
      let self ← match self? with
        | some p => pure p
        | none => fitNeed idx
      match op with
      | .add =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppM ``Nat.le_add_right #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppM ``Nat.le_add_left #[b.val, a.val])))
      | .or =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.left_le_or #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppOptM ``Nat.right_le_or #[a.val, b.val])))
      | .shiftLeft =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.le_shiftLeft #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      | _ =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      record idx self

/-- `max` on natural numbers through the linear order, as in `le_max_left` and `max_lt`. -/
private def natMax : MetaM Expr := do
  let nat := mkConst ``Nat
  mkAppOptM ``Max.max #[nat, ← mkAppOptM ``LinearOrder.toMax #[nat, none]]

/-- `max n₀ (max n₁ … nₘ)` from position `i`. -/
private partial def maxChain (maxFn : Expr) (vals : Array Expr) (i : Nat := 0) : Expr :=
  if i + 1 ≥ vals.size then vals[i]! else mkApp2 maxFn vals[i]! (maxChain maxFn vals (i + 1))

/-- `vals[pos] ≤ maxChain vals i`. -/
private partial def memProof (maxFn : Expr) (vals : Array Expr) (pos : Nat) (i : Nat := 0) :
    MetaM Expr := do
  if i + 1 ≥ vals.size then return ← mkAppM ``le_refl #[vals[i]!]
  if pos == i then return ← mkAppM ``le_max_left #[vals[i]!, maxChain maxFn vals (i + 1)]
  mkAppOptM ``le_max_of_le_right #[none, none, none, vals[i]!, none,
    ← memProof maxFn vals pos (i + 1)]

/-- `Fits w (maxChain vals i)` from the fit of every value. -/
private partial def fitChain (fits : Array Expr) (i : Nat := 0) : MetaM Expr := do
  if i + 1 ≥ fits.size then return fits[i]!
  mkAppM ``max_lt #[fits[i]!, ← fitChain fits (i + 1)]

/-- The `GlueComputable` certificate of a node, one closure rule per form. -/
private partial def glueProof (exact : Bool) (B kE P bound : Expr) (k : Nat)
    (hb : Nat → MetaM Expr) (hd : Nat → MetaM Expr) : ANode → MetaM Expr
  | .reg idx _ i => do
    mkAppOptM ``GlueComputable.proj #[B, kE, P, bound, ← finLit k i, ← hb idx]
  | .const idx c _ => do
    mkAppOptM ``GlueComputable.const #[B, kE, P, bound, c, ← hb idx]
  | .bin idx _ op dom a b => do
    let ga ← glueProof exact B kE P bound k hb hd a
    let gb ← glueProof exact B kE P bound k hb hd b
    match dom with
    | some di => mkAppM (op.rule exact) #[ga, gb, ← hd di, ← hb idx]
    | none => mkAppM (op.rule exact) #[ga, gb, ← hb idx]

/-- `![x₀, …, xₙ]` over element type `elemTy` (default `ℕ`). -/
private def vecOf (xs : List Expr) (elemTy : Expr := mkConst ``Nat) : MetaM Expr := do
  match xs with
  | [] => mkAppOptM ``Matrix.vecEmpty #[elemTy]
  | x :: xs => mkAppM ``Matrix.vecCons #[x, ← vecOf xs elemTy]

/-- `∀ i, GlueComputable B (fun v => ![f₀ v, …] i) P bound` from the coordinate certificates. -/
private partial def vecCoords (B kE P bound v : Expr) (vals proofs : Array Expr) (j : Nat) :
    MetaM Expr := do
  let l := vals.size
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit (l - j))) fun i => do
    let f ← mkLambdaFVars #[v] vals[j]!
    if j + 1 == l then
      return ← mkLambdaFVars #[i] (← mkAppOptM ``GlueComputable.vec_single
        #[B, kE, P, bound, f, proofs[j]!, i])
    let g ← mkLambdaFVars #[v] (← vecOf (vals.toList.drop (j + 1)))
    let tail ← vecCoords B kE P bound v vals proofs (j + 1)
    mkLambdaFVars #[i] (← mkAppOptM ``GlueComputable.vec_cons
      #[B, kE, P, bound, f, mkNatLit (l - j - 1), g, proofs[j]!, tail, i])

/-- Replace the maximal non-constructor subterms of `e` by local variables, then continue with
the skeleton and the pairs (variable, replaced subterm). -/
private partial def withSkeleton {β : Type} (e : Expr) (acc : Array (Expr × Expr))
    (k : Expr → Array (Expr × Expr) → MetaM β) : MetaM β := do
  let e' ← whnfR e
  if let .const c _ := e'.getAppFn then
    if let some (.ctorInfo info) := (← getEnv).find? c then
      if info.induct != ``Nat then
        let args := e'.getAppArgs
        let rec go (j : Nat) (newArgs : Array Expr) (acc : Array (Expr × Expr)) : MetaM β :=
          if h : j < args.size then
            if j < info.numParams then go (j + 1) (newArgs.push args[j]) acc
            else withSkeleton args[j] acc fun a' acc' => go (j + 1) (newArgs.push a') acc'
          else k (mkAppN e'.getAppFn newArgs) acc
        return ← go 0 #[] acc
  withLocalDeclD `z (← inferType e) fun z => k z (acc.push (z, e))

/-- The coordinates of `enc a` in the client's terms. Constructor applications are kept as a
skeleton so that the encoding reduces without unfolding the client's arithmetic. -/
private def coordinates (enc a : Expr) (l : Nat) : MetaM (Array Expr) :=
  withSkeleton a #[] fun skel holes => do
    let cs ← encodingAtoms enc skel l
    return cs.map fun c => c.replaceFVars (holes.map (·.1)) (holes.map (·.2))

/-! ### Realization -/

/-- The active combinator bundle, basis, and whether the basis is `.exact` or `.standard`. -/
private structure Ctx where
  /-- Proof combinators for the active realization judgment. -/
  comb : Combinators
  /-- The basis. -/
  basis : Expr
  /-- Whether the basis is `.exact`. -/
  exact : Bool
  /-- Whether the basis is `.standard`. -/
  standard : Bool

/-- Extract `a` from `pure a` in `Pure.pure`, `PFunctor.FreeM.pure`, or a projected `Pure` call. -/
private def pureArg? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``PFunctor.FreeM.pure 3 ||
      (e.getAppFn matches .proj ``Pure 0 _ && e.getAppNumArgs == 2) then
    some e.appArg!
  else none

/-- Extract `(β, x, k)` from `x >>= k` in `Bind.bind`, `PFunctor.FreeM.bind`, or a projected
`Bind` call. -/
private def bindArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity ``Bind.bind 6 then
    some (e.getArg! 2, e.getArg! 4, e.getArg! 5)
  else if e.isAppOfArity ``PFunctor.FreeM.bind 5 then
    some (e.getArg! 1, e.getArg! 3, e.getArg! 4)
  else if e.getAppFn matches .proj ``Bind 0 _ && e.getAppNumArgs == 4 then
    some (e.getArg! 0, e.getArg! 2, e.getArg! 3)
  else none

/-- `fun _ _ => 0`. -/
private def zeroWork (δ : Expr) : MetaM Expr :=
  withLocalDeclD `d δ fun d => withLocalDeclD `s (mkConst ``Memory.State) fun s =>
    mkLambdaFVars #[d, s] (mkNatLit 0)

/-- Whether a grading is definitionally zero, without assigning its metavariables. -/
private def isZeroWork (δ work : Expr) : MetaM Bool := do
  withNewMCtxDepth <| withReducible <| isDefEq work (← zeroWork δ)

/-- The local-work grading of a completed certificate. -/
private def certificateWork (comb : Combinators) (proof : Expr) : MetaM Expr := do
  let ty ← inferType proof
  unless ty.isAppOfArity comb.cert 10 do
    throwError "realize: internal error reading a certificate's work"
  return ty.getArg! 9

/-- Absorb fixed finite composition control while retaining the component grades. -/
private def absorbControl (comb : Combinators) (proof work : Expr) (factor : Nat) :
    TermElabM Expr := do
  let ty ← inferType proof
  let target := mkAppN ty.getAppFn (ty.getAppArgs.set! 9 work)
  let result ← mkFreshExprMVar target
  let args := ty.getAppArgs
  let transfer ← mkAppOptM comb.monoMul
    #[args[4]!, args[2]!, args[3]!, args[0]!, args[1]!, args[5]!, args[6]!, args[7]!,
      args[8]!, args[9]!, work, proof, mkNatLit factor]
  let [bound] ← result.mvarId!.apply transfer
    | throwError "realize: internal error absorbing finite control"
  let h ← Term.withSynthesize <| Term.elabTermEnsuringType
    (← `(by intro d s; omega)) (some (← bound.getType))
  bound.assign h
  instantiateMVars result

/-- `fun _ _ _ => True`. -/
private def trueSafe (δ : Expr) : MetaM Expr :=
  withLocalDeclD `w (mkConst ``Nat) fun w => withLocalDeclD `d δ fun d =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => mkLambdaFVars #[w, d, s] (mkConst ``True)

/-- The input encoding of the continuation of a bind. -/
private def appendInput (env : Env) (answer : Expr) (l : Nat) : MetaM Expr := do
  let prod ← mkAppM ``Function.Embedding.prodMap #[env.input, answer]
  let app ← mkAppM ``Equiv.toEmbedding
    #[← mkAppOptM ``Fin.appendEquiv #[mkConst ``Nat, mkNatLit env.k, mkNatLit l]]
  mkAppM ``Function.Embedding.trans #[prod, app]

/-- The environment of the continuation of a bind whose answer has type `α`. When `idNat` is true,
`answer` is the canonical 1-word `ℕ` encoding and existing atoms are reused directly. -/
private def extend (env : Env) (α answer : Expr) (l : Nat) (idNat : Bool := false) :
    MetaM Env := do
  let ty ← mkAppM ``Prod #[env.ty, α]
  let input ← appendInput env answer l
  let atoms ← withLocalDeclD `x ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    let old ← if idNat then pure (env.atoms.map (·.beta #[x1]))
      else env.atoms.mapM fun a => whnf (a.beta #[x1])
    let new ← if idNat then pure #[x2] else encodingAtoms answer x2 l
    (old ++ new).mapM (mkLambdaFVars #[x] ·)
  return { ty, k := env.k + l, input, atoms }

/-- The reply and next memory of a client from memory `s`, in the client's terms. -/
private def replyState (m s : Expr) : MetaM (Expr × Expr) := do
  let m' ← whnfR m
  if let some a := pureArg? m' then return (a, s)
  if m'.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR m'.appArg!
    let mem ← mkAppM ``Memory.State.mem #[s]
    let frontier ← mkAppM ``Memory.State.frontier #[s]
    if let some a := op.app1? ``Memory.Op.read then return (mkApp mem a, s)
    if let some (a, v) := op.app2? ``Memory.Op.write then
      return (mkConst ``Unit.unit,
        ← mkAppM ``Memory.State.mk #[← mkAppM ``Function.update #[mem, a, v], frontier])
    if let some n := op.app1? ``Memory.Op.alloc then
      return (frontier, ← mkAppM ``Memory.State.mk
        #[← mkAppM ``Cslib.WordRAM.clear #[mem, frontier, n], ← mkAppM ``HAdd.hAdd #[frontier, n]])
    if let some n := op.app1? ``Memory.Op.allocDirty then
      return (frontier, ← mkAppM ``Memory.State.mk #[mem, ← mkAppM ``HAdd.hAdd #[frontier, n]])
  let spec ← mkAppM ``Memory.spec #[mkNatLit 0]
  return (← mkAppM ``StateTransitionSpec.clientResult #[spec, s, m],
    ← mkAppM ``StateTransitionSpec.clientState #[spec, s, m])

/-- The result type of a memory client. -/
private def resultType (body : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType body)
  unless ty.isAppOfArity ``PFunctor.FreeM 2 do
    throwError "realize: expected a memory client, got{indentExpr body}\nof type{indentExpr ty}"
  whnf ty.appArg!

/-- The encoding of an intermediate answer type. -/
private def encodingOf (α : Expr) : MetaM Expr := do
  let some inst ← synthInstance? (← mkAppM ``WordEncoding #[α])
    | throwError "realize: no `WordEncoding` instance for the answer type{indentExpr α}"
  let e ← mkAppOptM ``WordEncoding.encode #[α, inst]
  return (← unfoldProjInst? e).getD e

/-- `Bind.bind (pure a) cont` in `Memory.Prog`. -/
private def bindPure (a cont : Expr) : MetaM Expr := do
  let prog := mkConst ``Memory.Prog
  let pa ← mkAppOptM ``Pure.pure #[prog, none, mkConst ``Nat, a]
  mkAppOptM ``Bind.bind #[prog, none, mkConst ``Nat, none, pa, cont]

/-- Prove `∀ d i, output (f d) i = g i (input d)` for `i : Fin l` by `Fin.cases`, with one `rfl` per
coordinate. Both sides are the same coordinate by construction of `g` (`coordinates`, `analyze`);
the kernel checks each `rfl`. -/
private def proveResult (ty : Expr) (l : Nat) : MetaM Expr :=
  forallBoundedTelescope ty (some 2) fun xs eq => do
    let #[d, i] := xs | throwError "realize: internal error in the result encoding"
    let P ← mkLambdaFVars #[i] eq
    let rec cover (n : Nat) (emb : Expr → MetaM Expr) : MetaM Expr := do
      let finN := mkApp (mkConst ``Fin) (mkNatLit n)
      match n with
      | 0 => withLocalDeclD `j finN fun j => do
        mkLambdaFVars #[j] (← mkAppOptM ``Fin.elim0 #[P.beta #[← emb j], j])
      | m + 1 => do
        let motive ← withLocalDeclD `j finN fun j => do mkLambdaFVars #[j] (P.beta #[← emb j])
        let goal := P.beta #[← emb (← mkNumeral finN 0)]
        let some (_, lhs, _) := goal.eq?
          | throwError "realize: internal error in the result encoding"
        let h0 ← mkExpectedTypeHint (← mkEqRefl lhs) goal
        let hs ← cover m fun j => do emb (← mkAppM ``Fin.succ #[j])
        mkAppOptM ``Fin.cases #[mkNatLit m, motive, h0, hs]
    mkLambdaFVars #[d] (← cover l pure)

/-- Certify `pure a` with the result encoding `out`, for the environment variable `d`. -/
private def realizePure (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr) (a out : Expr) :
    TermElabM Out := do
  let l ← encodingWidth out
  let coordsU ← coordinates out a l
  let gnodes ← coordsU.mapM fun c => liftMetaM (analyze atoms d c)
  unless ctx.exact || ctx.standard || gnodes.all (fun g => !(g matches .bin ..)) do
    throwError "realize: word arithmetic is certified in the exact and standard bases; the \
      goal's basis is{indentExpr ctx.basis}"
  let k := env.k
  let kE := mkNatLit k
  let B := ctx.basis
  let nat := mkConst ``Nat
  let finK := mkApp (mkConst ``Fin) kE
  let finL := mkApp (mkConst ``Fin) (mkNatLit l)
  let maxFn ← natMax
  withLocalDeclD `v (← mkArrow finK nat) fun v => do
    let (anodes, st) ← (gnodes.mapM (annotate ctx.exact k v)).run {}
    let uvals := gnodes.foldl (fun acc g => userVals g acc) #[]
    let domTy := conj st.domV.toList
    let P ← mkLambdaFVars #[v] domTy
    let bound ← mkLambdaFVars #[v]
      (if st.vals.isEmpty then mkNatLit 0 else maxChain maxFn st.vals)
    let hb (idx : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← memProof maxFn st.vals idx)
    let hd (di : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← conjunct hv st.domV.size di)
    let proofs ← anodes.mapM fun n => liftMetaM (glueProof ctx.exact B kE P bound k hb hd n)
    let vals := anodes.map (·.val)
    let gfun ← withLocalDeclD `i finL fun i => do
      mkLambdaFVars #[i, v] (mkApp (← vecOf vals.toList) i)
    let hcoord ← if l == 0 then
        withLocalDeclD `i finL fun i => do
          let ty ← mkAppM ``GlueComputable #[B, mkApp gfun i, P, bound]
          mkLambdaFVars #[i] (← mkAppOptM ``Fin.elim0 #[ty, i])
      else vecCoords B kE P bound v vals proofs 0
    withLocalDeclD `w nat fun w => do
      let needIdx := anodes.foldl (fun acc n => needNodes ctx.exact n false acc) #[]
      let needV ← needIdx.mapM fun i => mkAppM ``Fits #[w, st.vals[i]!]
      let needU ← needIdx.mapM fun i => mkAppM ``Fits #[w, uvals[i]!]
      let needTy := conj needV.toList
      let need ← mkLambdaFVars #[w, v] needTy
      let hregsTy ← withLocalDeclD `i finK fun i => do
        mkForallFVars #[i] (← mkAppM ``Fits #[w, mkApp v i])
      let hneed ← withLocalDeclD `hregs hregsTy fun hregs =>
        withLocalDeclD `hP domTy fun hP => withLocalDeclD `hn needTy fun hn => do
          let fits ← if st.vals.isEmpty then pure #[← mkAppM ``fits_zero #[w]] else do
            let (_, fits) ← (anodes.forM fun n => discard <|
              fitProofs ctx.exact k w hregs hP hn st.domV.size needIdx n none).run
                (Array.replicate st.vals.size default)
            pure fits
          mkLambdaFVars #[w, v, hregs, hP, hn] (← fitChain fits)
      let f ← mkLambdaFVars #[d] a
      let resTy ← withLocalDeclD `d env.ty fun d' => withLocalDeclD `i finL fun i => do
        let lhs := mkApp (← mkAppM ``DFunLike.coe #[out, f.beta #[d']]) i
        let rhs := mkApp2 gfun i (← mkAppM ``DFunLike.coe #[env.input, d'])
        mkForallFVars #[d', i] (← mkEq lhs rhs)
      let hresult ← proveResult resTy l
      let proof ← mkAppM ctx.comb.pure0
        #[env.input, out, f, gfun, need, hresult, hcoord, hneed]
      let safe ← withLocalDeclD `s (mkConst ``Memory.State) fun s =>
        mkLambdaFVars #[w, d, s] (mkAnd (conj st.domU.toList) (conj needU.toList))
      return { proof, output := out, safe, work := ← zeroWork env.ty }

/-- Check a certificate's output encoding against the required one. -/
private def checkOutput (comb : Combinators) (proof : Expr) (output? : Option Expr) :
    MetaM Expr := do
  let ty ← instantiateMVars (← inferType proof)
  unless ty.isAppOfArity comb.cert 10 do
    throwError "realize: internal error, not a certificate"
  let out := ty.getArg! 7
  if let some o := output? then
    unless ← isDefEq out o do
      throwError "realize: the query returns its answer encoded by{indentExpr out}\n\
        but the goal requires{indentExpr o}"
  return out

/-- The native comparison of a word condition, equality or `<`, with its operands. -/
private def cond? (c : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (ty, a, b) := c.eq? then
    if (← whnfR ty).isConstOf ``Nat then return some (``Cond.eq, a, b)
  if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 2, c.getArg! 3)
  if c.isAppOfArity ``GT.gt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 3, c.getArg! 2)
  return none

/-- The comparison of a branch condition: equality or `<`, with its operands. -/
private def parseCond (c : Expr) : MetaM (Name × Expr × Expr) := do
  if let some r ← cond? c then return r
  throwError "realize: a branch condition must combine word comparisons \
    (`=`, `≠`, `<`, `≤`, `>` or `≥`) using `¬`, `∧` or `∨`, \
    got{indentExpr c}"

/-- Expose named predicates throughout the logical guard while leaving word comparisons intact. -/
private partial def unfoldGuard (c : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if let some name := c.getAppFn.constName? then
    if [``Eq, ``Ne, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge].contains name then
      return c
  if fuel == 0 then throwError "realize: branch guard unfolding exceeded its limit at{indentExpr c}"
  if c.isAppOfArity ``And 2 || c.isAppOfArity ``Or 2 then
    return mkApp2 c.getAppFn (← unfoldGuard (c.getArg! 0) (fuel - 1))
      (← unfoldGuard (c.getArg! 1) (fuel - 1))
  if c.isAppOfArity ``Not 1 then
    return mkApp c.getAppFn (← unfoldGuard c.appArg! (fuel - 1))
  let c' ← whnfR c
  if c' != c then return ← unfoldGuard c' (fuel - 1)
  if let some c' ← withTransparency .default (unfoldDefinition? c) then
    return ← unfoldGuard c' (fuel - 1)
  return c

/-- Lower a compound word test to native comparisons. Leave word operands and alternatives
untouched so their own rules retain live values, fit and selected-path safety. -/
private def normalizeBranch? (body : Expr) : MetaM (Option Simp.Result) := do
  let guard ← unfoldGuard (body.getArg! 1)
  let mut guardThms : SimpTheorems := {}
  guardThms ← guardThms.addConst ``ne_eq
  guardThms ← guardThms.addConst ``not_lt (inv := true)
  let ctx ← Simp.mkContext
    (config := { dsimp := false, zeta := false, proj := false, iota := false })
    (simpTheorems := #[guardThms]) (congrTheorems := ← getSimpCongrTheorems)
  let defaults := Simp.mkDefaultMethodsCore #[]
  let guardMethods : Simp.Methods := { defaults with
    pre := fun e => do
      if (← whnfR (← inferType e)).isConstOf ``Nat then return .done { expr := e }
      if e != guard && (← isProp e) then return .done { expr := e }
      defaults.pre e }
  let (condition, _) ← Simp.main guard ctx (methods := guardMethods)
  -- Rebuild decidability from the exposed formula. Its original instance can be hidden
  -- behind a named guard; conditional congruence checks the bridge for either instance.
  let h ← mkAppOptM ``ite_cond_congr #[some (body.getArg! 0), some (body.getArg! 1),
    some condition.expr, some (body.getArg! 2), none, some (body.getArg! 3),
    some (body.getArg! 4), some (← condition.getProof)]
  let some (_, _, canonical) := (← inferType h).eq?
    | throwError "realize: internal error rebuilding a branch condition"
  let mut thms : SimpTheorems := {}
  for name in [``ite_not, ``ite_and, ``ite_or] do
    thms ← thms.addConst name
  let methods : Simp.Methods := { defaults with
    pre := fun e => do
      if e == body.getArg! 3 || e == body.getArg! 4 then return .done { expr := e }
      if ← isProp e then return .done { expr := e }
      defaults.pre e }
  let (normalized, _) ← Simp.main canonical (ctx.setSimpTheorems #[thms]) (methods := methods)
  -- Each recursive call exposes an alias or simplifies the outer condition. Do not
  -- recurse merely because an unsupported condition acquired a different instance.
  if normalized.expr.isAppOfArity ``ite 5 &&
      normalized.expr.getArg! 1 != body.getArg! 1 then
    return some { normalized with proof? := some (← mkEqTrans h (← normalized.getProof)) }
  return none

/-- The comparison of a loop guard, with a checked equivalence to its native test.
Successor lower bounds use the predecessor directly, without computing a successor word. -/
private partial def parseGuard (g : Expr) (orig : Expr := g.headBeta) (fuel : Nat := 64) :
    MetaM (Name × Expr × Expr × Expr) := do
  let g := g.headBeta
  if let some (kind, a, b) ← cond? g then
    return (kind, a, b, ← mkAppM ``Iff.refl #[g])
  if let some (ty, a, z) := g.ne?.orElse fun _ => g.not?.bind Expr.eq? then
    if (← whnfR ty).isConstOf ``Nat && (← withNewMCtxDepth (isDefEq z (mkNatLit 0))) then
      return (``Cond.lt, z, a,
        ← mkAppM ``Iff.symm #[← mkAppOptM ``Nat.pos_iff_ne_zero #[a]])
  if (g.isAppOfArity ``LE.le 4 || g.isAppOfArity ``GE.ge 4) &&
      (g.getArg! 0).isConstOf ``Nat then
    let (a, b) := if g.isAppOfArity ``GE.ge 4 then (g.getArg! 3, g.getArg! 2)
      else (g.getArg! 2, g.getArg! 3)
    let a ← whnfR a
    let literal? ← getNatValue? a
    let add? := if let some (.add, p, q) := binOp? a then some (p, q)
      else if a.isAppOfArity ``Nat.add 2 then some (a.getArg! 0, a.getArg! 1) else none
    let pred? ← if let some (p, q) := add? then do
        let one ← withNewMCtxDepth (isDefEq q (mkNatLit 1))
        pure (if one then some p else none)
      else pure <| if a.isAppOfArity ``Nat.succ 1 then some (a.getArg! 0)
        else literal?.bind fun n => if n == 0 then none else some (mkNatLit (n - 1))
    if let some pred := pred? then
      return (``Cond.lt, pred, b, ← mkAppOptM ``Nat.succ_le_iff #[pred, b])
  if fuel != 0 then
    let g' ← whnfR g
    if g' != g then return ← parseGuard g' orig (fuel - 1)
    if let some g' ← unfoldDefinition? g then return ← parseGuard g' orig (fuel - 1)
  throwError "realize: a loop guard must be `a = b`, `a < b`, `a > b`, `a ≠ 0` \
    or `a + 1 ≤ b` on words, \
    got{indentExpr orig}"

/-- Rebuild a branch condition with new operands. -/
private def rebuildCond (c a b : Expr) : MetaM Expr := do
  if c.isEq then mkEq a b
  else if c.isAppOfArity ``LT.lt 4 then mkAppM ``LT.lt #[a, b]
  else mkAppM ``GT.gt #[b, a]

/-- Both spellings of a result map on a memory program. -/
private def isClientMap (e : Expr) : Bool :=
  e.isAppOfArity ``Functor.map 6 || e.isAppOfArity ``PFunctor.FreeM.map 5

/-- Primitive syntax forms on which local method certificates are never queried. A result map is
not one: a certificate may cover a whole mapped client. -/
private def isPrimitiveClientForm (e : Expr) : Bool :=
  e.isAppOfArity ``Bind.bind 6 || e.isAppOfArity ``PFunctor.FreeM.bind 5 ||
  e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``PFunctor.FreeM.pure 3 ||
  e.isAppOfArity ``PFunctor.FreeM.lift 2 || e.isAppOfArity ``PFunctor.FreeM.liftBind 4 ||
  e.isAppOfArity ``ite 5

/-- Whether the head is a client form `realize` handles directly without unfolding. -/
private def isClientForm (e : Expr) : Bool :=
  isPrimitiveClientForm e || isClientMap e || e.isAppOfArity ``PFunctor.FreeM.liftM 7 ||
  e.isAppOfArity ``boundedWhile 8 || e.isAppOfArity ``iterate 6

/-- Reduce a layout/projection scalar address to word arithmetic by pure definitional steps,
stopping as soon as a live word, numeral or word-arithmetic operator is reached. -/
private def normScalar (atoms : Array Expr) (e : Expr) : MetaM Expr := do
  let isStop (x : Expr) : Bool :=
    if x.isFVar || x.isLit || x.isBVar || x.isMVar then true
    else if let some c := x.getAppFn.constName? then
      [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod,
       ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor, ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight,
       ``OfNat.ofNat, ``Nat.zero, ``Nat.succ, ``DFunLike.coe,
       ``Memory.State.mem, ``Memory.State.frontier,
       ``StateTransitionSpec.clientResult, ``StateTransitionSpec.clientState].contains c
    else false
  let env ← getEnv
  let mut cur := e
  for _ in [0:32] do
    if isStop cur then break
    if (← findAtom atoms cur).isSome then break
    let head := cur.getAppFn
    let args := cur.getAppArgs
    if let .proj s idx sv := head then
      let svR ← whnfR sv
      if isStructure env s then
        if let some field := ctorField? env (getStructureCtor env s).name idx svR then
          cur := (mkAppN field args).headBeta
          continue
      if let some next ← unfoldDefinition? svR then
        cur := mkAppN (.proj s idx next.headBeta) args
        continue
      break
    if let some next ← unfoldDefinition? cur then
      cur := next.headBeta
      continue
    let next ← whnfR cur
    if next != cur then
      cur := next
      continue
    break
  return cur

/-- Normalize an interpreted lower-interface operation `interp op` to a client form or primitive
memory query with reduced scalar operands while preserving definitional (`rfl`) equality. -/
private def normInterpOp (atoms : Array Expr) (e : Expr) : MetaM Expr := do
  let mut cur := e.headBeta
  for _ in [0:32] do
    if isClientForm cur then break
    if let some next ← unfoldDefinition? cur then
      cur := next.headBeta
      continue
    let next ← whnfR cur
    if next != cur then
      cur := next
      continue
    break
  if cur.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR cur.appArg!
    if let some opFn := op.getAppFn.constName? then
      if [``Memory.Op.read, ``Memory.Op.write, ``Memory.Op.alloc,
          ``Memory.Op.allocDirty].contains opFn then
        let opArgs ← op.getAppArgs.mapM (normScalar atoms)
        return mkApp2 cur.getAppFn (cur.getArg! 0) (mkAppN op.getAppFn opArgs)
  return cur

/-- An optional answer that a `match` in the client inspects: a discriminant of an `Option` type
that depends on the environment variable `d`. -/
private def optionDiscr? (d body : Expr) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  let found ← IO.mkRef (none : Option Expr)
  let _ ← Meta.transform body (pre := fun e => do
    if (← found.get).isSome then return .done e
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      for r in app.discrs do
        if r.containsFVar d.fvarId! &&
            (r.find? fun x => x.isFVar && !lctx.contains x.fvarId!).isNone then
          if (← whnfR (← inferType r)).isAppOfArity ``Option 1 then
            found.set (some r)
            return .done e
    return .continue)
  found.get

/-- Prove `∀ d, rhs = body` by a case split on the optional answer `r`. -/
private def proveSplit (d r ty : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar ty
  let (dfv, g) ← mvar.mvarId!.intro1
  let r' := r.replaceFVar d (mkFVar dfv)
  let (zs, g) ← g.generalize #[{ expr := r', xName? := `z }]
  for sg in ← g.cases zs[0]! do sg.mvarId.refl
  instantiateMVars mvar

/-- Keep query-paid loop control (`∀ x s, 1 ≤ memoryCost (body x) s`) when the body has zero local
work and begins with a memory query. -/
private def queryPayment? (body ty work : Expr) : MetaM (Option Expr) := do
  unless ← isZeroWork ty work do return none
  withLocalDeclD `x ty fun x => withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let b ← whnf (mkApp body x)
    unless b.isAppOfArity ``PFunctor.FreeM.liftBind 4 do return none
    tryBacktrack? do
      let pf ← mkAppM ``one_le_memoryCost_liftBind #[b.getArg! 2, b.getArg! 3, s]
      let goal ← mkAppM ``LE.le #[mkNatLit 1, ← mkAppM ``memoryCost #[mkApp body x, s]]
      return some (← mkLambdaFVars #[x, s] (← mkExpectedTypeHint pf goal))

/-- Apply `funext` across `xs` in outer-to-inner order around a pointwise equality proof `eq`. -/
private def mkFunextN (xs : Array Expr) (eq : Expr) : MetaM Expr :=
  xs.foldrM (init := eq) fun x acc => do mkAppM ``funext #[← mkLambdaFVars #[x] acc]

/-- Transport a certificate's domain or work along an equality of its functions. -/
private def transportField (proof eq : Expr) (index : Nat) : MetaM Expr := do
  let ty ← inferType proof
  let wrap ← withLocalDeclD `field (← inferType (ty.getArg! index)) fun field =>
    mkLambdaFVars #[field] (mkAppN ty.getAppFn (ty.getAppArgs.set! index field))
  mkAppM ``Eq.mp #[← mkAppM ``congrArg #[wrap, eq], proof]

/-- State `proof` as `comb.cert B prog input output safe work`, for the client `prog`
as written and the domain `safe` in the client's terms.

The rule's statement agrees with this one by construction: up to unfolding `prog`, reducing
structure projections, and evaluating the live words, which were located as the weak-head normal
forms of `input d i`. The kernel checks the agreement locally at each form. Elaboration does not
re-check it, because unfolding composed domains with nested interpreter runs grows with the
client. -/
private def certify (ctx : Ctx) (env : Env) (proof prog output safe work : Expr) : MetaM Expr := do
  mkExpectedTypeHint proof
    (← mkAppM ctx.comb.cert #[ctx.basis, prog, env.input, output, safe, work])

/-- Compose at a closed-form reply and next memory, retaining component work while absorbing
the bind's fixed control. The zero-work case keeps `bind₀_of_run`. -/
private def bindRun (comb : Combinators) (hP hQ reply next : Expr) : TermElabM Expr := do
  let pTy ← inferType hP
  let workP := pTy.getArg! 9
  let workQ ← certificateWork comb hQ
  let pZero ← isZeroWork (pTy.getArg! 2) workP
  let qZero ← isZeroWork ((← inferType hQ).getArg! 2) workQ
  if !pZero || !qZero then
    let (work, charged) ← withLocalDeclD `d (pTy.getArg! 2) fun d =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        let pair ← mkAppM ``Prod.mk #[d, reply.beta #[d, s]]
        let wp := workP.beta #[d, s]
        let wq := workQ.beta #[pair, next.beta #[d, s]]
        let sum ← if pZero then pure wq else if qZero then pure wp
          else mkAppM ``HAdd.hAdd #[wp, wq]
        let charged ← mkAppM ``HAdd.hAdd
          #[← mkAppM ``HAdd.hAdd #[wp, wq], mkNatLit 1]
        return (← mkLambdaFVars #[d, s] (← reduceProjections sum),
          ← mkLambdaFVars #[d, s] (← reduceProjections charged))
    let proof ← mkAppM comb.bind #[hP, hQ]
    let ty ← inferType proof
    let proof ← mkExpectedTypeHint proof (mkAppN ty.getAppFn (ty.getAppArgs.set! 9 charged))
    return ← absorbControl comb proof work 1
  let refl (f : Expr) : MetaM Expr :=
    lambdaBoundedTelescope f 2 fun xs b => do mkLambdaFVars xs (← mkEqRefl b)
  mkAppM comb.bind0OfRun #[hP, hQ, reply, next, ← refl reply, ← refl next]

/-- Compose a staged pure value `val` (leaving memory unchanged) with continuation `hCont`. -/
private def bindPureProof (comb : Combinators) (d val hVal hCont : Expr) : TermElabM Expr := do
  let (reply, next) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    return (← mkLambdaFVars #[d, s] val, ← mkLambdaFVars #[d, s] s)
  bindRun comb hVal hCont reply next

/-- Compose a staged pure `Out` (`hVal`) at value `val` with continuation `Out` (`hCont`). -/
private def bindPureOut (comb : Combinators) (d val : Expr) (hVal hCont : Out) :
    TermElabM Out := do
  let proof ← bindPureProof comb d val hVal.proof hCont.proof
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, val]
      mkLambdaFVars #[w, d, s] (mkAnd (hVal.safe.beta #[w, d, s])
        (← reduceProjections (hCont.safe.beta #[w, pair, s])))
  return { proof, output := hCont.output, safe, work := ← certificateWork comb proof }

/-- State a loop body's domain in the client's loop environment `(Δ × σ)` at fixed `e₀`. -/
private def adaptLoopSafe (pairTy e₀ bodySafe : Expr) : MetaM Expr :=
  withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `x pairTy fun x =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        let y ← mkAppM ``Prod.mk #[e₀, ← mkAppM ``Prod.snd #[x]]
        mkLambdaFVars #[w, x, s] (← reduceProjections (bodySafe.beta #[w, y, s]))

/-- State a loop body's local work in the client's loop environment `(Δ × σ)` at fixed `e₀`,
with the pointwise `rfl` agreement proof `∀ x s, bodyWork (e₀, x) s = clientWork (D, x) s`. -/
private def adaptLoopWork (pairTy σ e₀ D bodyWork : Expr) : MetaM (Expr × Expr) := do
  let state := mkConst ``Memory.State
  let clientWork ← withLocalDeclD `x pairTy fun x =>
    withLocalDeclD `s state fun s => do
      let y ← mkAppM ``Prod.mk #[e₀, ← mkAppM ``Prod.snd #[x]]
      mkLambdaFVars #[x, s] (← reduceProjections (bodyWork.beta #[y, s]))
  let hw ← withLocalDeclD `x σ fun x => withLocalDeclD `s state fun s => do
    let lhs := bodyWork.beta #[← mkAppM ``Prod.mk #[e₀, x], s]
    let rhs := clientWork.beta #[← mkAppM ``Prod.mk #[D, x], s]
    mkLambdaFVars #[x, s] (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  return (clientWork, hw)

/-- Expose tuple and pure data-structure projections to unification when a certificate packages
curried arguments. Structures carrying `Prop` proofs (such as `Fin` or `Subtype`) and other types
remain whole metavariables: no runtime value or proof witness is guessed. -/
private partial def callArgument (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if !(← isProp ty) && (← isClass? ty).isNone then
    if let .const s us := ty.getAppFn then
      let env ← getEnv
      if isStructure env s then
        let ctor := getStructureCtor env s
        if ctor.numFields > 0 && ty.getAppNumArgs == ctor.numParams then
          if let some acc ← tryBacktrack? (do
            let ctorFn := mkAppN (mkConst ctor.name us) ty.getAppArgs
            let mut acc := ctorFn
            let mut remTy ← inferType ctorFn
            for _ in [0:ctor.numFields] do
              let .forallE _ dom body _ ← whnf remTy | return none
              if ← isProp dom then return none
              let field ← callArgument dom
              acc := mkApp acc field
              remTy := body.instantiate1 field
            return some acc) then
            return acc
  mkFreshExprMVar ty

/-- Recognize `Fin k → ℕ` for a concrete positive width `k`. -/
private def finVecWidth? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  let .forallE _ dom body _ := ty | return none
  if body.hasLooseBVars then return none
  unless (← whnfR body).isConstOf ``Nat do return none
  let some n := (← whnfR dom).app1? ``Fin | return none
  let some k ← (evalNat (← whnf n)).run | return none
  if 1 ≤ k && k ≤ 32 then return some k
  return none

/-- Unify a certificate's method pattern against `body`, trying `callArgument` first and falling
back to an explicit `![?x₀, …, ?x_{k-1}]` vector when the certificate's environment is
`Fin k → ℕ`. Aligns `DataStructure.link` and `PFunctor.FreeM.liftM` heads without unfolding the
layout inside `methods`. -/
private def matchMethodCall (certArgs : Array Expr) (body : Expr) : MetaM (Option Expr) := do
  let tryWithArg (arg : Expr) (reduceVec : Bool) : MetaM (Option Expr) := do
    let mut called := (mkApp certArgs[5]! arg).headBeta
    if reduceVec then called ← reduceFinVecApps called
    if called.isAppOfArity ``Cslib.DataStructure.link 5 &&
        body.isAppOfArity ``PFunctor.FreeM.liftM 7 then
      if let some c' ← unfoldDefinition? called then called := c'.headBeta
    let matched ← if called.getAppFn == body.getAppFn &&
        called.getAppNumArgs == body.getAppNumArgs then
        (called.getAppArgs.zip body.getAppArgs).allM fun (a, b) => do
          let a ← whnfR a
          let b ← whnfR b
          if (← isClass? (← inferType a)).isSome then
            withTransparency .default (isDefEq a b)
          else
            withReducible (isDefEq a b)
      else withReducible (isDefEq called body)
    unless matched do return none
    let arg ← instantiateMVars arg
    if arg.hasMVar then return none
    return some arg
  if let some res ← tryBacktrack? (do tryWithArg (← callArgument certArgs[2]!) false) then
    return some res
  if let some fk ← finVecWidth? certArgs[2]! then
    return ← tryBacktrack? do
      let mvars ← (List.range fk).mapM fun _ => mkFreshExprMVar (mkConst ``Nat)
      tryWithArg (← vecOf mvars) true
  return none

/-- Collect local hypotheses whose types match `ctx.comb.cert` in `ctx.basis`. -/
private def localCerts (ctx : Ctx) : MetaM (Array (Expr × Array Expr)) := do
  let mut out := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars decl.type)
    unless ty.isAppOfArity ctx.comb.cert 10 do continue
    let args := ty.getAppArgs
    if ← withNewMCtxDepth (withReducible (isDefEq args[4]! ctx.basis)) then
      out := out.push (decl.toExpr, args)
  return out

/-- Check whether `cand` matches any local method certificate in the active judgment and basis,
without modifying metavariable state. -/
private def matchesLocalCert (ctx : Ctx) (cand : Expr) : MetaM Bool := do
  (← localCerts ctx).anyM fun (_, args) =>
    withNewMCtxDepth do return (← matchMethodCall args cand).isSome

/-- Wire a matched method's encoded argument to live words, retaining its domain. -/
private def reindexCall (comb : Combinators) (env : Env) (d arg certificate : Expr)
    (positions : Array Nat) : TermElabM Out := do
  let ty ← whnfR (← instantiateMVars (← inferType certificate))
  unless ty.isAppOfArity comb.cert 10 do
    throwError "realize: expected a `{comb.label}` method certificate{indentExpr ty}"
  let argClean ← etaContractStructures arg
  let args := ty.getAppArgs
  let k := positions.size
  let finK := mkApp (mkConst ``Fin) (mkNatLit k)
  let finEnv := mkApp (mkConst ``Fin) (mkNatLit env.k)
  let ix ← liftMetaM do vecOf (← positions.toList.mapM (finLit env.k)) finEnv
  let f ← mkLambdaFVars #[d] argClean
  let hwTy ← withLocalDeclD `e env.ty fun e => withLocalDeclD `i finK fun i => do
    let lhs := mkApp (← mkAppM ``DFunLike.coe #[args[6]!, f.beta #[e]]) i
    let rhs := mkApp (← mkAppM ``DFunLike.coe #[env.input, e]) (mkApp ix i)
    mkForallFVars #[e, i] (← mkEq lhs rhs)
  let hw ← proveResult hwTy k
  let proof ← mkAppM comb.reindex #[certificate, f, env.input, ix, hw]
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      mkLambdaFVars #[w, d, s] (← reduceProjections (args[8]!.beta #[w, argClean, s]))
  let work ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    mkLambdaFVars #[d, s] (← reduceProjections (args[9]!.beta #[argClean, s]))
  return { proof, output := args[7]!, safe, work }

/-- Field argument range `[lo, hi)` of a structure, tuple, sigma or `Matrix.vecCons` constructor
application. -/
private def compositeFieldRange? (env : Environment) (e : Expr) : Option (Nat × Nat) :=
  if e.isAppOfArity ``Matrix.vecCons 4 then some (2, 4)
  else if e.isAppOfArity ``Matrix.vecEmpty 1 then some (0, 0)
  else if let some ctorName := e.getAppFn.constName? then
    match env.find? ctorName with
    | some (.ctorInfo ci) =>
      if isStructure env ci.induct && ci.numFields > 0 &&
          e.getAppNumArgs == ci.numParams + ci.numFields then
        some (ci.numParams, ci.numParams + ci.numFields)
      else none
    | _ => none
  else none

/-- Find the first non-live `ℕ`-valued expression inside a tuple/structure/vector argument spine.
Returns `none` when no `ℕ` leaf decomposes cleanly, letting the caller fall back to whole-argument
staging. -/
private partial def findMissingNatLeaf? (atoms : Array Expr) (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if let some (lo, hi) := compositeFieldRange? (← getEnv) e then
    let args := e.getAppArgs
    for i in [lo : hi] do
      if let some m ← findMissingNatLeaf? atoms args[i]! then return some m
    return none
  if (← whnfR (← inferType e)).isConstOf ``Nat && (← findAtom atoms e).isNone then
    return some e
  return none

/-- Replace every occurrence of `target` inside the tuple/structure/`Matrix.vecCons` spine of `e`
with `repl` (keeping type parameters untouched). -/
private partial def replaceNatLeaf (e target repl : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e == target then return repl
  if let some (lo, hi) := compositeFieldRange? (← getEnv) e then
    let mut args := e.getAppArgs
    for i in [lo : hi] do
      args := args.set! i (← replaceNatLeaf args[i]! target repl)
    return mkAppN e.getAppFn args
  return e

/-- Stage only the non-live `ℕ` coordinates inside a wide composite argument `arg` one word at a
time, carrying `positions` directly so live coordinates (e.g. a 36-word parameter record) are
never re-analyzed or copied. -/
private partial def stageCallCoords (comb : Combinators) (env : Env) (d : Expr) (atoms : Array Expr)
    (arg methodCert : Expr) (k : Nat) (coords : Array Expr) (positions : Array (Option Nat))
    (stage : Env → Expr → Array Expr → Expr → Expr → TermElabM Out)
    (natEnc : Expr) (fuel : Nat := 16) : TermElabM (Option Out) := do
  if positions.all Option.isSome then
    return some (← reindexCall comb env d arg methodCert (positions.map Option.get!))
  if fuel == 0 then return none
  let some missing ← findMissingNatLeaf? atoms arg | return none
  let missingWhnf ← whnf missing
  -- Ensure `missing` actually covers at least one currently-`none` coordinate slot.
  let mut matchedAny := false
  let mut newPositions := positions
  for i in [0:k] do
    if positions[i]!.isNone then
      if coords[i]! == missingWhnf ||
          (← withNewMCtxDepth (isDefEq coords[i]! missingWhnf)) then
        newPositions := newPositions.set! i (some env.k)
        matchedAny := true
  unless matchedAny do return none
  let hP ← stage env d atoms missing natEnc
  let env' ← extend env (mkConst ``Nat) natEnc 1 (idNat := true)
  let hQ? ← withLocalDeclD `x env'.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    let argAtX1 := arg.replaceFVar d x1
    let missingAtX1 := missing.replaceFVar d x1
    let arg' ← replaceNatLeaf argAtX1 missingAtX1 x2
    if arg' == argAtX1 then return none
    unless ← isTypeCorrect arg' do return none
    let coords' := coords.map (·.replaceFVar d x1)
    let atoms' := env'.atoms.map (·.beta #[x])
    stageCallCoords comb env' x atoms' arg' methodCert k coords' newPositions
      stage natEnc (fuel - 1)
  let some hQ := hQ? | return none
  return some (← bindPureOut comb d missing hP hQ)

/-- Reuse a local method certificate before unfolding its body. Live arguments use static
wiring; otherwise a certified `pure` stage computes only the non-live scalar coordinates when the
argument decomposes along tuple/structure/vector constructors, falling back to whole-argument
staging in the callee's encoding. -/
private def tryRealizeCall (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr)
    (stage : Env → Expr → Array Expr → Expr → Expr → TermElabM Out) :
    TermElabM (Option Out) := do
  for (certExpr, args) in ← localCerts ctx do
    if let some out ← tryBacktrack? (do
      let some arg ← matchMethodCall args body | return none
      discard <| checkOutput ctx.comb certExpr output?
      let k ← encodingWidth args[6]!
      let coords ← encodingAtoms args[6]! arg k
      let positions ← coords.mapM fun a => liftMetaM (findAtom atoms a)
      if positions.all Option.isSome then
        return some (← reindexCall ctx.comb env d arg certExpr (positions.map Option.get!))
      -- Stage only the non-live `ℕ` leaves when `arg` decomposes along tuple/structure/vector
      -- constructors (e.g. a 36-word `DictParams` or `Fin k → ℕ` vector with live coordinates).
      if k > 1 || !(arg.isFVar || arg.isAppOf ``Prod.fst || arg.isAppOf ``Prod.snd) then
        if let some out ← tryBacktrack? (do
            let natEnc ← encodingOf (mkConst ``Nat)
            stageCallCoords ctx.comb env d atoms arg certExpr k
              coords positions stage natEnc (fuel := max 16 k)) then
          return some out
      -- Fallback: stage the typed argument in the callee's input encoding.
      let argClean ← etaContractStructures arg
      let hP ← stage env d atoms argClean args[6]!
      let env' ← extend env args[2]! args[6]! k
      let hQ ← withLocalDeclD `x env'.ty fun x => do
        reindexCall ctx.comb env' x (← mkAppM ``Prod.snd #[x]) certExpr
          ((Array.range k).map (env.k + ·))
      return some (← bindPureOut ctx.comb d argClean hP hQ)) then
      return some out
  return none

/-- Lift returned selections through their constructor/application context. Only the listed
equalities are used: arithmetic and method definitions are left for their existing rules. -/
private def normalizePure? (d : Expr) (atoms : Array Expr) (body : Expr) :
    TermElabM (Option Simp.Result) := do
  let interesting (e : Expr) : Bool :=
    e.isAppOfArity ``ite 5 || e.isAppOfArity ``decide 2 ||
      e.isAppOfArity ``Nat.min 2 || e.isAppOfArity ``Nat.max 2 ||
      ((e.isAppOfArity ``Min.min 4 || e.isAppOfArity ``Max.max 4) &&
        (e.getArg! 0).isConstOf ``Nat)
  if (body.appArg!.find? interesting).isNone then return none
  -- Constants and already encoded words remain glue values, including inside a mixed result.
  -- Expanding their selections would introduce comparisons and stronger fit obligations.
  let fixedOrLive (e : Expr) : MetaM Bool := do
    if !e.containsFVar d.fvarId! then return true
    -- Simp traverses reducibly; use the same transparency as the existing glue analysis.
    return (e.find? interesting).isSome &&
      (← withTransparency .default (findAtom atoms e)).isSome
  let mut thms : SimpTheorems := {}
  for name in [``Nat.min_def, ``Nat.max_def, ``ite_not] do
    thms ← thms.addConst name
  thms ← thms.addConst ``not_lt (inv := true)
  if (body.appArg!.find? (·.isAppOfArity ``decide 2)).isSome then
    let decideRule ← Term.elabTerm (← `(fun (p : Prop) [Decidable p] =>
      (show decide p = if p then true else false from by
        by_cases h : p
        · exact (decide_eq_true h).trans (ite_eq_left h).symm
        · exact (decide_eq_false h).trans (ite_eq_right h).symm))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    thms ← thms.add (.other `realize_decide) #[] (← instantiateMVars decideRule)
  let ctx ← Simp.mkContext
    (config := { dsimp := false, zeta := false, proj := false, iota := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let defaults := Simp.mkDefaultMethodsCore #[]
  let normalizeMethods : Simp.Methods := { defaults with
    pre := fun e => do
      if ← fixedOrLive e then return .done { expr := e }
      defaults.pre e }
  let (normalized, _) ← Simp.main body ctx (methods := normalizeMethods)
  let liftCtx := ctx.setSimpTheorems #[{}]
  let liftArgument (e : Expr) : MetaM (Option Simp.Result) := do
    let args := e.getAppArgs
    for h : i in [0:args.size] do
      let choice := args[i]
      unless choice.isAppOfArity ``ite 5 do continue
      if ← fixedOrLive choice then continue
      let f ← withLocalDeclD `selected (← inferType choice) fun selected => do
        mkLambdaFVars #[selected] (mkAppN e.getAppFn (args.set i selected))
      let proof ← mkAppOptM ``apply_ite #[none, none, f, choice.getArg! 1,
        choice.getArg! 2, choice.getArg! 3, choice.getArg! 4]
      let some (_, _, rhs) := (← inferType proof).eq?
        | throwError "realize: internal error lifting a conditional result"
      return some { expr := rhs, proof? := some proof }
    return none
  -- Stop at the first lifted choice. Traversing it would distribute one branch across
  -- another; its alternatives are instead certified recursively by the branch rule.
  let methods : Simp.Methods := { defaults with
    pre := fun e => do
      if e.isAppOfArity ``ite 5 || (← fixedOrLive e) then return .done { expr := e }
      defaults.pre e
    post := fun e => do
      if let some result ← liftArgument e then return .visit result
      defaults.post e }
  let (lifted, _) ← Simp.main normalized.expr liftCtx (methods := methods)
  if lifted.expr.isAppOfArity ``ite 5 then
    return some {
      expr := lifted.expr
      proof? := some (← mkEqTrans (← normalized.getProof) (← lifted.getProof)) }
  return none

/-- Simplify a mapped value for `pure`: apply `Option.map` to `some`, `none` and an optional
answer chosen by a (dependent) `if`, and drop the proof of a constructed `Fin`, so that a dependent
`if` whose branches no longer use its hypothesis becomes an ordinary one. -/
private def simpMappedValue (e : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for name in [``Option.map_some, ``Option.map_none, ``Option.map_ite, ``Option.map_dite,
      ``dite_eq_ite, ``Fin.val_mk] do
    thms ← thms.addConst name
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main (← Core.betaReduce e) ctx (methods := Simp.mkDefaultMethodsCore #[])).1

/-- Push the result map `lhs = f <$> m` one step into `m`, whose client form is `mR`, in the free
monad `M`: over a bind by `PFunctor.FreeM.map_bind`, over `pure` by `PFunctor.FreeM.map_pure` (by
`rfl`, then `simpMappedValue`), over an `if` by `apply_ite` and over another map by
`PFunctor.FreeM.comp_map`. Returns a proof of `lhs = rhs`, or `none` for any other form. The same
step serves a memory client and the source of a linked client. -/
private def pushMap? (M lhs f mR : Expr) : MetaM (Option Expr) := do
  let mapOf (g x : Expr) : MetaM Expr := mkAppM ``PFunctor.FreeM.map #[g, x]
  if let some (_, x, k) := bindArgs? mR then
    return some (← mkAppM ``PFunctor.FreeM.map_bind #[f, x, k])
  if let some a := pureArg? mR then
    let value ← simpMappedValue (mkApp f a)
    let pureOf (v : Expr) : MetaM Expr := mkAppOptM ``Pure.pure #[M, none, none, v]
    let rhs ← pureOf value.expr
    let eq ← match value.proof? with
      | none => mkEqRefl rhs
      | some pf => do
        let pureFn ← withLocalDeclD `v (← inferType value.expr) fun v => do
          mkLambdaFVars #[v] (← pureOf v)
        mkCongrArg pureFn pf
    return some (← mkExpectedTypeHint eq (← mkEq lhs rhs))
  if mR.isAppOfArity ``ite 5 then
    let mapFn ← withLocalDeclD `p (mR.getArg! 0) fun p => do
      mkLambdaFVars #[p] (← mapOf f p)
    return some (← mkAppOptM ``apply_ite
      #[none, none, mapFn, mR.getArg! 1, mR.getArg! 2, mR.getArg! 3, mR.getArg! 4])
  if isClientMap mR then
    let g := mR.appFn!.appArg!
    let x := mR.appArg!
    let eq ← mkEqSymm (← mkAppM ``PFunctor.FreeM.comp_map #[f, g, x])
    -- State the composite as a lambda, so that the mapped values beta-reduce.
    let fg ← withLocalDeclD `a (← resultType x) fun a => do
      mkLambdaFVars #[a] (mkApp f (mkApp g a).headBeta).headBeta
    let some (_, lhs', _) := (← inferType eq).eq? | throwError "realize: internal error"
    return some (← mkExpectedTypeHint eq (← mkEq lhs' (← mapOf fg x)))
  return none

mutual

/-- Stage a computed pure value `a` with explicit output encoding `output`. -/
private partial def stageValue (ctx : Ctx) (eEnv : Env) (eD : Expr) (eAtoms : Array Expr)
    (a output : Expr) : TermElabM Out := do
  let body ← mkAppOptM ``Pure.pure #[mkConst ``Memory.Prog, none, none, a]
  realizeBody ctx eEnv eD eAtoms body (some output)

/-- Certify a client `prog : δ → Memory.Prog α` in the environment `env`. -/
private partial def realizeProg (ctx : Ctx) (env : Env) (prog : Expr) (output? : Option Expr) :
    TermElabM Out :=
  withLocalDeclD `d env.ty fun d => do
    let atoms := env.atoms.map (·.beta #[d])
    let stepLoop : TermElabM Out := do
      let mut body := (prog.beta #[d]).headBeta
      for _ in [0:64] do
        if !isPrimitiveClientForm body then
          if let some out ← tryRealizeCall ctx env d atoms body output? (stageValue ctx) then
            return out
        let bodyR ← whnfR body
        if bodyR != body && !isPrimitiveClientForm bodyR then
          if let some out ← tryRealizeCall ctx env d atoms bodyR output? (stageValue ctx) then
            return out
        if isClientForm bodyR then
          return ← realizeBody ctx env d atoms bodyR output?
        if let some next ← unfoldDefinition? bodyR then
          body := next.headBeta
        else
          return ← realizeBody ctx env d atoms bodyR output?
      realizeBody ctx env d atoms (← whnfR body) output?
    let out ← stepLoop
    return { out with proof := ← certify ctx env out.proof prog out.output out.safe out.work }

/-- Certify a linked free-monad client `PFunctor.FreeM.liftM interp src` without unfolding `liftM`
to its recursor, preserving local certificate matches and closed-form memory states. -/
private partial def realizeLiftM (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let bArgs := body.getAppArgs
  let (P, m, α, instPure, instBind, interp) :=
    (bArgs[0]!, bArgs[1]!, bArgs[2]!, bArgs[3]!, bArgs[4]!, bArgs[5]!)
  let mkLift (ty src' : Expr) : Expr :=
    mkAppN body.getAppFn #[P, m, ty, instPure, instBind, interp, src']
  let congrFrom (rhs eqStep : Expr) : TermElabM Out := do
    let out ← realizeProg ctx env (← mkLambdaFVars #[d] rhs) output?
    let eq ← mkLambdaFVars #[d]
      (← mkExpectedTypeHint (← mkEqSymm eqStep) (← mkEq rhs body))
    return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, eq] }
  let distributeIte (choice f : Expr) : TermElabM Out := do
    let eqStep ← mkAppOptM ``apply_ite #[choice.getArg! 0, mkApp m α, f,
      choice.getArg! 1, choice.getArg! 2, choice.getArg! 3, choice.getArg! 4]
    let some (_, _, rhs) := (← inferType eqStep).eq?
      | throwError "realize: internal error lifting a linked conditional"
    congrFrom rhs eqStep
  let splitLiftMBind (β x k : Expr) : TermElabM Out := do
    let eqStep ← mkAppOptM ``PFunctor.FreeM.liftM_bind #[P, m, none, interp, none, β, α, x, k]
    let contLift ← withLocalDeclD `u β fun u =>
      mkLambdaFVars #[u] (mkLift α (mkApp k u).headBeta)
    let rhs ← mkAppOptM ``Bind.bind #[m, instBind, β, α, mkLift β x, contLift]
    congrFrom rhs eqStep
  let mut src := bArgs[6]!.headBeta
  for i in [0:64] do
    let srcR ← whnfR src
    if (i != 0 || srcR != src) && !isPrimitiveClientForm srcR then
      if let some out ← tryRealizeCall ctx env d atoms (mkLift α srcR) output? (stageValue ctx) then
        return out
    if let some a := pureArg? srcR then
      let pureBody ← mkAppOptM ``Pure.pure #[m, instPure, α, a]
      return ← realizeBody ctx env d atoms pureBody output?
    if srcR.isAppOfArity ``PFunctor.FreeM.lift 2 then
      let op := srcR.appArg!
      let eqStep ← mkAppOptM ``PFunctor.FreeM.liftM_lift #[P, m, none, none, interp, op]
      return ← congrFrom (← normInterpOp atoms (mkApp interp op)) eqStep
    if srcR.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
      let op := srcR.getArg! 2
      let cont := srcR.getArg! 3
      let first ← normInterpOp atoms (mkApp interp op)
      let domTy := (← whnf (← inferType cont)).bindingDomain!
      let contLift ← withLocalDeclD `u domTy fun u =>
        mkLambdaFVars #[u] (mkLift α (mkApp cont u).headBeta)
      return ← realizeBind ctx env d first contLift output?
    if srcR.isAppOfArity ``ite 5 then
      let srcTy := srcR.getArg! 0
      let liftFn ← withLocalDeclD `p srcTy fun p => mkLambdaFVars #[p] (mkLift α p)
      return ← distributeIte srcR liftFn
    -- `f <$> x` in `FreeM P`: push the map into `x`, or else out of the link
    if isClientMap srcR then
      let f := srcR.appFn!.appArg!
      let x := srcR.appArg!
      let β ← resultType x
      let mut xR? : Option Expr := none
      let mut cur := x.headBeta
      for _ in [0:64] do
        if !isPrimitiveClientForm cur && (← matchesLocalCert ctx (mkLift β cur)) then break
        let curR ← whnfR cur
        if isPrimitiveClientForm curR || isClientMap curR then
          xR? := some curR
          break
        let some next ← unfoldDefinition? curR | break
        cur := next.headBeta
      if let some xR := xR? then
        if let some eq ← pushMap? (← whnfR (← inferType srcR)).appFn! srcR f xR then
          let some (_, _, rhs) := (← inferType eq).eq?
            | throwError "realize: internal error pushing a map into a linked source"
          let liftWrap ← withLocalDeclD `q (← inferType srcR) fun q =>
            mkLambdaFVars #[q] (mkLift α q)
          let eqStep ← mkAppM ``congrArg #[liftWrap, eq]
          return ← congrFrom (mkLift α (← Core.betaReduce rhs)) eqStep
      -- `liftM interp (f <$> x) = liftM interp x >>= pure ∘ f`, certified through `liftM interp x`
      let eqOut ← mkAppOptM ``PFunctor.FreeM.liftM_map
        #[P, m, none, none, none, none, f, interp, x]
      let some (_, lhs, mapped) := (← inferType eqOut).eq?
        | throwError "realize: internal error moving a map out of a linked source"
      let eqBind ← mkAppM ``PFunctor.FreeM.bind_pure_comp #[f, mapped.appArg!]
      let some (_, bindForm, _) := (← inferType eqBind).eq?
        | throwError "realize: internal error moving a map out of a linked source"
      unless ← isDefEq lhs body do
        throwError "realize: internal error moving a map out of a linked source"
      let eq ← mkExpectedTypeHint (← mkEqTrans eqBind (← mkEqSymm eqOut)) (← mkEq bindForm body)
      let out ← realizeBind ctx env d mapped.appArg! bindForm.appArg! output?
      return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, ← mkLambdaFVars #[d] eq] }
    -- `x >>= k` in `FreeM P`
    if let some (β, x, k) := bindArgs? srcR then
      if ← matchesLocalCert ctx (mkLift β x) then
        return ← splitLiftMBind β x k
      let xR ← whnfR x
      if let some a := pureArg? xR then
        src := (mkApp k a).headBeta
        continue
      if xR.isAppOfArity ``PFunctor.FreeM.lift 2 then
        src := ← mkAppOptM ``PFunctor.FreeM.liftBind #[P, α, xR.appArg!, k]
        continue
      if xR.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
        let cont := xR.getArg! 3
        let domTy := (← whnf (← inferType cont)).bindingDomain!
        let cont' ← withLocalDeclD `u domTy fun u => do
          let bound ← mkAppOptM ``PFunctor.FreeM.bind #[P, β, α, (mkApp cont u).headBeta, k]
          mkLambdaFVars #[u] bound
        src := ← mkAppOptM ``PFunctor.FreeM.liftBind #[P, α, xR.getArg! 2, cont']
        continue
      if xR.isAppOfArity ``ite 5 then
        let bindLift ← withLocalDeclD `p (xR.getArg! 0) fun p => do
          let bound ← mkAppOptM ``PFunctor.FreeM.bind #[P, β, α, p, k]
          mkLambdaFVars #[p] (mkLift α bound)
        return ← distributeIte xR bindLift
      if let some (_, y, h) := bindArgs? xR then
        let eqInner ← mkAppM ``bind_assoc #[y, h, k]
        let some (_, _, innerRhs) := (← inferType eqInner).eq?
          | throwError "realize: internal error reassociating a linked bind"
        let liftWrap ← withLocalDeclD `q (← inferType srcR) fun q =>
          mkLambdaFVars #[q] (mkLift α q)
        return ← congrFrom (mkLift α innerRhs) (← mkAppM ``congrArg #[liftWrap, eqInner])
      if let some xNext ← unfoldDefinition? xR then
        src := ← mkAppOptM ``PFunctor.FreeM.bind #[P, β, α, xNext.headBeta, k]
        continue
      return ← splitLiftMBind β x k
    if let some next ← unfoldDefinition? srcR then
      src := next.headBeta
    else
      break
  throwError "realize: unsupported linked client form{indentExpr (mkLift α src)}"

/-- Certify the body of a client for the environment variable `d`. -/
private partial def realizeBody (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let realizeNormalized (normalized : Simp.Result) (outOpt : Option Expr) : TermElabM Out := do
    let out ← realizeBody ctx env d atoms normalized.expr outOpt
    let eq ← mkLambdaFVars #[d] (← mkEqSymm (← normalized.getProof))
    return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, eq] }
  let k := env.k
  -- linked free-monad source
  if body.isAppOfArity ``PFunctor.FreeM.liftM 7 then
    return ← realizeLiftM ctx env d atoms body output?
  if isClientMap body then return ← realizeMap ctx env d body output?
  -- sequencing
  if let some (_, m, f) := bindArgs? body then
    return ← realizeBind ctx env d m f output?
  if body.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    let m ← mkAppOptM ``PFunctor.FreeM.lift #[body.getArg! 0, body.getArg! 2]
    return ← realizeBind ctx env d m (body.getArg! 3) output?
  -- return
  if let some a := pureArg? body then
    let out ← output?.getDM (encodingOf (← resultType body))
    let saved ← saveState
    try
      return ← realizePure ctx env d atoms a out
    catch ex =>
      if ex.isInterrupt then throw ex
      saved.restore
      if let some normalized ← normalizePure? d atoms body then
        return ← realizeNormalized normalized (some out)
      throw ex
  -- memory queries
  if body.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR body.appArg!
    let operands := op.getAppArgs
    for h : j in [0:operands.size] do
      if (← findAtom atoms operands[j]).isNone then
        let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
          mkLambdaFVars #[r] (mkApp2 (mkConst ``PFunctor.FreeM.lift
            body.getAppFn.constLevels!) (body.getArg! 0) (mkAppN op.getAppFn (operands.set j r)))
        return ← realizeBody ctx env d atoms (← bindPure operands[j] rebuilt) output?
    let idx ← operands.mapM fun a => do
      let some i ← findAtom atoms a | throwError "realize: internal error"
      finLit k i
    let input := env.input
    let kE := mkNatLit k
    let proof ← match op.getAppFn.constName? with
      | some ``Memory.Op.read =>
        mkAppOptM ctx.comb.read #[ctx.basis, env.ty, kE, input, idx[0]!]
      | some ``Memory.Op.write =>
        mkAppOptM ctx.comb.write #[ctx.basis, env.ty, kE, input, idx[0]!, idx[1]!]
      | some ``Memory.Op.alloc =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `{ctx.comb.label}.mapSimulates`"
        mkAppOptM ctx.comb.alloc #[env.ty, kE, input, idx[0]!]
      | some ``Memory.Op.allocDirty =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `{ctx.comb.label}.mapSimulates`"
        mkAppOptM ctx.comb.allocDirty #[env.ty, kE, input, idx[0]!]
      | _ => throwError "realize: unsupported memory operation{indentExpr op}"
    let output ← checkOutput ctx.comb proof output?
    return { proof, output, safe := ← trueSafe env.ty, work := ← zeroWork env.ty }
  -- branching
  if body.isAppOfArity ``ite 5 then
    if (← cond? (body.getArg! 1)).isNone then
      if let some normalized ← normalizeBranch? body then
        return ← realizeNormalized normalized output?
    let c := body.getArg! 1
    let inst := body.getArg! 2
    let t := body.getArg! 3
    let e := body.getArg! 4
    let (kind, a, b) ← parseCond c
    let ia? ← findAtom atoms a
    let ib? ← findAtom atoms b
    let (some ia, some ib) := (ia?, ib?) | do
      let x := if ia?.isNone then a else b
      let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
        let c' ← if ia?.isNone then rebuildCond c r b else rebuildCond c a r
        mkLambdaFVars #[r] (← mkAppM ``ite #[c', t, e])
      let out ← realizeBody ctx env d atoms (← bindPure x rebuilt) output?
      let canonical := (rebuilt.beta #[x]).headBeta
      let hc ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq (canonical.getArg! 1) c)
      let eq ← mkLambdaFVars #[d] (← mkAppOptM ``ite_cond_congr
        #[body.getArg! 0, canonical.getArg! 1, c, canonical.getArg! 2, inst, t, e, hc])
      return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, eq] }
    let out ← output?.getDM (encodingOf (← resultType body))
    let hp ← realizeProg ctx env (← mkLambdaFVars #[d] t) (some out)
    let hn ← realizeProg ctx env (← mkLambdaFVars #[d] e) (some out)
    let cond ← mkAppM kind #[← finLit k ia, ← finLit k ib]
    let nativeCond ← mkAppM ``test #[cond, ← mkAppM ``DFunLike.coe #[env.input, d]]
    let nativeInst ← synthInstance (← mkAppM ``Decidable #[nativeCond])
    let hc ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq nativeCond c)
    let condCongr (α pos neg : Expr) : MetaM Expr :=
      mkAppOptM ``ite_cond_congr #[α, nativeCond, c, nativeInst, inst, pos, neg, hc]
    let state := mkConst ``Memory.State
    let nat := mkConst ``Nat
    let work ← withLocalDeclD `s state fun s => do
      mkLambdaFVars #[d, s] (← mkAppOptM ``ite
        #[nat, c, inst, hp.work.beta #[d, s], hn.work.beta #[d, s]])
    let proof ← if (← isZeroWork env.ty hp.work) && (← isZeroWork env.ty hn.work) then
        mkAppM ctx.comb.branch0 #[cond, hp.proof, hn.proof]
      else do
        let nativeWork ← withLocalDeclD `s state fun s => do
          mkLambdaFVars #[d, s] (← mkAppOptM ``ite
            #[nat, nativeCond, nativeInst, hp.work.beta #[d, s], hn.work.beta #[d, s]])
        let h ← absorbControl ctx.comb (← mkAppM ctx.comb.branch #[cond, hp.proof, hn.proof])
          nativeWork 2
        let workEq ← withLocalDeclD `s state fun s => do
          mkFunextN #[d, s] (← condCongr nat (hp.work.beta #[d, s]) (hn.work.beta #[d, s]))
        transportField h workEq 9
    let eq ← mkLambdaFVars #[d] (← condCongr (body.getArg! 0) t e)
    let proof ← mkAppM ctx.comb.congr #[proof, eq]
    let safe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
      mkLambdaFVars #[w, d, s] (mkApp5 (mkConst ``ite [Level.one]) (mkSort Level.zero) c inst
        (hp.safe.beta #[w, d, s]) (hn.safe.beta #[w, d, s]))
    let safeEq ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
      mkFunextN #[w, d, s]
        (← condCongr (mkSort Level.zero) (hp.safe.beta #[w, d, s]) (hn.safe.beta #[w, d, s]))
    let proof ← transportField proof safeEq 8
    return { proof, output := out, safe, work := ← certificateWork ctx.comb proof }
  -- a guarded loop
  if body.isAppOfArity ``boundedWhile 8 then
    return ← realizeWhile ctx env d atoms body output?
  -- a runtime-bounded loop
  if body.isAppOfArity ``iterate 6 then
    return ← realizeIterate ctx env d atoms (body.getArg! 1) (body.getArg! 2) (body.getArg! 3)
      (body.getArg! 4) (body.getArg! 5) output?
  -- a `match` on an optional answer becomes a test of its presence tag
  let body ← Core.betaReduce body
  if let some r ← optionDiscr? d body then
    return ← realizeOptionSplit ctx env d atoms body r output?
  throwError "realize: unsupported client form{indentExpr body}\n\
    Expected `bind`, `map`, `pure`, a memory query, `if` on a word comparison,\n\
    a `match` on an optional answer, `iterate` or `boundedWhile`.\n\
    Write recursion on a runtime value as one of these loops."

/-- Certify a result map `f <$> p` or `p.map f`.

A map over a `bind`, `pure`, `if` or another map is pushed into the client
(`PFunctor.FreeM.map_bind`, `PFunctor.FreeM.map_pure`, `apply_ite`, `PFunctor.FreeM.comp_map`), so
only the returned values are mapped and the mapped-over answer needs no word encoding. A map over
a linked client `liftM interp src` moves into its source (`PFunctor.FreeM.liftM_map`), where
`realizeLiftM` pushes it further. A map over any other client (a certified method, a query or a
loop) is `p >>= pure ∘ f` (`PFunctor.FreeM.bind_pure_comp`) and reuses the certificate for
`p`. -/
private partial def realizeMap (ctx : Ctx) (env : Env) (d : Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let f := body.appFn!.appArg!
  let m := body.appArg!
  -- Certify `rhs` and transport along `eq : body' = rhs`, where `body'` unfolds to `body`.
  let congrFrom (eq : Expr) : TermElabM Out := do
    let some (_, _, rhs) := (← inferType eq).eq?
      | throwError "realize: internal error rewriting a result map"
    let rhs ← Core.betaReduce rhs
    let out ← realizeProg ctx env (← mkLambdaFVars #[d] rhs) output?
    let eq ← mkLambdaFVars #[d] (← mkExpectedTypeHint (← mkEqSymm eq) (← mkEq rhs body))
    return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, eq] }
  -- The client form of `m`, unless `m` is a call that a local certificate covers.
  let mut mR? : Option Expr := none
  if isPrimitiveClientForm m || !(← matchesLocalCert ctx m) then
    let mut cur := m.headBeta
    for _ in [0:64] do
      let curR ← whnfR cur
      if isClientForm curR then
        mR? := some curR
        break
      if !isPrimitiveClientForm curR && (← matchesLocalCert ctx curR) then break
      let some next ← unfoldDefinition? curR | break
      cur := next.headBeta
  if let some mR := mR? then
    if let some eq ← pushMap? (mkConst ``Memory.Prog) body f mR then
      return ← congrFrom eq
    -- A map over a linked client moves into its source (`PFunctor.FreeM.liftM_map`).
    if mR.isAppOfArity ``PFunctor.FreeM.liftM 7 then
      let eq ← mkEqSymm (← mkAppOptM ``PFunctor.FreeM.liftM_map
        #[mR.getArg! 0, mR.getArg! 1, none, none, none, none, f, mR.getArg! 5, mR.getArg! 6])
      let some (_, lhs, _) := (← inferType eq).eq? | throwError "realize: internal error"
      if ← isDefEq lhs body then
        return ← congrFrom eq
  let eq ← mkAppM ``PFunctor.FreeM.bind_pure_comp #[f, m]
  let some (_, bind, _) := (← inferType eq).eq?
    | throwError "realize: internal error expanding a result map"
  let out ← realizeBind ctx env d m bind.appArg! output?
  return { out with proof := ← mkAppM ctx.comb.congr #[out.proof, ← mkLambdaFVars #[d] eq] }

/-- Certify a client that matches on the optional answer `r`: it equals the branch on `r`'s
presence tag, with `r` replaced by `none` and by `some` of its payload. -/
private partial def realizeOptionSplit (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body r : Expr) (output? : Option Expr) : TermElabM Out := do
  let rTy ← whnfR (← inferType r)
  let enc ← encodingOf rTy
  let words ← mkAppM ``DFunLike.coe #[enc, r]
  let l ← encodingWidth enc
  let payloadTy ← whnfR rTy.appArg!
  let payload ← if payloadTy.isConstOf ``Nat then
      unless l == 2 do
        throwError "realize: expected a tag and payload encoding for{indentExpr r}"
      pure (mkApp words (← finLit l 1))
    else if let some (a, b) := payloadTy.app2? ``Prod then
      unless (← whnfR a).isConstOf ``Nat && (← whnfR b).isConstOf ``Nat do
        throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
      unless l == 3 do
        throwError "realize: expected a tag and two payload words for{indentExpr r}"
      mkAppM ``Prod.mk #[mkApp words (← finLit l 1), mkApp words (← finLit l 2)]
    else
      throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
  let tag := mkApp words (← finLit l 0)
  let cond ← mkEq tag (← mkNumeral (mkConst ``Nat) 0)
  let noneE ← mkAppOptM ``Option.none #[rTy.appArg!]
  let someE ← mkAppM ``Option.some #[payload]
  let bodyNone := body.replace fun e => if e == r then some noneE else none
  let bodySome := body.replace fun e => if e == r then some someE else none
  let rhs ← mkAppM ``ite #[cond, bodyNone, bodySome]
  let eq ← proveSplit d r (← mkForallFVars #[d] (← mkEq rhs body))
  let out ← realizeBody ctx env d atoms rhs output?
  let h ← certify ctx env out.proof (← mkLambdaFVars #[d] rhs) out.output out.safe out.work
  let proof ← mkAppM ctx.comb.congr #[h, eq]
  return { out with proof }

/-- Certify `iterate step D n a`: copy the initial state and fuel, then run over the whole
environment (`iterate_congr`). Retain iteration work unless a query pays for each iteration. -/
private partial def realizeIterate (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (σ step D n a : Expr) (output? : Option Expr) : TermElabM Out := do
  unless ctx.exact do throwError "realize: loops are certified in the exact basis"
  let out ← output?.getDM (encodingOf σ)
  let l ← encodingWidth out
  let envB ← extend env σ out l
  let captured := step.containsFVar d.fvarId!
  -- the body over the whole environment
  let body ← if D == d && !captured then pure step else
    withLocalDeclD `x envB.ty fun x => do
      let x1 ← mkAppM ``Prod.fst #[x]
      let x2 ← mkAppM ``Prod.snd #[x]
      let Dx := (← mkLambdaFVars #[d] D).beta #[x1]
      mkLambdaFVars #[x] (mkApp (step.replaceFVar d x1) (← mkAppM ``Prod.mk #[Dx, x2]))
  let hB ← realizeProg ctx envB body (some out)
  let hq? ← queryPayment? body envB.ty hB.work
  let hLoop ← match hq? with
    | some hq => mkAppM ctx.comb.iterate0 #[env.input, out, hB.proof, hq]
    | none => mkAppM ctx.comb.iterateRuntime #[env.input, out, hB.proof]
  -- the fuel, after the state, then the initial state
  let word ← encodingOf (mkConst ``Nat)
  let (hN, h2) ← withLocalDeclD `x envB.ty fun x => do
    let nx := (← mkLambdaFVars #[d] n).beta #[← mkAppM ``Prod.fst #[x]]
    let hN ← realizePure ctx envB x (envB.atoms.map (·.beta #[x])) nx word
    return (hN, ← bindPureProof ctx.comb x nx hN.proof hLoop)
  let hA ← realizePure ctx env d atoms a out
  let proof ← bindPureProof ctx.comb d a hA.proof h2
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  let safe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reduceProjections (hN.safe.beta #[w, pair, s])
    let sl ← mkAppM ``iterationSafe #[body, hB.safe, w, d, n, a, s]
    mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let progR ← mkLambdaFVars #[d] (← mkAppM ``iterate #[body, d, n, a])
  let work ← certificateWork ctx.comb proof
  let proof ← certify ctx env proof progR out safe work
  if D == d && !captured then return { proof, output := out, safe, work }
  -- The adapted step agrees at this fixed environment, including any captured values.
  let hbody ← withLocalDeclD `x σ fun x => do
    let lhs := mkApp body (← mkAppM ``Prod.mk #[d, x])
    let rhs := mkApp step (← mkAppM ``Prod.mk #[D, x])
    mkLambdaFVars #[x] (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  let eq ← mkLambdaFVars #[d] (← mkAppOptM ``iterate_congr
    #[env.ty, σ, ← inferType D, body, step, d, D, hbody, n, a])
  let proof ← mkAppM ctx.comb.congr #[proof, eq]
  let pairTy ← mkAppM ``Prod #[← inferType D, σ]
  -- Keep the grade in the original loop's terms, including a captured environment.
  let (proof, work) ← if hq?.isSome then pure (proof, work) else do
    let (clientWork, hw) ← adaptLoopWork pairTy σ d D hB.work
    let work' ← withLocalDeclD `s state fun s => do
      mkLambdaFVars #[d, s] (← mkAppM ``iterationWork #[step, clientWork, D, n, a, s])
    let workEq ← withLocalDeclD `s state fun s => do
      let h ← mkAppOptM ``iterationWork_congr
        #[env.ty, σ, ← inferType D, body, step, hB.work, clientWork, d, D, hbody, hw, n, a, s]
      mkFunextN #[d, s] (← mkExpectedTypeHint h (← mkEq (work.beta #[d, s]) (work'.beta #[d, s])))
    pure (← transportField proof workEq 9, work')
  if !captured then return { proof, output := out, safe, work }
  -- State the reached-state domain in the original loop's terms, as in `realizeWhile`.
  let clientSafe ← adaptLoopSafe pairTy d hB.safe
  let safe' ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reduceProjections (hN.safe.beta #[w, pair, s])
    let sl ← mkAppM ``iterationSafe #[step, clientSafe, w, D, n, a, s]
    mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let safeEq ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let hs ← withLocalDeclD `x σ fun x => withLocalDeclD `t state fun t => do
      let lhs := hB.safe.beta #[w, ← mkAppM ``Prod.mk #[d, x], t]
      let rhs := clientSafe.beta #[w, ← mkAppM ``Prod.mk #[D, x], t]
      mkLambdaFVars #[x, t] (← mkExpectedTypeHint (← mkAppOptM ``Iff.rfl #[lhs])
        (mkApp2 (mkConst ``Iff) lhs rhs))
    let h ← mkAppOptM ``iterationSafe_congr
      #[env.ty, σ, ← inferType D, body, step, hB.safe, clientSafe, w, d, D, hbody, hs, n, a, s]
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reduceProjections (hN.safe.beta #[w, pair, s])
    let wrap ← withLocalDeclD `p (mkSort Level.zero) fun p =>
      mkLambdaFVars #[p] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn p))
    mkFunextN #[w, d, s] (← mkAppM ``congrArg #[wrap, ← mkAppM ``propext #[h]])
  let proof ← transportField proof safeEq 8
  return { proof, output := out, safe := safe', work }

/-- Certify `boundedWhile G step D n a` for the environment variable `d`.

The guard becomes a native comparison of the live words and the state's words. An operand that
does not depend on the state, such as the `0` of `0 < r`, is computed first into one more live
word. The body runs over the environment and state, retaining `whileWork` unless its zero work
and initial query justify `while₀`. The cutoff `n` is a ghost bound: it is never computed.
The certificate is transported to the client's own guard, step and loop environment `D`
(`boundedWhile_congr`, `whileSafe_imp`), and the loop's domain may assume the loop's valid history
(`consequence_valid`), which `whileSafe_of_measure` uses. -/
private partial def realizeWhile (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let args := body.getAppArgs
  let (Δ, σ, G, inst, step, D, n, a) :=
    (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
  let out ← output?.getDM (encodingOf σ)
  let l ← encodingWidth out
  let k := env.k
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  -- the comparison, its operands among the live words and the state's words (`none` for a
  -- computed operand), the computed operand, and the source-to-native guard equivalence
  let (kind, posA, posB, pre?, guardIff) ← withLocalDeclD `a σ fun x => do
    let (kind, oa, ob, hg) ← parseGuard (mkApp2 G D x)
    let words := atoms ++ (← encodingAtoms out x l)
    let locate (o : Expr) : MetaM (Option Nat) := do
      if let some i ← findAtom words o then return some i
      if o.containsFVar x.fvarId! then
        throwError "realize: a loop guard compares words; the operand{indentExpr o}\n\
          depends on the loop state but is not one of its words"
      return none
    let (ia, ib) := (← locate oa, ← locate ob)
    let pre? ← match ia, ib with
      | none, none => throwError "realize: the loop guard{indentExpr (mkApp2 G D x)}\n\
          does not depend on the loop state"
      | none, _ => pure (some oa)
      | _, none => pure (some ob)
      | _, _ => pure none
    return (kind, ia, ib, pre?, ← mkLambdaFVars #[x] hg)
  let word ← encodingOf nat
  let envP ← if pre?.isSome then extend env nat word 1 else pure env
  let cmp := envP.k + l
  let pos (i? : Option Nat) : MetaM Expr := finLit cmp <| match i? with
    | none => k
    | some i => if i < k || pre?.isNone then i else i + 1
  let cond ← mkAppM kind #[← pos posA, ← pos posB]
  -- `X` at the loop environment `e`, whose first component is `d` when an operand is computed
  let atEnv (X e : Expr) : MetaM Expr := do
    return X.replaceFVar d (← if pre?.isSome then mkAppM ``Prod.fst #[e] else pure e)
  -- the body over the loop environment and the state, and the ghost cutoff
  let envB ← extend envP σ out l
  let (bodyN, cutoff) ← withLocalDeclD `y envB.ty fun y => do
    let e ← mkAppM ``Prod.fst #[y]
    let x ← mkAppM ``Prod.mk #[← atEnv D e, ← mkAppM ``Prod.snd #[y]]
    return (← mkLambdaFVars #[y] (mkApp (← atEnv step e) x), ← mkLambdaFVars #[y] (← atEnv n e))
  let hB ← realizeProg ctx envB bodyN (some out)
  let hq? ← queryPayment? bodyN envB.ty hB.work
  let hLoop ← match hq? with
    | some hq => mkAppM ctx.comb.while0 #[envP.input, out, cond, cutoff, hB.proof, hq]
    | none => mkAppM ctx.comb.whileBounded #[envP.input, out, cond, cutoff, hB.proof]
  -- the initial state, then the loop
  let (hA, h) ← withLocalDeclD `e envP.ty fun e => do
    let ae ← atEnv a e
    let hA ← realizePure ctx envP e (envP.atoms.map (·.beta #[e])) ae out
    return (hA, ← bindPureProof ctx.comb e ae hA.proof hLoop)
  -- the computed operand, then the initial state and the loop
  let (hC?, h, e₀) ← match pre? with
    | none => pure (none, h, d)
    | some c => do
      let hC ← realizePure ctx env d atoms c word
      pure (some hC, ← bindPureProof ctx.comb d c hC.proof h, ← mkAppM ``Prod.mk #[d, c])
  -- the native guard at the loop environment, and its agreement with the client's
  let (gN, iN) ← withLocalDeclD `e envP.ty fun e => withLocalDeclD `a σ fun x => do
    let words ← mkAppM ``DFunLike.coe
      #[← mkAppM ``appendWords #[envP.input, out], ← mkAppM ``Prod.mk #[e, x]]
    let t ← mkAppM ``test #[cond, words]
    return (← mkLambdaFVars #[e, x] t,
      ← mkLambdaFVars #[e, x] (← synthInstance (← mkAppM ``Decidable #[t])))
  let (hgU, hgN, hbU, hbN) ← withLocalDeclD `a σ fun x => do
    let gU := mkApp2 G D x
    let gn := mkApp2 gN e₀ x
    let hgU ← mkExpectedTypeHint (guardIff.beta #[x]) (mkApp2 (mkConst ``Iff) gU gn)
    let bU := mkApp step (← mkAppM ``Prod.mk #[D, x])
    let bN := mkApp bodyN (← mkAppM ``Prod.mk #[e₀, x])
    let hbU ← mkExpectedTypeHint (← mkEqRefl bU) (← mkEq bU bN)
    return (← mkLambdaFVars #[x] hgU, ← mkLambdaFVars #[x] (← mkAppM ``Iff.symm #[hgU]),
      ← mkLambdaFVars #[x] hbU, ← mkLambdaFVars #[x] (← mkEqSymm hbU))
  -- the client's loop
  let prog := (← instantiateMVars (← inferType h)).getArg! 5
  let eq ← mkLambdaFVars #[d] (← mkExpectedTypeHint
    (← mkAppOptM ``boundedWhile_congr #[envP.ty, Δ, σ, gN, iN, G, inst, bodyN, step, e₀, D,
      hgN, hbN, n, a])
    (← mkEq (mkApp prog d) body))
  let h ← mkAppM ctx.comb.congr #[h, eq]
  -- the domain in the client's terms: the body's domain at the client's loop environment
  let pairTy ← mkAppM ``Prod #[Δ, σ]
  let safeB ← adaptLoopSafe pairTy e₀ hB.safe
  let safe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let spec ← mkAppM ``Memory.spec #[w]
    let valid ← mkAppM ``StateTransitionSpec.ValidHistory
      #[spec, s, ← mkAppM ``StateTransitionSpec.clientHistory #[spec, s, body]]
    let loop ← mkArrow valid
      (← mkAppOptM ``whileSafe #[Δ, σ, G, inst, step, safeB, w, D, n, a, s])
    let dom := mkAnd (← reduceProjections (hA.safe.beta #[w, e₀, s])) loop
    mkLambdaFVars #[w, d, s] <| match hC? with
      | some hC => mkAnd (hC.safe.beta #[w, d, s]) dom
      | none => dom
  -- the client's domain implies the native one under the loop's valid history
  let cv ← mkAppOptM ctx.comb.consequenceValid
    #[none, none, none, none, none, none, none, none, none, none, safe, h]
  let hsafeTy := (← whnf (← inferType cv)).bindingDomain!
  let hsafe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    forallBoundedTelescope (← instantiateForall hsafeTy #[w, d, s]) (some 4) fun hs goal => do
      let #[_, _, hv, hd] := hs | throwError "realize: internal error in the loop domain"
      let part (h : Expr) : MetaM (Expr × Expr) := do
        return (← mkAppM ``And.left #[h], ← mkAppM ``And.right #[h])
      let (hcs, rest) ← match hC? with
        | some _ => do let (p, q) ← part hd; pure (some p, q)
        | none => pure (none, hd)
      let (has, hloop) ← part rest
      let hsU ← withLocalDeclD `a σ fun x => withLocalDeclD `s state fun s' =>
        withLocalDeclD `hg (mkApp2 G D x) fun hg => do
          let hs := mkApp3 safeB w (← mkAppM ``Prod.mk #[D, x]) s'
          withLocalDeclD `h hs fun hh => do
            let hN := mkApp3 hB.safe w (← mkAppM ``Prod.mk #[e₀, x]) s'
            mkLambdaFVars #[x, s', hg, hh] (← mkExpectedTypeHint hh hN)
      let ws ← mkAppOptM ``whileSafe_imp #[Δ, envP.ty, σ, G, inst, gN, iN, step, bodyN, D, e₀,
        safeB, hB.safe, w, hgU, hbU, hsU, none, none, none, mkApp hloop hv]
      let dom ← mkAppM ``And.intro #[has, ws]
      let pf ← match hcs with
        | some p => mkAppM ``And.intro #[p, dom]
        | none => pure dom
      mkLambdaFVars (#[w, d, s] ++ hs) (← mkExpectedTypeHint pf goal)
  let proof := mkApp cv hsafe
  let work ← certificateWork ctx.comb proof
  if hq?.isSome then return { proof, output := out, safe, work }
  let (clientWork, hw) ← adaptLoopWork pairTy σ e₀ D hB.work
  let work' ← withLocalDeclD `s state fun s => do
    mkLambdaFVars #[d, s] (← mkAppOptM ``whileWork
      #[Δ, σ, G, inst, step, clientWork, D, n, a, s])
  let workEq ← withLocalDeclD `s state fun s => do
    let h ← mkAppOptM ``whileWork_congr
      #[envP.ty, Δ, σ, gN, iN, G, inst, bodyN, step, e₀, D, hB.work, clientWork,
        hgN, hbN, hw, n, a, s]
    mkFunextN #[d, s] (← mkExpectedTypeHint h (← mkEq (work.beta #[d, s]) (work'.beta #[d, s])))
  return { proof := ← transportField proof workEq 9, output := out, safe, work := work' }

/-- Certify `bind m f`: the first client, then the continuation over the extended environment. -/
private partial def realizeBind (ctx : Ctx) (env : Env) (d m f : Expr) (output? : Option Expr) :
    TermElabM Out := do
  let α ← resultType m
  let hP ← realizeProg ctx env (← mkLambdaFVars #[d] m) none
  let l ← encodingWidth hP.output
  let env' ← extend env α hP.output l
  let fd ← mkLambdaFVars #[d] f
  let q ← withLocalDeclD `x env'.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    mkLambdaFVars #[x] (fd.beta #[x1, x2]).headBeta
  let hQ ← realizeProg ctx env' q output?
  -- the reply and next memory in the client's terms, so that the domain is stated in them
  let (reply, next) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let (r, s') ← replyState m s
    return (← mkLambdaFVars #[d, s] r, ← mkLambdaFVars #[d, s] s')
  let proof ← bindRun ctx.comb hP.proof hQ.proof reply next
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, reply.beta #[d, s]]
      let sq ← reduceProjections (hQ.safe.beta #[w, pair, next.beta #[d, s]])
      mkLambdaFVars #[w, d, s] (mkAnd (hP.safe.beta #[w, d, s]) sq)
  return { proof, output := hQ.output, safe, work := ← certificateWork ctx.comb proof }

end

/-- Split the conjunctions and `if`s of a synthesized domain into separate goals. -/
private partial def splitDomain (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if t.isAppOfArity ``And 2 then
    let [g₁, g₂] ← g.apply (mkConst ``And.intro) | throwError "realize: internal split error"
    return (← splitDomain g₁) ++ (← splitDomain g₂)
  if t.isAppOfArity ``ite 5 then
    let c := t.getArg! 1
    let (gpos, gneg) ← g.byCases c `hc
    let pos ← gpos.mvarId.withContext do
      let eq ← mkAppOptM ``if_pos
        #[c, t.getArg! 2, mkFVar gpos.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gpos.mvarId.replaceTargetEq (t.getArg! 3) eq
    let neg ← gneg.mvarId.withContext do
      let eq ← mkAppOptM ``if_neg
        #[c, t.getArg! 2, mkFVar gneg.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gneg.mvarId.replaceTargetEq (t.getArg! 4) eq
    return (← splitDomain pos) ++ (← splitDomain neg)
  return [g]

/-- Present an entry obligation in the same source context as its domain and work budget. -/
private def entryGoal (g : MVarId) (keepHistory : Bool) : MetaM MVarId := do
  let (xs, g) ← g.introN 7 [`w, `d, `s, `hwords, `hmem, `hv, `h]
  -- Preserve the existing zero-work context: clients may introduce their own `hv` from `h`.
  let g ← if keepHistory then pure g else g.clear xs[5]!
  g.withContext do
    let g ← g.replaceTargetDefEq (← Core.betaReduce (← g.getType))
    let hdecl := (← getLCtx).lastDecl.get!
    g.replaceLocalDeclDefEq hdecl.fvarId (← Core.betaReduce hdecl.type)

/-- Prove a goal matching `comb.cert B p input output safe work`, leaving genuine fit, domain and
budget conditions in the entry context, with valid history also available for nonzero generated
work. -/
def elabRealize (comb : Combinators) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← whnfR (← goal.getType))
  unless target.isAppOfArity comb.cert 10 do
    throwError "realize: the goal is not a `{comb.label}` certificate:{indentExpr target}"
  let args := target.getAppArgs
  let δ := args[2]!
  let B := args[4]!
  let p := args[5]!
  let input := args[6]!
  let output := args[7]!
  let k ← encodingWidth input
  let exact ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.exact))
  let standard ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.standard))
  let atoms ← withLocalDeclD `d δ fun d => do
    (← encodingAtoms input d k).mapM (mkLambdaFVars #[d] ·)
  let env : Env := { ty := δ, k, input, atoms }
  -- `realizeProg` states the certificate for `p` itself, with the domain `out.safe`
  let out ← realizeProg { comb, basis := B, exact, standard } env p (some output)
  let cons ← mkAppOptM comb.consequenceWork
    #[B, δ, args[3]!, args[0]!, args[1]!, p, input, output, out.safe, args[8]!,
      out.work, args[9]!, out.proof]
  let [hsafe, hwork] ← goal.apply cons | throwError "realize: internal error in `consequence`"
  setGoals [hwork]
  let zero ← isZeroWork δ out.work
  if zero then
    evalTactic (← `(tactic| exact fun _ _ _ _ _ _ _ => Nat.zero_le _))
  else
    evalTactic (← `(tactic| try exact fun _ _ _ _ _ _ _ => le_rfl))
  let workGoals ← (← getGoals).mapM fun g => liftMetaM (entryGoal g true)
  let g ← entryGoal hsafe (!zero)
  setGoals [g]
  evalTactic (← `(tactic|
    try simp only [true_and, and_true, and_self, Nat.add_zero, iterationSafe_true]))
  let gs ← getGoals
  let gs ← gs.flatMapM fun g => liftMetaM (splitDomain g)
  -- A condition repeated in the same local context is proved once.
  let mut kept : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let lctx := (← g.getDecl).lctx
    let dup? ← kept.findM? fun g' => do
      return (← g'.getDecl).lctx.getFVarIds == lctx.getFVarIds &&
        (← instantiateMVars (← g'.getType)) == t
    match dup? with
    | some g' => g.assign (mkMVar g')
    | none => kept := kept.push g
  setGoals (kept.toList ++ workGoals)

end Cslib.Tactic.Realize

namespace Cslib.WordRAM

open Lean Elab Tactic Cslib.Tactic.Realize in
/-- Prove `Realizes B p input output safe work`, leaving genuine fit, domain and budget
conditions in the entry context, with valid history also available for nonzero generated work. -/
scoped elab "realize" : tactic =>
  elabRealize unboundedCombinators

/-- Supply method certificates as local facts before running `realize`. -/
scoped macro "realize" "[" certificates:term,* "]" : tactic => do
  let mut script ← `(tactic| realize)
  for certificate in certificates.getElems.reverse do
    script ← `(tactic| (have hcert := $certificate; $script))
  return script

/-- `realize [c₁, …] rewriting [r₁, …]` first rewrites the client, under its environment binder,
with `simp only [r₁, …]`, and then runs `realize [c₁, …]`; the certificate list may be omitted.
It stages a client whose syntax must be restated before it can be certified: a recursion replaced
by its loop, definitions unfolded with a repeated subterm folded, or a client equation proved
beforehand. Only the client is rewritten, not the domain or the work. -/
scoped syntax "realize" (" [" term,* "]")? " rewriting " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic

macro_rules
  | `(tactic| realize $[[$certificates,*]]? rewriting [$rules,*]) => do
    let certificates := certificates.map (·.getElems) |>.getD #[]
    `(tactic| (conv => arg 2; ext d; simp only [$rules,*]); realize [$certificates,*])

end Cslib.WordRAM
