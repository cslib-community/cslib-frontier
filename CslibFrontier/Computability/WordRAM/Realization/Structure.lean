/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Backend
public meta import Lean.Elab.Command

/-!
# Word encodings of structures as the tuple of their fields

`word_enc_structure eS : S where f₁ : e₁, …, fₙ : eₙ` declares a faithful finite-register word
encoding `eS : S ↪ (Fin k → ℕ)` of a one-constructor `structure` `S` from explicit per-field
word encodings `eᵢ : Fᵢ ↪ (Fin kᵢ → ℕ)` (or explicit `WordEncoding Fᵢ` values), mirroring
`Turing.MultiTapeTM.enc_structure` without hidden default-encoding typeclass search:

* `eSFields`, the left-associated `appendWords` encoding of the field tuple, and `eS`, the
  combined `S ↪ (Fin k → ℕ)` embedding proved injective structurally without `fin_cases`;
* `eS_apply`, unfolding `eS a` to `eSFields` applied to the tuple of field values;
* when every field width reduces to a numeral (`k = k₁ + ⋯ + kₙ`), `@[simp]` coordinate
  equations `eS_coord_0`, …, `eS_coord_{k-1}` whose right-hand sides are normalized through nested
  `wordWords`, `blockWords` and `word_enc_structure` projections;
* per-field slice equations `eS_<field>` (marked `@[simp]` when widths are symbolic) and the
  word-fit composition lemma `eS_fits`.

Applied structure types with implicit `variable` parameters (`word_enc_structure eL : Layout n`),
explicit command parameters `(p : T)` before `:`, flattened parent structures, and dependent fields
`f : w using hw` (encoding `f` as the scalar word `w f` for an injective `w` reading earlier
fields by name) follow the same conventions as `enc_structure`. Supporting `@[simp]` coordinate
and slice equations (`blockWords_zero`, `blockWords_one`, `appendWords_castAdd`,
`appendWords_natAdd`, `appendWords_addNat`, `sigmaWords_castAdd`, `sigmaWords_natAdd`,
`sigmaWords_addNat`) and word-fit helpers (`blockWords_fits`, `fits_sigmaWords`) normalize encoded
slices and compose `Fits` bounds across `Block`, `appendWords` and `sigmaWords`.

## Main definitions

* `wordWords`: the one-word scalar encoding `ℕ ↪ (Fin 1 → ℕ)`.
* `sigmaWords`: fixed-fiber-width dependent-pair word encoding `(Σ a, β a) ↪ (Fin (k + l) → ℕ)`.
-/

public section

namespace Cslib.WordRAM.Realization

/-- The single-word encoding of a natural number, definitionally equal to
`WordEncoding.encode (α := ℕ)`. -/
abbrev wordWords : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- Coordinate zero of `blockWords` is the block's base address. -/
@[simp] theorem blockWords_zero (b : Block) : blockWords b 0 = b.base := rfl

/-- Coordinate one of `blockWords` is the block's length. -/
@[simp] theorem blockWords_one (b : Block) : blockWords b 1 = b.length := rfl

/-- Both words of `blockWords b` fit in `w` bits when `b.base` and `b.length` do. -/
theorem blockWords_fits {w : ℕ} {b : Block} (hbase : Fits w b.base) (hlen : Fits w b.length) :
    ∀ i, Fits w (blockWords b i) :=
  Fin.cases hbase fun i => Fin.cases hlen (fun j => j.elim0) i

/-- The left slice of `appendWords` reads the first component's encoding. -/
@[simp] theorem appendWords_castAdd {δ α : Type} {k l : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ)) (p : δ × α) (i : Fin k) :
    appendWords input output p (Fin.castAdd l i) = input p.1 i := by
  simp [appendWords, Fin.appendEquiv]

/-- The right slice of `appendWords` reads the second component's encoding. -/
@[simp] theorem appendWords_natAdd {δ α : Type} {k l : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin l → ℕ)) (p : δ × α) (j : Fin l) :
    appendWords input output p (Fin.natAdd k j) = output p.2 j := by
  simp [appendWords, Fin.appendEquiv]

/-- Equal-width `addNat` normal-form companion of `appendWords_natAdd`. -/
@[simp] theorem appendWords_addNat {δ α : Type} {k : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : α ↪ (Fin k → ℕ)) (p : δ × α) (j : Fin k) :
    appendWords input output p (j.addNat k) = output p.2 j := by
  rw [← Fin.natAdd_eq_addNat, appendWords_natAdd]

/-- Faithfully encode a dependent pair whose second component has a fixed register width `l`
independent of the first component. -/
@[expose] def sigmaWords {α : Type} {β : α → Type} {k l : ℕ}
    (fst : α ↪ (Fin k → ℕ)) (snd : ∀ a, β a ↪ (Fin l → ℕ)) :
    (Σ a, β a) ↪ (Fin (k + l) → ℕ) where
  toFun p := Fin.appendEquiv k l (fst p.1, snd p.1 p.2)
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hp := (Fin.appendEquiv k l).injective h
    have ha : a = a' := fst.injective (congrArg Prod.fst hp)
    subst ha
    exact congrArg (Sigma.mk a) ((snd a).injective (congrArg Prod.snd hp))

/-- The left slice of `sigmaWords` reads the first component's encoding. -/
@[simp] theorem sigmaWords_castAdd {α : Type} {β : α → Type} {k l : ℕ}
    (fst : α ↪ (Fin k → ℕ)) (snd : ∀ a, β a ↪ (Fin l → ℕ)) (p : Σ a, β a) (i : Fin k) :
    sigmaWords fst snd p (Fin.castAdd l i) = fst p.1 i := by
  simp [sigmaWords, Fin.appendEquiv]

/-- The right slice of `sigmaWords` reads the second component's encoding. -/
@[simp] theorem sigmaWords_natAdd {α : Type} {β : α → Type} {k l : ℕ}
    (fst : α ↪ (Fin k → ℕ)) (snd : ∀ a, β a ↪ (Fin l → ℕ)) (p : Σ a, β a) (j : Fin l) :
    sigmaWords fst snd p (Fin.natAdd k j) = snd p.1 p.2 j := by
  simp [sigmaWords, Fin.appendEquiv]

/-- Equal-width `addNat` normal-form companion of `sigmaWords_natAdd`. -/
@[simp] theorem sigmaWords_addNat {α : Type} {β : α → Type} {k : ℕ}
    (fst : α ↪ (Fin k → ℕ)) (snd : ∀ a, β a ↪ (Fin k → ℕ)) (p : Σ a, β a) (j : Fin k) :
    sigmaWords fst snd p (j.addNat k) = snd p.1 p.2 j := by
  rw [← Fin.natAdd_eq_addNat, sigmaWords_natAdd]

/-- Every word of `sigmaWords fst snd p` fits when both components' words fit. -/
theorem fits_sigmaWords {α : Type} {β : α → Type} {k l w : ℕ}
    (fst : α ↪ (Fin k → ℕ)) (snd : ∀ a, β a ↪ (Fin l → ℕ)) {p : Σ a, β a}
    (h₁ : ∀ i, Fits w (fst p.1 i)) (h₂ : ∀ j, Fits w (snd p.1 p.2 j)) :
    ∀ i, Fits w (sigmaWords fst snd p i) :=
  Fin.addCases (fun i => by simpa using h₁ i) (fun j => by simpa using h₂ j)

end Cslib.WordRAM.Realization

public meta section

namespace Cslib.WordRAM.Realization

open Lean Meta Elab Command Term Lean.Parser.Command

/-- Normalize the right-hand side of a generated `@[simp]` coordinate equation in the current
`simp` context so that nested `wordWords`, `blockWords` and `word_enc_structure` projections
reduce to direct field accesses and satisfy `simpNF`. -/
elab "word_enc_simp_rhs% " t:term : term => do
  let e ← Term.elabTermAndSynthesize t none
  let ctx ← Simp.mkContext (config := { dsimp := true, zeta := true, proj := true, iota := true })
    (simpTheorems := #[← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
  let (res, _) ← Simp.main e ctx
  return res.expr

/-- `word_enc_structure eS : S where f₁ : e₁, f₂ : e₂` declares the finite-register word encoding
`eS : S ↪ (Fin k → ℕ)` of a structure `S` as the concatenated words of its fields in declaration
order, together with `eSFields`, `eS_apply`, coordinate `@[simp]` equations `eS_coord_j` (when all
field widths reduce to numerals), field-slice equations `eS_<field>`, and `eS_fits`.

List every field of `S` once in declaration order, giving an explicit `Fᵢ ↪ (Fin kᵢ → ℕ)` (or
explicit `WordEncoding Fᵢ` value) for each field; no typeclass search chooses a default encoding.
A parent structure may be listed as `toParent` or flattened into its fields. A field whose type
depends on earlier fields may be written `f : w using hw`, encoding `f` as the single word `w f`
via `hw : Function.Injective w`. Explicit `(p : T)` parameters before `:` become explicit arguments
of every generated declaration; the optional `public` or `private` prefix defaults to `public`. -/
syntax (name := wordEncStructure) (docComment)? (visibility)? "word_enc_structure " ident
  (" (" ident " : " term ")")* " : " term " where "
  (ident " : " term:max (" using " term:max)?),+ : command

private def appIdent (base : Name) (suffix : String) : Ident :=
  mkIdent (base.appendAfter suffix)

/-- Left-associated tuple `(((t₀, t₁), t₂), …)` matching left-associated `appendWords`. -/
private def leftTuple (ts : Array Term) : MacroM Term := do
  let mut r := ts[0]!
  for t in ts.extract 1 ts.size do
    r ← `(($r, $t))
  return r

/-- Left-associated `appendWords (appendWords e₀ e₁) e₂ …`, or `e₀` for one slot. -/
private def leftTupleEncoding (es : Array Term) : MacroM Term := do
  let mut r := es[0]!
  for e in es.extract 1 es.size do
    r ← `(appendWords $r $e)
  return r

/-- Path of fields from structure `s` to field `n`, descending through parent subobjects. -/
private partial def fieldPath? (env : Environment) (s n : Name) : Option (Array Name) :=
  if (getStructureFields env s).contains n then some #[n] else
    (getStructureFields env s).findSome? fun p =>
      (isSubobjectField? env s p).bind fun parent =>
        (fieldPath? env parent n).map (#[p] ++ ·)

/-- Expected frontier of field paths of `s` given the listed paths. -/
private partial def fieldFrontier (env : Environment) (s : Name) (prefix_ : Array Name)
    (listed : Array (Array Name)) : Array (Array Name) :=
  (getStructureFields env s).flatMap fun f =>
    let p := prefix_.push f
    match isSubobjectField? env s f with
    | some parent =>
      if listed.any fun q => q.size > p.size && q.extract 0 p.size == p then
        fieldFrontier env parent p listed
      else #[p]
    | none => #[p]

/-- Structure projection constants along `path` starting from `s`. -/
private def pathProjs (env : Environment) (s : Name) (path : Array Name) : Array Name := Id.run do
  let mut cur := s
  let mut r := #[]
  for f in path do
    r := r.push (cur ++ f)
    if let some p := isSubobjectField? env cur f then cur := p
  return r

/-- Read the projections `projs` from `x`. -/
private def readPath (projs : Array Name) (x : Term) : MacroM Term :=
  projs.foldlM (fun t c => `($(mkCIdent c) $t)) x

/-- Apply `s`'s constructor (and flattened parent constructors) to `leaf p` at each path `p`. -/
private partial def nestCtor (env : Environment) (s : Name) (prefix_ : Array Name)
    (paths : Array (Array Name)) (leaf : Array Name → Term) : MacroM Term := do
  let args ← (getStructureFields env s).mapM fun f => do
    let p := prefix_.push f
    if paths.contains p then return leaf p
    match isSubobjectField? env s f with
    | some parent => `(($(← nestCtor env parent p paths leaf)))
    | none => Macro.throwError s!"word_enc_structure: no encoded path for field {p}"
  return Syntax.mkApp (mkCIdent (getStructureCtor env s).name) args

/-- Root component of every identifier in `stx`. -/
private partial def identRoots (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n.getRoot]
  | .node _ _ args => args.flatMap identRoots
  | _ => #[]

/-- Substitute `vals[i]` for `names[i]` (and dotted roots `names[i].f`) in `t`. -/
private def substIdents (names : Array Name) (vals : Array Term) (t : Term) : MacroM Term := do
  let r ← t.raw.replaceM fun stx => do
    if let .ident info _ n _ := stx then
      if let some i := names.idxOf? n then
        return some (← `(($(vals[i]!)))).raw
      if let some i := names.idxOf? n.getRoot then
        let mut r : Syntax := (← `(($(vals[i]!)))).raw
        for c in n.components.drop 1 do
          r := Syntax.node info ``Lean.Parser.Term.proj #[r, mkAtom ".", mkIdent c]
        return some r
    return none
  return ⟨r⟩

/-- Validate that `S` names a non-class structure and `fs` lists its fields once in order. -/
private def checkFields (S : Term) (fs : Array Ident) : CommandElabM (Name × Array (Array Name)) :=
  do
  let head ← match S with
    | `($id:ident) => pure id
    | `($id:ident $_args*) => pure id
    | _ => throwErrorAt S
        "word_enc_structure: expected a structure name, optionally applied to parameters"
  let s ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo head
  let env ← getEnv
  let sName := MessageData.ofConstName s
  unless isStructure env s do
    throwErrorAt S "word_enc_structure: `{sName}` is not a structure"
  if isClass env s then
    throwErrorAt S "word_enc_structure: `{sName}` is a class; only structures can be encoded"
  let found := fs.filterMap fun f => fieldPath? env s f.getId
  let expected := fieldFrontier env s #[] found
  let order := m!"the fields of `{sName}` in declaration order are \
    {MessageData.joinSep (expected.toList.map fun p => m!"`{p.back!}`") ", "}"
  let mut seen : Array (Array Name) := #[]
  for f in fs do
    let n := f.getId
    let some p := fieldPath? env s n |
      throwErrorAt f "word_enc_structure: `{n}` is not a field of `{sName}`; {order}"
    let some i := expected.idxOf? p | do
      let child := (found.find? fun q => q.size > p.size && q.extract 0 p.size == p).map (·.back!)
      throwErrorAt f "word_enc_structure: the parent field `{n}` and its field \
        `{child.getD n}` are both listed; list either the parent field or its fields; {order}"
    if seen.contains p then
      throwErrorAt f "word_enc_structure: field `{n}` is listed twice; {order}"
    if let some prev := seen.back? then
      if i < expected.idxOf prev then
        throwErrorAt f "word_enc_structure: field `{n}` must come before `{prev.back!}`; {order}"
    seen := seen.push p
  let missing := expected.filter (!seen.contains ·)
  unless missing.isEmpty do
    let names := MessageData.joinSep (missing.toList.map fun p => m!"`{p.back!}`") ", "
    throwErrorAt S "word_enc_structure: missing \
      {if missing.size = 1 then "field" else "fields"} {names} of `{sName}`; {order}"
  return (s, seen)

/-- Whether `e` is `x` or projections of `x`. -/
private partial def readsLocal (env : Environment) (x : Expr) (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ => e.consumeMData == x
  | .proj _ _ s => readsLocal env x s
  | e => match e.getAppFn with
    | .const c _ => match env.getProjectionFnInfo? c with
      | some info => e.getAppNumArgs == info.numParams + 1 && readsLocal env x e.appArg!
      | none => false
    | _ => false

private def occursOutsideReads (env : Environment) (x p : Expr) (e : Expr) : Bool :=
  (e.replace fun s => if readsLocal env x s then some x else none).containsFVar p.fvarId!

/-- Detect when `fieldsDecl` leaves an explicit parameter unused only because a dependent `using`
clause consumes it, mirroring `enc_structure`. -/
private def usingOnlyParams (fieldsDecl : Name) (ps : Array Ident) (S : Term)
    (depTerms : Term → MacroM (Array (Term × Term))) : CommandElabM Bool := liftTermElabM do
  let env ← getEnv
  let some ci ← withoutExporting do return (← getEnv).find? fieldsDecl | return false
  let some val := ci.value? | return false
  Meta.forallTelescope ci.type fun xs body => do
    if xs.size < ps.size then return false
    let params := xs.extract (xs.size - ps.size) xs.size
    for p in ps, v in params do
      unless (← v.fvarId!.getUserName) == p.getId do return false
    let value := val.beta xs
    let others (v : Expr) : MetaM Bool := xs.anyM fun w => do
      return w != v && (← w.fvarId!.getType).containsFVar v.fvarId!
    let unused ← params.filterM fun v => do
      return !value.containsFVar v.fvarId! && !body.containsFVar v.fvarId! && !(← others v)
    if unused.isEmpty then return false
    let st ← Term.saveState
    try
      Term.withoutErrToSorry do
        let sType ← Term.elabType S
        let xId := mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope `x)
        Meta.withLocalDeclD xId.getId sType fun x => do
          let mut found : Array Expr := #[]
          for (w, hw) in ← liftMacroM (depTerms xId) do
            let wE ← Term.elabTerm w none
            let hwE ← Term.elabTerm hw (← Term.elabType (← `(Function.Injective $w)))
            Term.synthesizeSyntheticMVarsNoPostponing
            found := found.push (← instantiateMVars wE) |>.push (← instantiateMVars hwE)
          return unused.all fun v => found.any (occursOutsideReads env x v ·)
    catch _ => pure false
    finally st.restore (restoreInfo := true)

/-- Information inspected on each field's explicit slot encoding. -/
private structure SlotInfo where
  /-- Elaborated slot term of type `Fᵢ ↪ (Fin wᵢ → ℕ)`. -/
  slotTerm : Term
  /-- Concrete numeral width when `wᵢ` reduces to a `Nat` literal. -/
  natWidth? : Option Nat
  /-- Whether `wᵢ = 1` and `(slotTerm v 0)` is definitionally `v`, so `Fits` takes `Fits w v`. -/
  scalarIdentity : Bool

private instance : Inhabited SlotInfo := ⟨⟨default, none, false⟩⟩

/-- Check that `slotStx` explicitly denotes `F ↪ (Fin k → ℕ)` (or an explicit `WordEncoding F`
value, projected to `.encode`), extract any concrete width numeral, and test scalar identity. -/
private def inspectSlots (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (S : Term) (rawSlots : Array Term) (isDep : Array Bool)
    (wordOfTerm : Nat → Term → MacroM Term) : CommandElabM (Array SlotInfo) :=
  runTermElabM fun _ => do
  let st ← Term.saveState
  try
    Term.elabBinders params fun _ => do
      let sType ← Term.elabType S
      let aId := mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope `a)
      Meta.withLocalDeclD aId.getId sType fun _ => do
        (Array.range rawSlots.size).mapM fun i => do
          if isDep[i]! then
            return { slotTerm := ← `(wordWords), natWidth? := some 1, scalarIdentity := true }
          let rawSlot : Term := rawSlots[i]!
          let valStx ← liftMacroM (wordOfTerm i aId)
          let valExpr ← Term.elabTermAndSynthesize valStx none
          let valTy ← inferType valExpr
          let eExpr ← Term.elabTermAndSynthesize rawSlot none
          let eTy ← instantiateMVars (← inferType eExpr)
          let (slotTerm, embExpr) ← if (← whnf eTy).isAppOfArity ``WordEncoding 1 then
              let proj ← `(WordEncoding.encode (self := $rawSlot))
              let pe ← Term.elabTermAndSynthesize proj none
              pure (proj, pe)
            else
              pure (rawSlot, eExpr)
          let embTy ← instantiateMVars (← inferType embExpr)
          let some (domTy, tgt) := (← whnf embTy).app2? ``Function.Embedding
            | throwErrorAt rawSlot
                "word_enc_structure: expected field encoding `F ↪ (Fin k → ℕ)`, \
                  got{indentExpr embTy}"
          unless ← isDefEq domTy valTy do
            throwErrorAt rawSlot "word_enc_structure: field has type{indentExpr valTy}\n\
              but encoding has domain{indentExpr domTy}"
          let .forallE _ finDom body _ ← whnf tgt
            | throwErrorAt rawSlot
                "word_enc_structure: expected codomain `Fin k → ℕ`, got{indentExpr tgt}"
          unless (← whnf body).isConstOf ``Nat do
            throwErrorAt rawSlot
                "word_enc_structure: expected codomain `Fin k → ℕ`, got{indentExpr tgt}"
          let some wExpr := (← whnf finDom).app1? ``Fin
            | throwErrorAt rawSlot
                "word_enc_structure: expected codomain `Fin k → ℕ`, got{indentExpr tgt}"
          let wExpr ← instantiateMVars wExpr
          let natWidth? ← match ← (evalNat wExpr).run with
            | some k => pure (some k)
            | none => (evalNat (← whnf wExpr)).run
          let scalarIdentity ← match natWidth? with
            | some 1 => do
              let zeroFin ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 1)) 0
              let applied := mkApp (← mkAppM ``DFunLike.coe #[embExpr, valExpr]) zeroFin
              withNewMCtxDepth (isDefEq applied valExpr)
            | _ => pure false
          return { slotTerm, natWidth?, scalarIdentity }
  finally st.restore (restoreInfo := false)

/-- Elaborate `word_enc_structure`: tuple abbreviation, structure embedding, `_apply`, `@[simp]`
coordinate equations, per-field slice equations and `_fits`. -/
@[command_elab wordEncStructure] def elabWordEncStructure : CommandElab := fun stx => do
  let `($[$doc:docComment]? $[$vis:visibility]? word_enc_structure $eS:ident
      $[($ps:ident : $pts:term)]* : $S:term where
      $[$fs:ident : $es:term $[using $hws:term]?],*) :=
    stx | throwUnsupportedSyntax
  let pts : Array Term := pts.map (⟨·⟩)
  let es : Array Term := es.map (⟨·⟩)
  let vis : TSyntax ``Lean.Parser.Command.visibility ← match vis with
    | some v => pure v
    | none => `(visibility| public)
  let (s, paths) ← checkFields S fs
  let env ← getEnv
  let name := eS.getId
  let n := fs.size
  let names := fs.map (·.getId)
  for i in [0:n] do
    if let some hw := hws[i]! then
      let roots := identRoots es[i]! ++ identRoots hw
      for p in ps do
        if names.extract 0 i |>.contains p.getId then
          if roots.contains p.getId then
            throwErrorAt p "word_enc_structure: parameter `{p.getId}` shares its name with an \
              earlier field read by `{names[i]!}`; rename the parameter"
  let projs := paths.map (pathProjs env s)
  let dependent := hws.any (·.isSome)
  let simple := !dependent && paths.all (·.size == 1)
  let params ← ps.zip pts |>.mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t))
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (fun p => (⟨p.raw⟩ : Term)))
  let eSTerm := applied eS
  let userNames := ps.map (·.getId) ++ identRoots S ++ pts.flatMap (identRoots ·) ++
    es.flatMap (identRoots ·) ++ hws.flatMap fun | some hw => identRoots hw | none => #[]
  let freshIdent (base : Name) : CommandElabM Ident := do
    return mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope base)
  let plainIdent (base : Name) : CommandElabM Ident :=
    if userNames.contains base then freshIdent base else pure (mkIdent base)
  let a ← plainIdent `a
  let wordFn (i : Nat) (vals : Array Term) : MacroM Term :=
    substIdents (names.extract 0 i) (vals.extract 0 i) es[i]!
  let word (i : Nat) (vals : Array Term) (x : Term) : MacroM Term := do
    if hws[i]!.isSome then `($(← wordFn i vals) $x) else pure x
  let wordOf (i : Nat) (x : Term) : MacroM Term := do
    let reads ← projs.mapM (readPath · x)
    word i reads reads[i]!
  let isDep := hws.map (·.isSome)
  let slotInfos ← inspectSlots params S es isDep wordOf
  let slots := slotInfos.map (·.slotTerm)
  let allConcrete : Option (Array Nat) := slotInfos.mapM (·.natWidth?)
  let fields := appIdent name "Fields"
  let fieldsOf ← liftMacroM do leftTuple (← (Array.range n).mapM fun i => wordOf i a)
  let encoding ← liftMacroM <| leftTupleEncoding slots
  let fieldsTerm := applied fields
  elabCommand (← `($vis:visibility abbrev $fields:ident $params* := $encoding))
  let fieldsDecl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fields
  addDocStringCore fieldsDecl s!"The tuple word encoding of the fields of `{name}`."
  if dependent then
    let depTerms (x : Term) : MacroM (Array (Term × Term)) := do
      let reads ← projs.mapM (readPath · x)
      (Array.range n).filterMapM fun i => do
        let some hw := hws[i]! | return none
        return some (← wordFn i reads, ← substIdents (names.extract 0 i) (reads.extract 0 i) hw)
    if ← usingOnlyParams fieldsDecl ps S depTerms then
      elabCommand (← `(attribute [nolint unusedArguments] $fields:ident))
  let inj : Term ← if simple then `(fun x y h => by cases x; cases y; simp_all) else do
    let ls ← (Array.range n).mapM fun i => freshIdent (Name.mkSimple s!"l{i}")
    let rs ← (Array.range n).mapM fun i => freshIdent (Name.mkSimple s!"r{i}")
    let h ← freshIdent `h
    let t ← freshIdent `t
    let leaf (xs : Array Ident) (p : Array Name) : Term := ⟨xs[paths.idxOf p]!.raw⟩
    let lhs ← liftMacroM <| nestCtor env s #[] paths (leaf ls)
    let rhs ← liftMacroM <| nestCtor env s #[] paths (leaf rs)
    let lTerms : Array Term := ls.map (⟨·.raw⟩)
    let mut tacs : Array (TSyntax `tactic) := #[]
    for i in [0:n] do
      let e ← freshIdent (Name.mkSimple s!"e{i}")
      let wl ← liftMacroM <| word i lTerms lTerms[i]!
      let wr ← liftMacroM <| word i lTerms ⟨rs[i]!.raw⟩
      let comp ← liftMacroM do
        let mut r : Term := t
        for _ in [0 : n - 1 - i] do r ← `(($r).1)
        if i > 0 then r ← `(($r).2)
        return r
      tacs := tacs.push (← `(tactic| have $e:ident : $wl = $wr := congrArg (fun $t => $comp) $h))
      if let some hw := hws[i]! then
        let hw ← liftMacroM <| substIdents (names.extract 0 i) (lTerms.extract 0 i) hw
        let w ← liftMacroM <| wordFn i lTerms
        tacs := tacs.push (← `(tactic| replace $e:ident := ($hw : Function.Injective $w) $e))
      tacs := tacs.push (← `(tactic| subst $(rs[i]!):ident))
    let mut tac ← `(tactic| rfl)
    for t' in tacs.reverse do
      tac ← `(tactic| ($t'; $tac))
    `(fun x y => match x, y with | $lhs, $rhs => fun $h => by $tac:tactic)
  -- Width expression of slot `i`: concrete numeral when known, else `WordEncoding`-free helper.
  let slotWidthTerm (i : Nat) : CommandElabM Term := do
    if let some m := slotInfos[i]!.natWidth? then
      return Syntax.mkNumLit (toString m)
    `((fun {α : Type} {l : ℕ} (_ : α ↪ (Fin l → ℕ)) => l) ($(slots[i]!)))
  let mut totalWidthTerm ← slotWidthTerm 0
  for i in [1:n] do
    let wi ← slotWidthTerm i
    totalWidthTerm ← `($totalWidthTerm + $wi)
  let codomainWidth : Term := match allConcrete with
    | some ms => Syntax.mkNumLit (toString (ms.foldl (· + ·) 0))
    | none => totalWidthTerm
  elabCommand (← `($[$doc:docComment]? @[expose]
    $vis:visibility def $eS:ident $params* : $S ↪ (Fin $codomainWidth → ℕ) :=
      (⟨fun $a => $fieldsOf, $inj⟩ : $S ↪ _).trans $fieldsTerm))
  let encRef : Term ← `(($eSTerm : $S ↪ (Fin $codomainWidth → ℕ)))
  let applyDecl := appIdent name "_apply"
  elabCommand (← `($vis:visibility theorem $applyDecl:ident $params* ($a : $S) :
    $encRef $a = $fieldsTerm $fieldsOf := rfl))
  -- Concrete `@[simp]` coordinate equations `eS_coord_j`
  if let some ms := allConcrete then
    let mut off := 0
    for i in [0:n] do
      let mi := ms[i]!
      let slot := slots[i]!
      let fieldVal ← liftMacroM (wordOf i a)
      let mLit : Term := Syntax.mkNumLit (toString mi)
      for r in [0:mi] do
        let j := off + r
        let jLit : Term := Syntax.mkNumLit (toString j)
        let rLit : Term := Syntax.mkNumLit (toString r)
        let coordName := appIdent name s!"_coord_{j}"
        elabCommand (← `(@[simp] $vis:visibility theorem $coordName:ident $params* ($a : $S) :
          $encRef $a $jLit = word_enc_simp_rhs% ($slot ($fieldVal) ($rLit : Fin $mLit)) := by
            first | rfl | (change $slot ($fieldVal) ($rLit : Fin $mLit) = _; simp)))
      off := off + mi
  -- Per-field slice projection equations `eS_<field>` (marked `@[simp]` when symbolic)
  let jIdx ← plainIdent `j
  for i in [0:n] do
    if slotInfos[i]!.natWidth? == some 0 then continue
    let wi ← slotWidthTerm i
    let slot := slots[i]!
    let fieldVal ← liftMacroM (wordOf i a)
    let mut idxTerm : Term := jIdx
    if i > 0 then
      let mut prefixW ← slotWidthTerm 0
      for p in [1:i] do
        let wp ← slotWidthTerm p
        prefixW ← `($prefixW + $wp)
      idxTerm ← `(Fin.natAdd $prefixW $idxTerm)
    for q in [i + 1 : n] do
      let wq ← slotWidthTerm q
      idxTerm ← `(Fin.castAdd $wq $idxTerm)
    let mut sliceProof : Term ←
      if i > 0 then `(appendWords_natAdd _ _ _ _) else `(rfl)
    for _ in [i + 1 : n] do
      sliceProof ← `((appendWords_castAdd _ _ _ _).trans $sliceProof)
    let sliceName := appIdent name s!"_{fs[i]!.getId}"
    if allConcrete.isSome then
      elabCommand (← `($vis:visibility theorem $sliceName:ident $params*
        ($a : $S) ($jIdx : Fin $wi) :
        $encRef $a $idxTerm = $slot ($fieldVal) $jIdx :=
          $sliceProof))
    else
      elabCommand (← `(@[simp] $vis:visibility theorem $sliceName:ident $params*
        ($a : $S) ($jIdx : Fin $wi) :
        $encRef $a $idxTerm = word_enc_simp_rhs% ($slot ($fieldVal) $jIdx) := by
          refine Eq.trans ($sliceProof) ?_
          first | rfl | simp))
  -- Compositional word-fit lemma `eS_fits` (zero `fin_cases`)
  let wId ← plainIdent `w
  let mut fitBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut fitProofs : Array Term := #[]
  for i in [0:n] do
    let slot := slots[i]!
    let fieldVal ← liftMacroM (wordOf i a)
    if slotInfos[i]!.natWidth? == some 0 then
      fitProofs := fitProofs.push (← `(fun j => j.elim0))
    else if slotInfos[i]!.scalarIdentity then
      let hi ← plainIdent (Name.mkSimple s!"h_{fs[i]!.getId}")
      fitBinders := fitBinders.push (← `(bracketedBinder| ($hi : Fits $wId ($fieldVal))))
      fitProofs := fitProofs.push (← `(Fin.cases $hi fun j => j.elim0))
    else
      let hi ← plainIdent (Name.mkSimple s!"h_{fs[i]!.getId}")
      fitBinders := fitBinders.push
        (← `(bracketedBinder| ($hi : ∀ j, Fits $wId ($slot ($fieldVal) j))))
      fitProofs := fitProofs.push hi
  let mut combinedFit : Term := fitProofs[0]!
  for i in [1:n] do
    let prevSlots ← liftMacroM <| leftTupleEncoding (slots.extract 0 i)
    let nextSlot := slots[i]!
    combinedFit ← `(fits_appendWords $prevSlots $nextSlot $combinedFit $(fitProofs[i]!))
  let fitsName := appIdent name "_fits"
  elabCommand (← `($vis:visibility theorem $fitsName:ident $params*
    {$wId : ℕ} {$a : $S} $fitBinders* : ∀ j, Fits $wId ($encRef $a j) := $combinedFit))

end Cslib.WordRAM.Realization
