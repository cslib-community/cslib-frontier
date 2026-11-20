/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveParser
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveChild
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.InductiveValidation
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.InductiveRecursiveAccess
public meta import Lean.Elab.Command

/-!
# Generating flat encodings of directly recursive inductive types

Implementation of the recursive branch of `enc_inductive`. Scalar payloads use the explicitly
supplied embeddings. Every constructor contributes exactly one framed token; recursive children
contribute their streams without further framing. Parameters select a family and its scalar
embeddings and are not serialized. Tags use the declaration order and right-nested `encSum`.
-/

public meta section
namespace Turing.MultiTapeTM.Internal
open Lean Elab Command Term Meta

private def suffix (name : Name) (s : String) : Ident := mkIdent (name.appendAfter s)

/-- Give internal binders a fresh scope while keeping declaration names and user parameters. -/
private def freshBinders : CommandElabM (Name → Ident) := do
  let scope ← liftMacroM <| withFreshMacroScope do getCurrMacroScope
  let moduleName ← getMainModule
  return fun name => mkIdent (addMacroScope moduleName name scope)

private def tuple (ts : Array Term) : MacroM Term := do
  if ts.isEmpty then return ← `(())
  let mut r := ts.back!
  for t in ts.pop.reverse do r ← `(($t, $r))
  return r

private def tupleEnc (es : Array Term) : MacroM Term := do
  if es.isEmpty then return ← `(encUnit)
  let mut r := es.back!
  for e in es.pop.reverse do r ← `(encPair $e $r)
  return r

private def inject (t : Term) (i n : Nat) : MacroM Term := do
  let mut r := t
  if i + 1 < n then r ← `(Sum.inl $r)
  for _ in [0:i] do r ← `(Sum.inr $r)
  return r

private def appendAll (ts : Array Term) : MacroM Term := do
  let mut r : Term ← `([])
  for t in ts.reverse do r ← `($t ++ $r)
  return r

private structure RecursiveSpec where
  eT : Ident
  ps : Array Ident
  params : TSyntaxArray ``Lean.Parser.Term.bracketedBinder
  type : Term
  constructors : Array Ident
  encodings : Array (Array Term)
  checked : RecursiveInductiveInfo
  payloadEncs : Array Term

private def elabRecursiveConstructors (spec : RecursiveSpec) : CommandElabM Unit := do
  let binder ← freshBinders
  let gamma := binder `γ
  let encoder := binder `encIn
  let eT := spec.eT
  let ps := spec.ps
  let params := spec.params
  let T := spec.type
  let cs := spec.constructors
  let encss := spec.encodings
  let checked := spec.checked
  let payloadEncs := spec.payloadEncs
  let root := checked.typeName
  let recs := checked.recursiveFields
  let n := cs.size
  let tokens := suffix eT.getId "_tokens"
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (⟨·.raw⟩))
  let ref (s : String) := applied (suffix eT.getId s)
  -- Constructor equations and native assembly: frame the scalar token once, then copy children.
  let mut rests : Array Term := #[payloadEncs.back!]
  for p in payloadEncs.pop.reverse do
    rests := #[← `(encSum $p $(rests[0]!))] ++ rests
  for i in [0:n] do
    let xs := (Array.range recs[i]!.size).map fun j => binder (Name.mkSimple s!"x{j}")
    let args : Array Term := xs.map (⟨·.raw⟩)
    let ctor := mkIdent (root ++ cs[i]!.getId)
    let value := Syntax.mkApp ctor args
    let scalarIndices := (Array.range xs.size).filter fun j => !(recs[i]!)[j]!
    let childIndices := (Array.range xs.size).filter fun j => (recs[i]!)[j]!
    let scalar := scalarIndices.map (args[·]!)
    let token ← liftMacroM <| inject (← liftMacroM <| tuple scalar) i n
    let tail ← liftMacroM <| appendAll
      (← childIndices.mapM fun j => `($(applied eT) $(args[j]!)))
    let mut bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    for j in [0:xs.size] do
      bs := bs.push (← `(bracketedBinder| ($(xs[j]!) : $((checked.fieldTypes[i]!)[j]!))))
    let equation := suffix eT.getId s!"_{cs[i]!.getId}_apply"
    elabCommand (← `(@[simp] public theorem $equation:ident $params* $bs* :
        $(applied eT) ($value : $T) = frame ($(ref "TokenEncoding") $token) ++ $tail := by
      simp [$(suffix eT.getId "_apply"):ident, $tokens:ident]))
    elabCommand (← `(public theorem $(suffix eT.getId s!"_{cs[i]!.getId}_length"):ident
        $params* $bs* : ($(applied eT) ($value : $T)).length =
          2 * ($(ref "TokenEncoding") $token).length + 1 + ($tail : List Bool).length := by
      rw [$equation:ident]
      simp only [List.length_append, length_frame]))
    let fn (j : Nat) := binder (Name.mkSimple s!"f{j}")
    let hn (j : Nat) := binder (Name.mkSimple s!"h{j}")
    let tn (j : Nat) := binder (Name.mkSimple s!"T{j}")
    let sn (j : Nat) := binder (Name.mkSimple s!"S{j}")
    let fieldEncs ← (Array.range xs.size).mapM fun j =>
      if (recs[i]!)[j]! then pure (applied eT) else pure (encss[i]!)[j]!
    let mut rb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    for j in [0:xs.size] do
      rb := rb.push (← `(bracketedBinder| {$(fn j) : $gamma → $((checked.fieldTypes[i]!)[j]!)}))
      rb := rb.push (← `(bracketedBinder| {$(tn j) $(sn j) : $gamma → ℕ}))
    for j in [0:xs.size] do
      rb := rb.push (← `(bracketedBinder| ($(hn j) :
        ComputableInO $(fn j) $encoder $(fieldEncs[j]!) $(tn j) $(sn j))))
    let mut htoken : Term ← `(ComputableInO.const ())
    if !scalarIndices.isEmpty then
      htoken := hn scalarIndices.back!
      for j in scalarIndices.pop.reverse do htoken ← `(ComputableInO.prod $(hn j) $htoken)
    if i + 1 < n then
      htoken ← `(ComputableInO.comp_linear
        (ComputableInO.inl $(payloadEncs[i]!) $(rests[i + 1]!)) $htoken)
    for j in (List.range i).reverse do
      htoken ← `(ComputableInO.comp_linear
        (ComputableInO.inr $(payloadEncs[j]!) $(rests[j + 1]!)) $htoken)
    htoken ← `(ComputableInO.comp_linear
      (ComputableInDegree.of_frame (f := fun token => frame ($(ref "TokenEncoding") token))
        (encIn := $(ref "TokenEncoding")) (encMid := encBits) (fun _ => rfl)).inO_one $htoken)
    let mut htail : Term ← `(ComputableInO.const ([] : List Bool) (encMid := encBits))
    for j in childIndices.reverse do
      htail ← `(ComputableInO.append $(hn j) $htail (encOut := encBits) (fun _ => rfl))
    let computedArgs ← (Array.range xs.size).mapM fun j => `($(fn j) a)
    let computed := Syntax.mkApp ctor computedArgs
    let mut sumT : Term ← `(2 * ($encoder a).length)
    let mut sumS : Term ← `(2 * ($encoder a).length)
    for j in [0:xs.size] do
      sumT ← `($sumT + $(tn j) a)
      sumS ← `($sumS + $(sn j) a)
    elabCommand (← `(@[scoped fun_prop] public theorem
        $(suffix eT.getId s!"_{cs[i]!.getId}_inO"):ident $params*
        {$gamma : Type} {$encoder : $gamma ↪ List Bool} $rb* :
        ComputableInO (fun a => ($computed : $T)) $encoder $(applied eT)
          (fun a => $sumT) (fun a => $sumS) := by
      exact (ComputableInO.append $htoken $htail (fun a => by
        simp only [$equation:ident, encBits_apply, Function.comp_apply] <;> rfl)).mono_le
        (fun a => by omega)
          (fun a => by omega)))
    let matcher := suffix eT.getId s!"_{cs[i]!.getId}_matches"
    let mut matchAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for j in [0:n] do
      let ys := (Array.range recs[j]!.size).map fun k => binder (Name.mkSimple s!"y{k}")
      let pat := Syntax.mkApp (mkIdent (root ++ cs[j]!.getId)) (ys.map (⟨·.raw⟩))
      let b : Term ← if i == j then `(true) else `(false)
      matchAlts := matchAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $b))
    elabCommand (← `(/-- Recognize this constructor on a typed value. -/
      @[expose, nolint defsWithUnderscore unusedArguments]
      public def $matcher:ident $params* (value : $T) : Bool :=
        match value with $matchAlts:matchAlt*))
    let fieldTypes := checked.fieldTypes[i]!
    let mut payloadTy : Term ← `(Unit)
    if !fieldTypes.isEmpty then
      payloadTy := fieldTypes.back!
      for ty in fieldTypes.pop.reverse do payloadTy ← `($ty × $payloadTy)
    for field in [0:xs.size + 1] do
      let projection := suffix eT.getId (if field == 0 then s!"_{cs[i]!.getId}_payload?"
        else s!"_{cs[i]!.getId}_field{field - 1}?")
      let outTy := if field == 0 then payloadTy else fieldTypes[field - 1]!
      let mut pas : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for j in [0:n] do
        let ys := (Array.range recs[j]!.size).map fun k => binder (Name.mkSimple s!"y{k}")
        let pat := Syntax.mkApp (mkIdent (root ++ cs[j]!.getId)) (ys.map (⟨·.raw⟩))
        let rhs ← if i == j then do
          let v ← if field == 0 then liftMacroM (tuple (ys.map (⟨·.raw⟩)))
            else pure (⟨ys[field - 1]!.raw⟩ : Term)
          `(some $v)
        else `(none)
        pas := pas.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs))
      elabCommand (← `(/-- Extract this constructor's fields, or return `none` on another case. -/
        @[expose, nolint defsWithUnderscore unusedArguments]
        public def $projection:ident $params* (value : $T) : Option $outTy :=
          match value with $pas:matchAlt*))
      elabCommand (← `(@[simp] public theorem $(suffix projection.getId "_isSome"):ident
          $params* (value : $T) : ($(applied projection) value).isSome =
            $(applied matcher) value := by cases value <;> rfl))
      if field == 0 then
        let mut reconstructArgs : Array Term := #[]
        let mut rest : Term ← `(payload)
        for j in [0:xs.size] do
          if j + 1 < xs.size then
            reconstructArgs := reconstructArgs.push (← `(($rest).1))
            rest ← `(($rest).2)
          else reconstructArgs := reconstructArgs.push rest
        let reconstructed := Syntax.mkApp ctor reconstructArgs
        let valueIff := suffix projection.getId "_eq_some_iff"
        elabCommand (← `(/-- The complete payload reconstructs exactly this constructor. -/
          public theorem $valueIff:ident $params* (value : $T) (payload : $payloadTy) :
              $(applied projection) value = some payload ↔ value = $reconstructed := by
            cases value <;> simp [$projection:ident, Prod.ext_iff]))
        elabCommand (← `(/-- This matcher recognizes the constructor's range. -/
          public theorem $(suffix matcher.getId "_iff"):ident $params* (value : $T) :
              $(applied matcher) value = true ↔ ∃ payload : $payloadTy,
                value = $reconstructed := by
            rw [← $(suffix projection.getId "_isSome"):ident]
            simp only [Option.isSome_iff_exists, $valueIff:ident]))
    let ofInO := mkIdent ``Turing.MultiTapeTM.ComputableInSpace.of_inO
    let inOName := suffix eT.getId s!"_{cs[i]!.getId}_inO"
    let inORef := applied inOName
    let mut sb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut unpack : TSyntaxArray `tactic := #[]
    for j in [0:xs.size] do
      sb := sb.push (← `(bracketedBinder| {$(fn j) : $gamma → $((checked.fieldTypes[i]!)[j]!)}))
      sb := sb.push (← `(bracketedBinder| {$(sn j) : $gamma → ℕ}))
    for j in [0:xs.size] do
      sb := sb.push (← `(bracketedBinder| ($(hn j) :
        ComputableInSpace $(fn j) $encoder $(fieldEncs[j]!) $(sn j))))
      unpack := unpack.push (← `(tactic| obtain ⟨$(tn j), $(hn j)⟩ := $(hn j).exists_inO))
    if unpack.isEmpty then unpack := #[← `(tactic| skip)]
    let hs : Array Term := (Array.range xs.size).map fun j => hn j
    elabCommand (← `(@[scoped fun_prop] public theorem
        $(suffix eT.getId s!"_{cs[i]!.getId}_inSpace"):ident $params*
        {$gamma : Type} {$encoder : $gamma ↪ List Bool} $sb* :
        ComputableInSpace (fun a => ($computed : $T)) $encoder $(applied eT)
          (fun a => $sumS) := by
      $unpack:tactic*
      have ho : ComputableInO (fun a : $gamma => ($computed : $T)) $encoder $(applied eT)
          (fun a => $sumT) (fun a => $sumS) := $inORef $hs*
      exact $ofInO ho))
    let mut pb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut clocks : TSyntaxArray `tactic := #[]
    let dn (j : Nat) := binder (Name.mkSimple s!"d{j}")
    let en (j : Nat) := binder (Name.mkSimple s!"e{j}")
    let mut proofs : Array Term := #[]
    for j in [0:xs.size] do
      pb := pb.push (← `(bracketedBinder| {$(fn j) : $gamma → $((checked.fieldTypes[i]!)[j]!)}))
    let mut polyBound : Term ← `((PolyBounded.const 2).mul PolyBounded.self)
    let mut sumClock : Term ← `(2 * ($encoder a).length)
    for j in [0:xs.size] do
      pb := pb.push (← `(bracketedBinder| ($(hn j) :
        ComputableInPolyTime $(fn j) $encoder $(fieldEncs[j]!))))
      clocks := clocks.push (← `(tactic|
        obtain ⟨$(dn j), $(en j), $(hn j)⟩ := $(hn j).exists_degree))
      proofs := proofs.push (← `($(hn j).inO))
      sumClock ← `($sumClock + (($encoder a).length + 1) ^ $(dn j))
      polyBound ← `(($polyBound).add
        ((PolyBounded.self.add (PolyBounded.const 1)).pow $(dn j)))
    if clocks.isEmpty then clocks := #[← `(tactic| skip)]
    elabCommand (← `(@[scoped fun_prop] public theorem
        $(suffix eT.getId s!"_{cs[i]!.getId}_polyTime"):ident $params*
        {$gamma : Type} {$encoder : $gamma ↪ List Bool} $pb* :
        ComputableInPolyTime (fun a => ($computed : $T)) $encoder $(applied eT) := by
      $clocks:tactic*
      have ho : ComputableInO (fun a : $gamma => ($computed : $T)) $encoder $(applied eT)
          (fun a => $sumClock) (fun a => $sumClock) := $inORef $proofs*
      exact ho.computableInPolyTime $polyBound $polyBound))

private def elabRecursiveChildren (spec : RecursiveSpec) (tokenTy : Term) : CommandElabM Unit := do
  let binder ← freshBinders
  let eT := spec.eT
  let ps := spec.ps
  let params := spec.params
  let T := spec.type
  let cs := spec.constructors
  let checked := spec.checked
  let recs := checked.recursiveFields
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (⟨·.raw⟩))
  let ref (s : String) := applied (suffix eT.getId s)
  let streamEnc : Term ← `(encList $(ref "TokenEncoding"))
  for i in [0:cs.size] do
    let xs := (Array.range recs[i]!.size).map fun j => binder (Name.mkSimple s!"x{j}")
    let args : Array Term := xs.map (⟨·.raw⟩)
    let ctor := mkIdent (checked.typeName ++ cs[i]!.getId)
    let value := Syntax.mkApp ctor args
    let childIndices := (Array.range xs.size).filter fun j => (recs[i]!)[j]!
    let scalarIndices := (Array.range xs.size).filter fun j => !(recs[i]!)[j]!
    let token ← liftMacroM <| inject (← liftMacroM <| tuple (scalarIndices.map (args[·]!)))
      i cs.size
    let mut children : Term ← `(([] : List (List $tokenTy)))
    for j in childIndices.reverse do children ← `($(ref "_tokens") $(args[j]!) :: $children)
    let mut bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    for j in [0:xs.size] do
      bs := bs.push (← `(bracketedBinder| ($(xs[j]!) : $((checked.fieldTypes[i]!)[j]!))))
    for j in childIndices, rpos in Array.range childIndices.size do
      let proof := suffix eT.getId s!"_{cs[i]!.getId}_field{j}?_stream"
      let projection := suffix eT.getId s!"_{cs[i]!.getId}_field{j}?"
      let matcher := suffix eT.getId s!"_{cs[i]!.getId}_matches"
      elabCommand (← `(private theorem $proof:ident $params* $bs* :
          RecursiveEncoding.child? $(ref "_arity") $(quote rpos) ($(ref "_tokens") ($value : $T)) =
            some ($(ref "_tokens") $(args[j]!)) := by
        simpa [$(suffix eT.getId "_tokens"):ident] using
          (RecursiveEncoding.child?_node (arity := $(ref "_arity")) $token $children
            (by simp [$(suffix eT.getId "_tokens_forest"):ident]) $(quote rpos) (by simp) [])))
      elabCommand (← `(/-- Extracting a recursive field has a native polynomial-time certificate.
        The machine scans constructor arities and copies the selected child stream. -/
        @[scoped fun_prop] public theorem $(suffix projection.getId "_polyTime"):ident $params* :
            ComputableInPolyTime $(applied projection) $(applied eT) (encOption $(applied eT)) := by
          have hc := (RecursiveEncoding.child?_polyTime
            (encToken := $(ref "TokenEncoding"))
            ($(ref "_arity_deg")).computableInPolyTime $(ref "_arity_le") $(quote rpos)).comp
              ($(ref "_tokens_deg")).computableInPolyTime
          have hd := ComputableInPolyTime.optionElimWithInput
            (body := fun _ stream => $(ref "_decodeTokens") stream) hc
            (ComputableInPolyTime.const none)
            (($(ref "_decodeTokens_polyTime")).comp
              (ComputableInPolyTime.snd $(applied eT) $streamEnc))
          exact (ComputableInPolyTime.ite $(applied (suffix matcher.getId "_polyTime"))
            hd (ComputableInPolyTime.const none)).of_enc_eq
              (fun value => by
                cases value <;> simp [$projection:ident, $matcher:ident, $proof:ident,
                  $(suffix eT.getId "_decodeTokens_tokens"):ident])))

private def elabRecursivePayloads (spec : RecursiveSpec) : CommandElabM Unit := do
  let eT := spec.eT
  let ps := spec.ps
  let params := spec.params
  let T := spec.type
  let cs := spec.constructors
  let recs := spec.checked.recursiveFields
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (⟨·.raw⟩))
  for i in [0:cs.size] do
    let matcher := suffix eT.getId s!"_{cs[i]!.getId}_matches"
    let payload := suffix eT.getId s!"_{cs[i]!.getId}_payload?"
    let fields := (Array.range recs[i]!.size).map fun j =>
      suffix eT.getId s!"_{cs[i]!.getId}_field{j}?"
    let fieldEncs := (Array.range fields.size).map fun j =>
      if (recs[i]!)[j]! then applied eT else (spec.encodings[i]!)[j]!
    let out ← liftMacroM <| tupleEnc fieldEncs
    let mut proof : Term ← `(ComputableInPolyTime.ite
      $(applied (suffix matcher.getId "_polyTime"))
      (ComputableInPolyTime.const (encOut := encOption encUnit) (some ()))
      (ComputableInPolyTime.const none))
    if !fields.isEmpty then
      proof := applied (suffix fields.back!.getId "_polyTime")
      for f in fields.pop.reverse do
        proof ← `(ComputableInPolyTime.optionPair
          $(applied (suffix f.getId "_polyTime")) $proof)
    elabCommand (← `(/-- Complete payload reconstruction is natively polynomial-time. -/
      @[scoped fun_prop] public theorem $(suffix payload.getId "_polyTime"):ident $params* :
          ComputableInPolyTime $(applied payload) $(applied eT) (encOption $out) :=
        ($proof).of_enc_eq (fun value : $T => by
          cases value <;> simp [$payload:ident, $matcher:ident, $[$fields:ident],*])))

/-- Generate the flat recursive representation after checking all constructors and fields.
Explicit parameters are section variables during checking and explicit binders in every output. -/
def elabRecursiveInductive (doc : Option (TSyntax ``Lean.Parser.Command.docComment))
    (eT : Ident) (ps : Array Ident) (pts : Array Term) (T : Term)
    (cs : Array Ident) (encss : Array (Array Term)) : CommandElabM Unit := do
  let binder ← freshBinders
  let params ← ps.zip pts |>.mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t))
  elabCommand (← `(section))
  try
    if !params.isEmpty then elabCommand (← `(variable $params*))
    let checked ← checkRecursiveInductive T cs encss
    let root := checked.typeName
    let recs := checked.recursiveFields
    let n := cs.size
    let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (⟨·.raw⟩))
    let ref (s : String) := applied (suffix eT.getId s)
    let scalarEncs := (Array.range n).map fun i =>
      (Array.range encss[i]!.size).filterMap fun j =>
        if (recs[i]!)[j]! then none else some (encss[i]!)[j]!
    let payloadEncs ← liftMacroM <| scalarEncs.mapM tupleEnc
    let mut tokenEnc : Term := payloadEncs.back!
    for p in payloadEncs.pop.reverse do tokenEnc ← `(encSum $p $tokenEnc)
    let tokenTy ← runTermElabM fun _ => do
      let e ← Term.elabTerm tokenEnc none
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← whnfR (← instantiateMVars (← inferType e))
      let some (domain, _) := ty.app2? ``Function.Embedding |
        throwError "enc_inductive: expected token embedding, got{indentExpr ty}"
      PrettyPrinter.delab domain
    let tokEnc := suffix eT.getId "TokenEncoding"
    elabCommand (← `(/-- Constructor tags and scalar fields, in declaration order.
      Scalar tuples frame every field except the last. Recursive fields are omitted. -/
      @[nolint unusedArguments] public abbrev $tokEnc:ident $params* := $tokenEnc))
    let streamEnc : Term ← `(encList $(ref "TokenEncoding"))
    let tokens := suffix eT.getId "_tokens"
    let readToken := suffix eT.getId "_readToken"
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut makeAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut tokenPatterns : Array Term := #[]
    let mut nodeAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut leafAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut arityAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for i in [0:n] do
      let xs := (Array.range recs[i]!.size).map fun j => binder (Name.mkSimple s!"x{j}")
      let args : Array Term := xs.map (⟨·.raw⟩)
      let ctor := mkIdent (root ++ cs[i]!.getId)
      let pat := Syntax.mkApp ctor args
      let scalar := (Array.range xs.size).filterMap fun j =>
        if (recs[i]!)[j]! then none else some args[j]!
      let children := (Array.range xs.size).filterMap fun j =>
        if (recs[i]!)[j]! then some args[j]! else none
      let token ← liftMacroM <| inject (← liftMacroM <| tuple scalar) i n
      let childStreams ← children.mapM fun c => `($(ref "_tokens") $c)
      let tail ← liftMacroM <| appendAll childStreams
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $token :: $tail))
      let mut nodes : Term ← `(1)
      let mut leaves : Term ← `(0)
      for c in children do nodes ← `($nodes + $(ref "_nodes") $c)
      for e in scalarEncs[i]!, x in scalar do leaves ← `($leaves + ($e $x).length)
      for c in children do leaves ← `($leaves + $(ref "_leafSize") $c)
      nodeAlts := nodeAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $nodes))
      leafAlts := leafAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $leaves))
      let sp := (Array.range scalar.size).map fun j => binder (Name.mkSimple s!"s{j}")
      let tokenPattern ← liftMacroM <| inject (← liftMacroM <| tuple (sp.map (⟨·.raw⟩))) i n
      let operands := binder (if children.isEmpty then `_operands else `operands)
      let mut ctorArgs : Array Term := #[]
      let mut rj := 0
      let mut sj := 0
      let k := children.size
      for isRec in recs[i]! do
        if isRec then
          let mut index : Term ← `((0 : Fin $(quote (k - rj))))
          for _ in [0:rj] do index ← `(Fin.succ $index)
          ctorArgs := ctorArgs.push (← `($operands $index))
          rj := rj + 1
        else
          ctorArgs := ctorArgs.push (⟨sp[sj]!.raw⟩)
          sj := sj + 1
      let make := Syntax.mkApp ctor ctorArgs
      tokenPatterns := tokenPatterns.push tokenPattern
      makeAlts := makeAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $tokenPattern =>
        fun ($operands : Fin $(quote k) → $T) => $make))
      arityAlts := arityAlts.push
        (← `(Lean.Parser.Term.matchAltExpr| | $tokenPattern => $(quote k)))
    elabCommand (← `(/-- Preorder constructor stream; children occur in recursive-field order. -/
      @[expose] public def $tokens:ident $params* : $T → List $tokenTy :=
        fun value => match value with $alts:matchAlt*))
    elabCommand (← `(/-- Number of constructor occurrences, including leaves. -/
      @[expose] public def $(suffix eT.getId "_nodes"):ident $params* : $T → ℕ :=
        fun value => match value with $nodeAlts:matchAlt*))
    elabCommand (← `(/-- Sum of the unframed scalar encoding lengths at all nodes. -/
      @[expose] public def $(suffix eT.getId "_leafSize"):ident $params* : $T → ℕ :=
        fun value => match value with $leafAlts:matchAlt*))
    let arity := suffix eT.getId "_arity"
    elabCommand (← `(/-- Recursive arity of a constructor token. -/
      @[expose, nolint unusedArguments] public def $arity:ident $params* : $tokenTy → ℕ :=
        fun token => match token with $arityAlts:matchAlt*))
    let makeNode := suffix eT.getId "_make"
    elabCommand (← `(/-- Reconstruct a node from its scalar token and recursive operands. -/
      @[expose, nolint unusedArguments] public def $makeNode:ident $params* :
          (token : $tokenTy) → (Fin ($(ref "_arity") token) → $T) → $T :=
        fun token => match token with $makeAlts:matchAlt*))
    elabCommand (← `(/-- Read a constructor token and its fixed number of operands. -/
      @[expose, nolint unusedArguments] public def $readToken:ident $params* :=
        RecursiveEncoding.readNode $(ref "_arity") $(ref "_make")))
    let mut arityProofs : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut boundProofs : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut lawProofs : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut raw : Term ← `(ComputableInDegree.of_eq
      (f := fun token : $tokenTy => $(ref "TokenEncoding") token)
      (encIn := $(ref "TokenEncoding")) (encMid := encBits) (fun _ => rfl))
    let mut bits : Array Term := #[]
    for _ in [0:n - 1] do
      bits := bits.push (← `((ComputableInDegree.headD
        (enc₁ := encBool) (enc := encBits) false).comp $raw))
      raw ← `((ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).comp $raw)
    let counts := recs.map fun fields => fields.foldl (fun k b => k + if b then 1 else 0) 0
    let maxArity := counts.foldl max 0
    let mut arityCert : Term ← `(ComputableInDegree.const
      (encIn := $(ref "TokenEncoding")) (encMid := encUnary) $(quote counts.back!))
    for i in (List.range (n - 1)).reverse do
      arityCert ← `((($(bits[i]!)).ite (($arityCert).restrict _)
        ((ComputableInDegree.const (encMid := encUnary) $(quote counts[i]!)).restrict _)).mono
          (d' := 1) (e' := 0))
    for pat in tokenPatterns, k in counts do
      arityProofs := arityProofs.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => by rfl))
      boundProofs := boundProofs.push
        (← `(Lean.Parser.Term.matchAltExpr| | $pat => by simp [$arity:ident]))
      lawProofs := lawProofs.push (← `(Lean.Parser.Term.matchAltExpr|
        | $pat => fun (children : Fin $(quote k) → $T) => by
        simp only [$tokens:ident, $makeNode:ident, $arity:ident, List.ofFn_succ,
          List.ofFn_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil] <;> rfl))
    elabCommand (← `(/-- Reading recursive arities uses only finitely many constructor tag bits. -/
      @[scoped fun_prop] public theorem $(suffix eT.getId "_arity_deg"):ident $params* :
          ComputableInDegree $(ref "_arity") $(ref "TokenEncoding") encUnary 1 0 :=
        ($arityCert).of_enc_eq (fun token => match token with $arityProofs:matchAlt*)))
    elabCommand (← `(/-- Constructor arities are bounded independently of scalar fields. -/
      public theorem $(suffix eT.getId "_arity_le"):ident $params* (token : $tokenTy) :
          $(ref "_arity") token ≤ $(quote maxArity) :=
        match token with $boundProofs:matchAlt*))
    elabCommand (← `(/-- Node reconstruction writes its token followed by its children's streams. -/
      public theorem $(suffix eT.getId "_tokens_make"):ident $params* :
          ∀ (token : $tokenTy) (children : Fin ($(ref "_arity") token) → $T),
            $(ref "_tokens") ($(ref "_make") token children) =
              token :: (List.ofFn children).flatMap $(ref "_tokens") :=
        fun token => match token with $lawProofs:matchAlt*))
    elabCommand (← `(/-- Prefix decoding preserves the entire following stream. -/
      public theorem $(suffix eT.getId "_parseFuel_tokens"):ident $params*
          (value : $T) (rest : List $tokenTy) (fuel : ℕ)
          (hf : ($(ref "_tokens") value).length ≤ fuel) :
          Cslib.PrefixParser.parseFuel $(ref "_readToken") fuel
            ($(ref "_tokens") value ++ rest) = some (value, rest) := by
        induction value generalizing rest fuel <;> cases fuel <;>
          simp_all only [$tokens:ident, List.length_cons, List.length_append,
            List.length_nil, Nat.add_zero, Nat.not_succ_le_zero, List.cons_append,
            List.append_nil, List.append_assoc, Cslib.PrefixParser.parseFuel, $readToken:ident,
            RecursiveEncoding.readNode,
            $arity:ident, $makeNode:ident,
            Cslib.PrefixParser.parseOperands, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Fin.cases_zero, Fin.cases_succ]
        all_goals simp (disch := omega) [*, $tokens:ident, List.append_assoc,
          Cslib.PrefixParser.parseOperands, Option.bind_eq_bind, Option.pure_def,
          Fin.cases, Fin.induction, Fin.induction.go] <;> omega))
    let roundtrip := ref "_parseFuel_tokens"
    elabCommand (← `($[$doc:docComment]? @[expose] public def $eT:ident $params* : $T ↪ List Bool :=
      (⟨$(ref "_tokens"), fun x y h => by
        have hp := Cslib.PrefixParser.append_injective $roundtrip
          (rest := []) (rest' := []) (by simpa only [List.append_nil] using h)
        exact hp.1⟩ : $T ↪ List $tokenTy).trans $streamEnc))
    elabCommand (← `(public theorem $(suffix eT.getId "_apply"):ident $params*
        (value : $T) : $(applied eT) value = $streamEnc ($(ref "_tokens") value) := rfl))
    elabCommand (← `(@[scoped fun_prop] public theorem $(suffix eT.getId "_tokens_deg"):ident
        $params* : ComputableInDegree $(ref "_tokens") $(applied eT) $streamEnc 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
    elabCommand (← `(/-- Exact size: every token is framed once, independently of depth. -/
      public theorem $(suffix eT.getId "_length"):ident $params* (value : $T) :
          ($(applied eT) value).length =
            (($(ref "_tokens") value).map fun token =>
              2 * ($(ref "TokenEncoding") token).length + 1).sum :=
        length_encList _ _))
    elabCommand (← `(/-- Number of stream tokens equals the number of constructors. -/
      @[simp] public theorem $(suffix eT.getId "_tokens_length"):ident $params* (value : $T) :
          ($(ref "_tokens") value).length = $(ref "_nodes") value := by
        induction value <;>
          simp_all [$tokens:ident, $(suffix eT.getId "_nodes"):ident] <;> omega))
    let maxScalars := scalarEncs.foldl (fun m es => max m es.size) 0
    let factor := 4
    let overhead := 2 * (n + maxScalars) + 1
    elabCommand (← `(/-- Linear bit size in constructor count plus scalar word lengths. -/
      public theorem $(suffix eT.getId "_length_le"):ident $params*
          (value : $T) :
          ($(applied eT) value).length ≤ $(quote overhead) * $(ref "_nodes") value +
            $(quote factor) * $(ref "_leafSize") value := by
        induction value <;>
          simp_all [$(suffix eT.getId "_apply"):ident, $tokens:ident,
            $(suffix eT.getId "_nodes"):ident, $(suffix eT.getId "_leafSize"):ident,
            $tokEnc:ident, length_encList, List.map_append, List.sum_append,
            Nat.mul_add, Nat.add_mul] <;> omega))
    elabCommand (← `(/-- Parse exactly one tree from typed tokens; reject trailing tokens. -/
      @[expose] public def $(suffix eT.getId "_decodeTokens"):ident $params* :=
        Cslib.PrefixParser.decode $(ref "_readToken")))
    elabCommand (← `(@[simp] public theorem $(suffix eT.getId "_decodeTokens_tokens"):ident
        $params* (value : $T) : $(ref "_decodeTokens") ($(ref "_tokens") value) = some value :=
      Cslib.PrefixParser.decode_tokens $roundtrip value))
    elabCommand (← `(/-- Native decoding of typed token streams; no scalar decoder is assumed. -/
      @[scoped fun_prop] public theorem $(suffix eT.getId "_decodeTokens_polyTime"):ident
          $params* : ComputableInPolyTime $(ref "_decodeTokens") $streamEnc
            (encOption $(applied eT)) :=
        RecursiveEncoding.decode_readNode_polyTime $(ref "_arity") $(ref "_make")
          $(ref "_tokens") $(ref "_tokens_make") $(ref "_apply")
          ($(ref "_arity_deg")).computableInPolyTime $(ref "_arity_le")))
    elabCommand (← `(/-- Serialized values are exactly complete one-root constructor streams. -/
      public theorem $(suffix eT.getId "_tokens_forest"):ident $params* (value : $T) :
          RecursiveEncoding.Forest $(ref "_arity") 1 ($(ref "_tokens") value) := by
        have h := $(ref "_parseFuel_tokens") value []
          ($(ref "_tokens") value).length le_rfl
        simp only [List.append_nil] at h
        exact (RecursiveEncoding.parseFuel_readNode_sound $(ref "_arity") $(ref "_make")
          $(ref "_tokens") $(ref "_tokens_make") _ _ _ _ h).2))
    elabCommand (← `(/-- Reencoding a decoded value recovers every input token; all other
      complete-word parses fail. -/
      public theorem $(suffix eT.getId "_decodeTokens_map"):ident $params*
          (stream : List $tokenTy) :
          ($(ref "_decodeTokens") stream).map $(ref "_tokens") =
            if RecursiveEncoding.isTree $(ref "_arity") stream then some stream else none :=
        RecursiveEncoding.decode_readNode_tokens $(ref "_arity") $(ref "_make")
          $(ref "_tokens") $(ref "_tokens_make") stream))
    let mut db : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut payloadDecoders : Array Term := #[]
    for i in [0:n] do
      let mut ds : Array Term := #[]
      for j in [0:recs[i]!.size] do
        unless (recs[i]!)[j]! do
          let d := binder (Name.mkSimple s!"decode{i}_{j}")
          db := db.push (← `(bracketedBinder| ($d : PartialDecoder $((encss[i]!)[j]!))))
          ds := ds.push (⟨d.raw⟩)
      let mut payloadD : Term ← `(PartialDecoder.unit)
      if !ds.isEmpty then
        payloadD := ds.back!
        for d in ds.pop.reverse do payloadD ← `(PartialDecoder.pair $d $payloadD)
      payloadDecoders := payloadDecoders.push payloadD
    let mut tokenD := payloadDecoders.back!
    for d in payloadDecoders.pop.reverse do tokenD ← `(PartialDecoder.sum $d $tokenD)
    elabCommand (← `(/-- Strict bit-word decoder, conditional on explicitly supplied native
      partial decoders for every scalar field. Empty scalar types are supported. -/
      @[expose] public def $(suffix eT.getId "_decoder"):ident $params* $db* :
          PartialDecoder $(applied eT) :=
        PartialDecoder.checked
          (fun word => ((PartialDecoder.list $tokenD).decode word).bind $(ref "_decodeTokens"))
          (fun value => by
            rw [$(suffix eT.getId "_apply"):ident, PartialDecoder.decode_enc, Option.bind_some,
              $(suffix eT.getId "_decodeTokens_tokens"):ident])
          (by
            have h := ComputableInPolyTime.optionElimWithInput
              (body := fun _ stream => $(ref "_decodeTokens") stream)
              (PartialDecoder.list $tokenD).computable (ComputableInPolyTime.const none)
              (($(ref "_decodeTokens_polyTime")).comp
                (ComputableInPolyTime.snd encBits $streamEnc))
            exact h.of_enc_eq (fun word => by
              cases (PartialDecoder.list $tokenD).decode word <;> rfl))))
    let spec : RecursiveSpec := {
      eT, ps, params, type := T, constructors := cs, encodings := encss, checked, payloadEncs }
    elabRecursiveConstructors spec
    elabRecursiveAccess eT ps params T cs encss recs
    elabRecursiveChildren spec tokenTy
    elabRecursivePayloads spec
  finally
    elabCommand (← `(end))

end Turing.MultiTapeTM.Internal
