/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project visualization tooling)
import Lean

/-!
# Declaration census for `tools/viz/lean_census.py`

Run as `lake env lean --run tools/viz/LeanDecls.lean <lib-dir>`, with one module name per line on
standard input. Prints one JSON object: for each module that has build outputs under `<lib-dir>`,
the number of its declarations of each kind and the library modules whose constants its
declarations mention; and the modules that have no build outputs.

It reads the built `.olean` files (all three parts of a split module) without importing them, as
`scripts/ParallelDefs.lean` does, so it counts what elaboration produced rather than what the
source text looks like: declarations made by commands and macros (`enc_structure`, `deriving`,
`to_additive`-style generators) are counted, and new surface syntax needs no change here.

A declaration is *written* unless Lean generates it: recursors, `casesOn`, `noConfusion`,
equation and injectivity lemmas, structure projections, auxiliary `match_`/`proof_` constants
and names with macro scopes are *generated* and counted only in total. Written declarations are
classified by what they are: `theorem`, `def`, `abbrev` (a definition with abbreviation
reducibility hints), `instance`, `structure`, `class`, `inductive`, `opaque`, `axiom` and
`syntax` (the parser a `notation`, `syntax` or `macro` command declares) and `meta` (a
definition whose type is a metaprogramming type: tactics, elaborators and extensions).
-/

open Lean

namespace LeanDecls

def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
    "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "mk", "sizeOf_spec",
    "proxyType", "proxyTypeEquiv", "eq_def", "eq_unfold", "injEq", "inj", "induct",
    "induct_unfolding", "mutual_induct", "fun_cases", "fun_cases_unfolding", "congr_simp"]

/-- Whether a name, without its private prefix, is one Lean generates. -/
def isGenerated (n : Name) : Bool :=
  let n := privateToUserName n
  n.isInternalDetail || n.hasMacroScopes ||
    n.components.any (fun c => match c with
      | .str _ s => s.startsWith "match_" || s == "splitter"
      | _ => false) ||
    match n with
    | .str _ s => generatedSuffixes.contains s || s.startsWith "eq_" && (s.drop 3).all Char.isDigit
    | _ => false

/-- What a module's extension entries say about its declarations. -/
structure Tags where
  instances : NameSet := {}
  projections : NameSet := {}
  structures : NameSet := {}
  classes : NameSet := {}
  /-- Constructors of the module's inductive types; Lean generates constants under their names. -/
  ctors : NameSet := {}

unsafe def tags (entries : Array (Name × Array EnvExtensionEntry)) : Tags := Id.run do
  let mut t : Tags := {}
  for (ext, es) in entries do
    -- Some extensions are registered under private names.
    let ext := privateToUserName ext
    if ext == `Lean.projectionFnInfoExt then
      for e in es do
        t := { t with projections := t.projections.insert (unsafeCast e : Name × ProjectionFunctionInfo).1 }
    else if ext == `Lean.Meta.instanceExtension then
      for e in es do
        let entry := match (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry) with
          | .global a => a
          | .scoped _ a => a
        if let some n := entry.globalName? then
          t := { t with instances := t.instances.insert n }
    else if ext == `Lean.structureExt then
      for e in es do
        t := { t with structures := t.structures.insert (unsafeCast e : StructureInfo).structName }
    else if ext == `Lean.classExtension then
      for e in es do
        t := { t with classes := t.classes.insert (unsafeCast e : ClassEntry).name }
  return t

/-- Whether a definition declares syntax (a `notation`, `syntax` or `macro` parser). -/
def isSyntax (c : ConstantInfo) : Bool :=
  c.type.isConstOf ``Lean.ParserDescr || c.type.isConstOf ``Lean.TrailingParserDescr

/-- Namespaces of the metaprogramming types: a definition whose type mentions one is a tactic,
elaborator, delaborator or extension, run by attributes rather than referred to. -/
def metaRoots : List Name :=
  [`Lean.Elab, `Lean.Meta, `Lean.MetaM, `Lean.PrettyPrinter, `Lean.Parser, `Lean.Syntax,
    `Lean.TSyntax, `Lean.Macro, `Lean.MacroM, `Lean.Expr, `Lean.Name, `Lean.Json,
    `Mathlib.Meta, `Mathlib.Tactic, `Aesop, `Qq]

def isMeta (c : ConstantInfo) : Bool :=
  c.type.getUsedConstants.any fun n => metaRoots.any (·.isPrefixOf n)

def kind (t : Tags) (c : ConstantInfo) : Option String :=
  if isGenerated c.name || t.projections.contains c.name || t.ctors.contains c.name.getPrefix then
    none else
  match c with
  | .thmInfo _ => some "theorem"
  | .defnInfo d =>
    if isSyntax c then some "syntax"
    else if isMeta c then some "meta"
    else if t.instances.contains c.name then some "instance"
    else if d.hints matches .abbrev then some "abbrev"
    else some "def"
  | .inductInfo _ =>
    if t.classes.contains c.name then some "class"
    else if t.structures.contains c.name then some "structure"
    else some "inductive"
  | .opaqueInfo _ => some (if t.instances.contains c.name then "instance" else "opaque")
  | .axiomInfo _ => some "axiom"
  | _ => none

/-- The module part holding all of a module's declarations, and every mapped region. -/
unsafe def readModule (libDir : System.FilePath) (mod : String) :
    IO (Option (ModuleData × Array CompactedRegion)) := do
  let base := (libDir / System.FilePath.mk (mod.replace "." "/")).addExtension "olean"
  unless ← base.pathExists do return none
  let split ← (base.addExtension "private").pathExists
  let paths := if split then #[base, base.addExtension "server", base.addExtension "private"]
    else #[base]
  let parts ← readModuleDataParts paths
  let some (data, _) := parts[if split then 2 else 0]? |
    throw <| IO.userError s!"cannot read {base}"
  return some (data, parts.map (·.2))

/-- One constant of the library, as the census graph sees it. -/
structure Node where
  name : Name
  module : Nat
  kind : Option String
  /-- Library constants its type and value mention, by index; deduplicated. -/
  refs : Array Nat
  usesSorry : Bool
  deriving Inhabited

/-- Direct module imports, without implicit `Init` or duplicate phase entries. -/
def directImports (d : ModuleData) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  for imp in d.imports do
    let m := imp.module
    if m != `Init && !seen.contains m then
      seen := seen.insert m
      out := out.push m
  return out

def jsonDecl (mods : Array String) (n : Node) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("name", toJson (privateToUserName n.name).toString),
    ("module", toJson mods[n.module]!), ("kind", toJson n.kind)] ++ extra)

unsafe def main (args : List String) : IO UInt32 := do
  let [libDir] := args | do
    IO.eprintln "usage: lake env lean --run tools/viz/LeanDecls.lean <lib-dir> < requests"
    return 2
  let t0 ← IO.monoMsNow
  let stdin ← IO.getStdin
  let mut mods : Array String := #[]
  let mut headlines : Array (String × Array Name) := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | "headline" :: id :: names => headlines := headlines.push (id, names.toArray.map (·.toName))
    | [m] => mods := mods.push m
    | _ => throw <| IO.userError s!"cannot parse the request {line.trimAscii}"
  let mut datas : Array (String × ModuleData) := #[]
  let mut regions : Array CompactedRegion := #[]
  let mut missing : Array Json := #[]
  let mut index : Std.HashMap Name Nat := {}
  let mut constCount := 0
  for m in mods do
    match ← readModule libDir m with
    | none => missing := missing.push (toJson m)
    | some (data, rs) =>
      regions := regions ++ rs
      datas := datas.push (m, data)
      -- Node `i` is the `i`-th constant read. Two modules that never meet in one environment may
      -- declare the same name; references to it resolve to the first.
      for n in data.constNames do
        index := index.insertIfNew n constCount
        constCount := constCount + 1
  let modNames := datas.map (·.1)
  IO.eprintln s!"census: read library {(← IO.monoMsNow) - t0} ms"
  -- Every module the library imports, directly or not: the dependencies' modules are read for
  -- their constant names and imports only, so a use can be traced to the module defining it.
  initSearchPath (← findSysroot)
  let mut allMods : Array Name := modNames.map (·.toName)
  let mut modIdx : Std.HashMap Name Nat := {}
  for h : i in [:allMods.size] do modIdx := modIdx.insert allMods[i] i
  let mut modImports : Array (Array Nat) := #[]
  let mut queue : Array Name := #[]
  let mut pendingImports : Array (Array Name) := datas.map fun (_, d) => directImports d
  for imps in pendingImports do
    for i in imps do unless modIdx.contains i do queue := queue.push i
  let mut extOwner : Std.HashMap Name Nat := {}
  repeat
    let some mod := queue.back? | break
    queue := queue.pop
    if modIdx.contains mod then continue
    let mi := allMods.size
    allMods := allMods.push mod
    modIdx := modIdx.insert mod mi
    let (data, region) ← readModuleData (← findOLean mod)
    regions := regions.push region
    for n in data.constNames do extOwner := extOwner.insert n mi
    let imps := directImports data
    pendingImports := pendingImports.push imps
    for i in imps do unless modIdx.contains i do queue := queue.push i
  modImports := pendingImports.map (·.filterMap (modIdx[·]?))
  IO.eprintln s!"census: read dependencies {(← IO.monoMsNow) - t0} ms"
  let mut modUsed : Array (Std.HashSet Nat) := Array.replicate datas.size {}
  let mut nodes : Array Node := #[]
  let mut out : Array (String × Json) := #[]
  for h : mi in [:datas.size] do
    let (m, data) := datas[mi]
    let t := { tags data.entries with
      ctors := data.constants.foldl (init := {}) fun s c =>
        if c matches .ctorInfo _ then s.insert c.name else s }
    let mut counts : Std.HashMap String Nat := {}
    let mut generated := 0
    for c in data.constants do
      let k := kind t c
      match k with
      | some k => counts := counts.insert k (counts.getD k 0 + 1)
      | none => generated := generated + 1
      let mut used := c.type.getUsedConstants
      if let some v := c.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
      let mut refs : Std.HashSet Nat := {}
      let mut usesSorry := false
      for n in used do
        if n == ``sorryAx then usesSorry := true
        if let some i := index[n]? then
          refs := refs.insert i
        else if let some o := extOwner[n]? then
          modUsed := modUsed.modify mi (·.insert o)
      nodes := nodes.push { name := c.name, module := mi, kind := k, refs := refs.toArray, usesSorry }
    let kinds := Json.mkObj (counts.toList.map fun (k, n) => (k, toJson n))
    out := out.push (m, Json.mkObj [("kinds", kinds), ("generated", toJson generated)])
  IO.eprintln s!"census: constant graph {(← IO.monoMsNow) - t0} ms"
  -- Module-level uses, from the constant graph.
  let mut modUses : Array (Std.HashSet Nat) := Array.replicate datas.size {}
  for n in nodes do
    for r in n.refs do
      let o := nodes[r]!.module
      if o != n.module then
        modUses := modUses.modify n.module (·.insert o)
        modUsed := modUsed.modify n.module (·.insert o)
  out := out.mapIdx fun i (m, j) =>
    (m, j.setObjVal! "uses" (toJson ((modUses[i]!.toArray.map (modNames[·]!)).qsort (· < ·))))
  IO.eprintln s!"census: module uses {(← IO.monoMsNow) - t0} ms"
  -- How many distinct written declarations mention each one. A constant Lean generated (an
  -- auxiliary proof, a matcher, an equation lemma) speaks for the declaration that owns it: the
  -- nearest written declaration whose name prefixes its own.
  let ownerOf : Array Nat := Id.run do
    let mut out := Array.range nodes.size
    for h : i in [:nodes.size] do
      if nodes[i].kind.isNone then
        let mut p := nodes[i].name.getPrefix
        while !p.isAnonymous do
          if let some j := index[p]? then
            if nodes[j]!.kind.isSome then
              out := out.set! i j
              break
          p := p.getPrefix
    return out
  let mut members : Array (Array Nat) := Array.replicate nodes.size #[]
  for h : i in [:nodes.size] do members := members.modify ownerOf[i]! (·.push i)
  let mut refCount : Array Nat := Array.replicate nodes.size 0
  for h : o in [:nodes.size] do
    if ownerOf[o]! != o then continue
    let mut targets : Std.HashSet Nat := {}
    for i in members[o]! do
      for r in nodes[i]!.refs do
        let t := ownerOf[r]!
        if t != o then targets := targets.insert t
    for t in targets do refCount := refCount.modify t (· + 1)
  IO.eprintln s!"census: ref counts {(← IO.monoMsNow) - t0} ms"
  let isDefLike (n : Node) := match n.kind with
    | some "def" | some "abbrev" | some "structure" | some "inductive" | some "class"
    | some "opaque" => true
    | _ => false
  let mut unused : Array Json := #[]
  for h : i in [:nodes.size] do
    let n := nodes[i]
    if isDefLike n && refCount[i]! == 0 then unused := unused.push (jsonDecl modNames n)
  -- The 400 most mentioned written declarations. Most counts are equal, which sends `qsort`
  -- quadratic, so first find the count threshold from a histogram and sort only what clears it.
  let mut histogram : Std.HashMap Nat Nat := {}
  for h : i in [:nodes.size] do
    let c := refCount[i]!
    if nodes[i].kind.isSome && c > 0 then
      histogram := histogram.insert c (histogram.getD c 0 + 1)
  let mut threshold := 0
  let mut seenCount := 0
  for (c, k) in histogram.toArray.qsort (fun a b => a.1 > b.1) do
    seenCount := seenCount + k
    threshold := c
    if seenCount ≥ 400 then break
  let ranked := (Array.range nodes.size).filter
      (fun i => nodes[i]!.kind.isSome && refCount[i]! ≥ threshold && threshold > 0)
    |>.qsort (fun a b => refCount[a]! > refCount[b]! || (refCount[a]! == refCount[b]! && a < b))
  let top := (ranked.extract 0 400).map fun i =>
    jsonDecl modNames nodes[i]! [("refs", toJson refCount[i]!)]
  IO.eprintln s!"census: unused and top {(← IO.monoMsNow) - t0} ms"
  -- The library constants each registered result rests on.
  let mut cones : Array (String × Json) := #[]
  for (id, names) in headlines do
    let roots := names.filterMap (index[·]?)
    let mut seen : Std.HashSet Nat := {}
    let mut stack := roots
    let mut written := 0
    let mut usesSorry := false
    let mut perModule : Std.HashMap Nat Nat := {}
    while !stack.isEmpty do
      let i := stack.back!
      stack := stack.pop
      if seen.contains i then continue
      seen := seen.insert i
      let n := nodes[i]!
      if n.kind.isSome then
        written := written + 1
        perModule := perModule.insert n.module (perModule.getD n.module 0 + 1)
      if n.usesSorry then usesSorry := true
      for r in n.refs do
        unless seen.contains r do stack := stack.push r
    cones := cones.push (id, Json.mkObj [
      ("found", toJson roots.size), ("requested", toJson names.size),
      ("theorems", Json.arr (roots.map fun i => Json.mkObj [
        ("name", toJson (privateToUserName nodes[i]!.name).toString),
        ("module", toJson modNames[nodes[i]!.module]!)])),
      ("constants", toJson seen.size), ("declarations", toJson written), ("sorry", toJson usesSorry),
      ("modules", Json.mkObj (perModule.toList.map fun (mi, c) => (modNames[mi]!, toJson c)))])
  IO.eprintln s!"census: cones {(← IO.monoMsNow) - t0} ms"
  IO.println (Json.mkObj [("modules", Json.mkObj out.toList), ("missing", Json.arr missing),
    ("unused", Json.arr unused), ("top", Json.arr top),
    ("cones", Json.mkObj cones.toList),
    ("moduleGraph", Json.mkObj [
      ("names", toJson (allMods.map (·.toString))),
      ("imports", toJson modImports),
      ("used", toJson (modUsed.map (·.toArray.qsort (· < ·))))])]).compress
  -- Keep the mapped regions alive until the constants are no longer needed.
  let _ := regions
  return 0

end LeanDecls

unsafe def main (args : List String) : IO UInt32 := LeanDecls.main args
