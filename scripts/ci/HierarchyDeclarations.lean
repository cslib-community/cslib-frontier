-- Temporary hosted instrumentation for #4073. DO NOT MERGE.
import Lean
open Lean

unsafe def main (args : List String) : IO Unit := do
  let stdout ← IO.getStdout
  let mut regions : Array CompactedRegion := #[]
  for mod in args do
    let base := System.FilePath.mk ".lake/build/lib/lean" /
      System.FilePath.mk (mod.replace "." "/")
    let parts ← readModuleDataParts #[(base.addExtension "olean")]
    let some (data, region) := parts[0]? | throw <| IO.userError s!"missing {mod}"
    regions := regions.push region
    for c in data.constants do
      unless c.name.isInternalDetail do
        let kind := match c with
          | .defnInfo _ => "def"
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "thm"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "induct"
          | .ctorInfo _ => "ctor"
          | .recInfo _ => "rec"
          | .quotInfo _ => "quot"
        let body := match c with
          | .defnInfo v => reprStr v.value
          | _ => ""
        stdout.putStrLn <| Json.compress <| Json.mkObj [
          ("name", toJson c.name.toString), ("module", toJson mod),
          ("kind", toJson kind), ("levels", toJson (c.levelParams.map toString)),
          ("type", toJson (reprStr c.type)), ("exposedBody", toJson body)]
    -- Keep mapped expressions alive through serialization.
  if regions.isEmpty then stdout.flush
