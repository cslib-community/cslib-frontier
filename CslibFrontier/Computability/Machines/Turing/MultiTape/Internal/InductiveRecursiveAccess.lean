/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeLifts
public meta import Lean.Elab.Command

/-!
# Native access rules for flat recursive inductive encodings

The recursive branch of `enc_inductive` uses a framed scalar token followed by flat child
streams. Its constructor matchers read the token's finite tag, and scalar projections read
fields of that token. These operations need no scalar decoder. Recursive-field extraction and
its stream scanner are handled separately.
-/

public meta section

namespace Turing.MultiTapeTM.Internal

open Lean Elab Command

private def suffix (name : Name) (s : String) : Ident := mkIdent (name.appendAfter s)

private def applied (ps : Array Ident) (name : Ident) : Term :=
  Syntax.mkApp name (ps.map (⟨·.raw⟩))

/-- Emit the linear time, charged-space, and polynomial views of a generated degree rule. -/
private def linearViews (ps : Array Ident)
    (params : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
    (fn encIn encOut : Term) (name : Name) : CommandElabM Unit := do
  let current ← getCurrNamespace
  let decl (s : String) := mkIdent ((name.appendAfter s).replacePrefix current .anonymous)
  let degree := applied ps (suffix name "_deg")
  let (linear, space, polynomial) ← liftMacroM <| linearDegreeViews degree
  elabCommand (← `(@[scoped fun_prop] public theorem $(decl "_inO"):ident $params* :
    ComputableInO $fn $encIn $encOut (fun value => ($encIn value).length)
      (fun value => ($encIn value).length) := $linear))
  elabCommand (← `(@[scoped fun_prop] public theorem $(decl "_inSpace"):ident $params* :
    ComputableInSpace $fn $encIn $encOut (fun value => ($encIn value).length) := $space))
  elabCommand (← `(@[scoped fun_prop] public theorem $(decl "_polyTime"):ident $params* :
    ComputableInPolyTime $fn $encIn $encOut := $polynomial))

/-- Generate native rules for the constructor matchers and scalar fields of a checked flat
recursive encoding. Constructor equations, semantic matchers, and semantic field projections
must already have been declared by `enc_inductive`. Recursive fields are omitted here. -/
def elabRecursiveAccess (eT : Ident) (ps : Array Ident)
    (params : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) (T : Term) (cs : Array Ident)
    (encss : Array (Array Term)) (recursive : Array (Array Bool)) : CommandElabM Unit := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo eT
  let current ← getCurrNamespace
  let decl (full : Name) := mkIdent (full.replacePrefix current .anonymous)
  let encoding := applied ps (mkIdent name)
  let tokenEncoding := suffix name "TokenEncoding"
  let ctorEquations := cs.map fun c => suffix name s!"_{c.getId}_apply"
  let n := cs.size
  for i in [0:n] do
    let matcher := suffix name s!"_{cs[i]!.getId}_matches"
    let matcherRef := applied ps matcher
    let matcherDegree := suffix matcher.getId "_deg"
    -- Remove only the root token's frame. The child streams are never reframed.
    let mut raw : Term ← `(ComputableInDegree.of_unframe
      (f := fun value : $T => unframe ($encoding value))
      (encIn := $encoding) (encMid := encBits) (fun _ => rfl))
    let mut test : Term ← `(ComputableInDegree.const
      (encIn := $encoding) (encMid := encBool) true)
    let tags := i + (if i + 1 < n then 1 else 0)
    for j in [0:tags] do
      let bit : Term ← `((ComputableInDegree.headD
        (enc₁ := encBool) (enc := encBits) false).comp $raw)
      let wanted ← if j < i then pure bit else
        `((ComputableInDegree.of_finite
          (encIn := encBool) (encMid := encBool) Bool.not).comp $bit)
      test ← `((ComputableInDegree.of_finite (encIn := encPair encBool encBool)
        (encMid := encBool) (fun pair : Bool × Bool => pair.1 && pair.2)).comp
          (($test).prod $wanted))
      raw ← `((ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).comp $raw)
    elabCommand (← `(@[scoped fun_prop] public theorem $(decl matcherDegree.getId):ident $params* :
        ComputableInDegree $matcherRef $encoding encBool 1 0 :=
      (($test).mono (d' := 1) (e' := 0)).of_enc_eq (fun value => by
        cases value <;>
          simp [$matcher:ident, $[$ctorEquations:ident],*, $tokenEncoding:ident,
            encBits, encBool, List.headD, unframe_frame_append, unframe])))
    linearViews ps params matcherRef encoding (← `(encBool)) matcher.getId
    let scalarIndices := (Array.range (recursive[i]!).size).filter fun j => !(recursive[i]!)[j]!
    for scalarIndex in [0:scalarIndices.size] do
      let fieldIndex := scalarIndices[scalarIndex]!
      let projection := suffix name s!"_{cs[i]!.getId}_field{fieldIndex}?"
      let projectionRef := applied ps projection
      let out := (encss[i]!)[fieldIndex]!
      let mut word := raw
      for _ in [0:scalarIndex] do
        word ← `((ComputableInDegree.of_dropFrame (f := dropFrame)
          (encIn := encBits) (encMid := encBits) (fun _ => rfl)).comp $word)
      if scalarIndex + 1 < scalarIndices.size then
        word ← `((ComputableInDegree.of_unframe (f := unframe)
          (encIn := encBits) (encMid := encBits) (fun _ => rfl)).comp $word)
      let someWord ← `((ComputableInDegree.const
        (encIn := $encoding) (encMid := encBool) true).append $word (fun _ => rfl))
      let matcherDegreeRef := applied ps matcherDegree
      elabCommand (← `(@[scoped fun_prop] public theorem
          $(decl (projection.getId.appendAfter "_deg")):ident $params* :
          ComputableInDegree $projectionRef $encoding (encOption $out) 1 1 := by
        have hn : ComputableInDegree (fun _ : $T => ([] : List Bool))
            $encoding encBits 1 1 := (ComputableInDegree.const (encMid := encBits) []).mono
        exact ((($matcherDegreeRef).ite
          (($someWord).restrict _) (hn.restrict _)).mono (d' := 1) (e' := 1)).of_enc_eq
            (fun value => by
              cases value <;>
                simp [$projection:ident, $matcher:ident, $[$ctorEquations:ident],*,
                  $tokenEncoding:ident, encBits, unframe_frame_append,
                  dropFrame_frame_append, unframe, dropFrame]
              all_goals rfl)))
      linearViews ps params projectionRef encoding (← `(encOption $out)) projection.getId

end Turing.MultiTapeTM.Internal
