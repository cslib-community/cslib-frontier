/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Encoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time execution of structurally encoded layers

A compiler state encodes wire labels and the next edge number in unary, and vertices by their
standard binary graph encoding. Structurally encoded layers run uniformly in polynomial time;
local edge indices are converted to the actual wire labels.

## Main definitions

* `Cslib.Complexity.NCL.Word.encState`: structural encoding of compiler states.

## Main results

* `Cslib.Complexity.NCL.Slice.computableInPolyTime_run`: execution of arbitrary layers.


## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM
open scoped Slice

/-- Encode wire labels and the edge counter in unary, and emitted graph vertices structurally. -/
@[expose] def Word.encState : Word.State ↪ List Bool :=
  (show Word.State ↪ (List ℕ × ℕ) × List (Vertex ℕ) from
    { toFun st := ((st.wires, st.next), st.verts)
      inj' := by rintro ⟨w, n, vs⟩ ⟨w', n', vs'⟩ h; cases h; rfl }).trans
    (encPair (encPair (encList encUnary) encUnary) (encList (encVertex encNat)))

private theorem Word.State.computableInPolyTime_data :
    ComputableInPolyTime (fun st : Word.State => ((st.wires, st.next), st.verts)) Word.encState
      (encPair (encPair (encList encUnary) encUnary) (encList (encVertex encNat))) :=
  ComputableInPolyTime.of_eq (fun _ => rfl)

/-- Read a compiler state's wire stack in polynomial time. -/
@[fun_prop]
theorem Word.State.computableInPolyTime_wires :
    ComputableInPolyTime Word.State.wires Word.encState (encList encUnary) :=
  Word.State.computableInPolyTime_data.fst'.fst'

/-- Read a compiler state's next edge number in polynomial time. -/
@[fun_prop]
theorem Word.State.computableInPolyTime_next :
    ComputableInPolyTime Word.State.next Word.encState encUnary :=
  Word.State.computableInPolyTime_data.fst'.snd'

/-- Read a compiler state's vertex output in polynomial time. -/
@[fun_prop]
theorem Word.State.computableInPolyTime_verts :
    ComputableInPolyTime Word.State.verts Word.encState (encList (encVertex encNat)) :=
  Word.State.computableInPolyTime_data.snd'

private theorem computableInPolyTime_stateData :
    ComputableInPolyTime
      (fun p : (List ℕ × ℕ) × List (Vertex ℕ) => Word.State.mk p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encUnary) encUnary) (encList (encVertex encNat))) Word.encState :=
  ComputableInPolyTime.of_eq (fun _ => rfl)

/-- Assemble a compiler state from polynomial-time fields. -/
@[fun_prop]
theorem Word.State.computableInPolyTime_mk {α : Type} {input : α ↪ List Bool}
    {w : α → List ℕ} {n : α → ℕ} {vs : α → List (Vertex ℕ)}
    (hw : ComputableInPolyTime w input (encList encUnary))
    (hn : ComputableInPolyTime n input encUnary)
    (hv : ComputableInPolyTime vs input (encList (encVertex encNat))) :
    ComputableInPolyTime (fun x => Word.State.mk (w x) (n x) (vs x)) input Word.encState := by
  change ComputableInPolyTime
    ((fun p : (List ℕ × ℕ) × List (Vertex ℕ) => Word.State.mk p.1.1 p.1.2 p.2) ∘
      fun x => ((w x, n x), vs x)) input Word.encState
  exact computableInPolyTime_stateData.comp ((hw.prod hn).prod hv)

private abbrev stepInput := encPair encUnary Word.encState

private theorem computableInPolyTime_run_swap :
    ComputableInPolyTime (fun p : ℕ × Word.State => (Slice.swap p.1).run p.2)
      stepInput Word.encState := by
  have hk := ComputableInPolyTime.fst encUnary Word.encState
  have hs := ComputableInPolyTime.snd encUnary Word.encState
  have hw := Word.State.computableInPolyTime_wires.comp hs
  have hfirst := ComputableInPolyTime.listGetDWithInput hw
    (show ComputableInPolyTime (fun p : ℕ × Word.State => p.1 + 1) stepInput encUnary by
      unfold stepInput
      fun_prop) 0
  have hsecond := ComputableInPolyTime.listGetDWithInput hw hk 0
  unfold Slice.run
  exact Word.State.computableInPolyTime_mk
    (((ComputableInPolyTime.listTakeWithInput hw hk).listAppend'
      (hfirst.cons' (hsecond.cons' (.const [])))).listAppend'
        (ComputableInPolyTime.listDropWithInput hw (by fun_prop)))
    (Word.State.computableInPolyTime_next.comp hs) (Word.State.computableInPolyTime_verts.comp hs)

private def runData (d : Slice.Data) (st : Word.State) : Word.State :=
  if d.isSwap then (Slice.swap d.offset).run st else
    let k := d.offset
    let a := d.inputs
    let b := d.outputs
    let vs := d.vertices
    ⟨st.wires.take k ++ ((List.range b.length).map (st.next + ·)) ++
        st.wires.drop (k + a.length),
      st.next + b.length,
      st.verts ++ vs.map (Vertex.map (fun e =>
        if e.1 then st.wires.getD (k + e.2) 0 else st.next + e.2))⟩

private theorem runData_data (sl : Slice) (st : Word.State) : runData sl.data st = sl.run st := by
  cases sl with
  | swap k => rfl
  | gen k a b vs =>
    simp only [runData, Slice.data, Bool.false_eq_true, ite_false, Slice.run, List.map_map]
    congr 2
    · exact congrArg _ (List.ext_getElem (by simp) (by simp))
    · congr 2
      exact Vertex.map_comp_map fun e => by cases e <;> rfl


private abbrev encDataState := encPair Slice.encData Word.encState

private theorem computableInPolyTime_runData_vertices :
    ComputableInPolyTime (fun p : Slice.Data × Word.State => p.1.vertices.map
      (Vertex.map (fun e => if e.1 then p.2.wires.getD (p.1.offset + e.2) 0 else p.2.next + e.2)))
      encDataState (encList (encVertex encNat)) := by
  have hu : ComputableInPolyTime
      (fun p : ((Slice.Data × Word.State) × Vertex (Bool × ℕ)) × (Bool × ℕ) =>
        let ⟨⟨⟨data, state⟩, _⟩, edge⟩ := p
        if edge.1 then state.wires.getD (data.offset + edge.2) 0 else state.next + edge.2)
      (encPair (encPair encDataState (encVertex (encPair encBool encUnary)))
        (encPair encBool encUnary)) encUnary := by
    unfold encDataState Slice.encData
    fun_prop
  exact ComputableInPolyTime.mapWithInput
    (by
      unfold encDataState Slice.encData
      fun_prop)
    (Vertex.computableInPolyTime_mapWithInput (.snd _ _)
      (ComputableInPolyTime.unary_to_binary.comp hu))

private theorem computableInPolyTime_runData :
    ComputableInPolyTime (fun p : Slice.Data × Word.State => runData p.1 p.2)
      encDataState Word.encState := by
  have hs := ComputableInPolyTime.snd Slice.encData Word.encState
  have hw := Word.State.computableInPolyTime_wires.comp hs
  have hk : ComputableInPolyTime (fun p : Slice.Data × Word.State => p.1.offset)
      encDataState encUnary := by
    unfold encDataState Slice.encData
    fun_prop
  have hswap : ComputableInPolyTime (fun p : Slice.Data × Word.State =>
      (Slice.swap p.1.offset).run p.2) encDataState Word.encState := by
    change ComputableInPolyTime
      ((fun p : ℕ × Word.State => (Slice.swap p.1).run p.2) ∘
        fun p : Slice.Data × Word.State => (p.1.offset, p.2)) encDataState Word.encState
    exact computableInPolyTime_run_swap.comp (hk.prod hs)
  refine ComputableInPolyTime.ite
    (by
      unfold encDataState Slice.encData
      fun_prop) hswap ?_
  exact Word.State.computableInPolyTime_mk
    (((ComputableInPolyTime.listTakeWithInput hw hk).listAppend'
      (by
        unfold Slice.encData
        fun_prop)).listAppend'
        (ComputableInPolyTime.listDropWithInput hw
          (hk.unary_add' (by
            unfold encDataState Slice.encData
            fun_prop))))
    ((Word.State.computableInPolyTime_next.comp hs).unary_add'
      (by
        unfold Slice.encData
        fun_prop))
    ((Word.State.computableInPolyTime_verts.comp hs).listAppend'
      computableInPolyTime_runData_vertices)


/-- Execute an arbitrary encoded layer on an encoded compiler state in polynomial time. -/
@[fun_prop]
theorem Slice.computableInPolyTime_run :
    ComputableInPolyTime (fun p : Slice × Word.State => p.1.run p.2)
      (encPair encSlice Word.encState) Word.encState := by
  simpa only [Function.comp_def, Prod.map, runData_data] using computableInPolyTime_runData.comp
    ((Slice.computableInPolyTime_data.comp (.fst _ _)).prod (.snd _ _))

end Cslib.Complexity.NCL
