/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomial-time word type checking

The color-stack checker threads an optional list through the layers. Each successful layer
increases its length by at most the layer's wire allowance. The structural encoding bounds
the total allowance, giving polynomial growth for the fold.

## Main results

* `Cslib.Complexity.NCL.Slice.computableInPolyTime_typeRun`: polynomial-time layer type checking.
* `Cslib.Complexity.NCL.Word.computableInPolyTime_wellTyped`: polynomial-time closed-word checking.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM
open scoped Slice

private def typeRunData (d : Slice.Data) (cs : List Color) : Option (List Color) :=
  let k := d.offset
  if d.isSwap then
    if k + 2 ≤ cs.length then
      some (cs.take k ++ [cs.getD (k + 1) .red, cs.getD k .red] ++ cs.drop (k + 2))
    else none
  else
    let a := d.inputs
    let b := d.outputs
    if k + a.length ≤ cs.length ∧ (cs.drop k).take a.length = a then
      some (cs.take k ++ b ++ cs.drop (k + a.length))
    else none

private theorem typeRunData_data (sl : Slice) (cs : List Color) :
    typeRunData sl.data cs = sl.typeRun cs := by
  cases sl with
  | gen k a b vs => rfl
  | swap k =>
    dsimp only [typeRunData, Slice.data]
    simp only [ite_true]
    by_cases hk : k + 2 ≤ cs.length
    · simp [Slice.typeRun, hk, List.getElem?_eq_getElem (by omega : k < cs.length),
        List.getElem?_eq_getElem (by omega : k + 1 < cs.length)]
    · rw [ite_eq_right hk]
      by_cases h0 : k < cs.length
      · simp [Slice.typeRun, List.getElem?_eq_getElem h0,
          List.getElem?_eq_none (by omega : cs.length ≤ k + 1)]
      · simp [Slice.typeRun, List.getElem?_eq_none (by omega : cs.length ≤ k)]

private theorem computableInPolyTime_typeRunData :
    ComputableInPolyTime (fun p : Slice.Data × List Color => typeRunData p.1 p.2)
      (encPair Slice.encData (encList encColor)) (encOption (encList encColor)) := by
  unfold typeRunData
  fun_prop

/-- Check one structurally encoded layer against a color stack in polynomial time. -/
@[fun_prop]
theorem Slice.computableInPolyTime_typeRun :
    ComputableInPolyTime (fun p : Slice × List Color => p.1.typeRun p.2)
      (encPair encSlice (encList encColor)) (encOption (encList encColor)) := by
  simpa only [Function.comp_def, typeRunData_data] using computableInPolyTime_typeRunData.comp
    ((Slice.computableInPolyTime_data.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))

private def typeStep (state : Option (List Color)) (sl : Slice) : Option (List Color) :=
  state.bind sl.typeRun

private theorem typeRun_eq_fold (w : Word) (cs : List Color) :
    (Word.typeRun w) cs = w.foldl typeStep (some cs) :=
  List.foldlM_eq_foldl _ _ _

private theorem computableInPolyTime_typeStep :
    ComputableInPolyTime (fun p : Option (List Color) × Slice => typeStep p.1 p.2)
      (encPair (encOption (encList encColor)) encSlice) (encOption (encList encColor)) := by
  have hbody := Slice.computableInPolyTime_typeRun.comp
    (show ComputableInPolyTime (fun p : (Option (List Color) × Slice) × List Color => (p.1.2, p.2))
      (encPair (encPair (encOption (encList encColor)) encSlice) (encList encColor))
      (encPair encSlice (encList encColor)) by fun_prop)
  have he (p : Option (List Color) × Slice) :
      p.1.elim none (fun cs => p.2.typeRun cs) = typeStep p.1 p.2 := by cases p.1 <;> rfl
  simpa only [he] using ComputableInPolyTime.optionElimWithInput
    (body := fun (p : Option (List Color) × Slice) (cs : List Color) => p.2.typeRun cs)
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const (none : Option (List Color))) hbody

private theorem typeRun_length_le (sl : Slice) (cs out : List Color)
    (h : sl.typeRun cs = some out) : out.length ≤ cs.length + sl.cost := by
  rw [← typeRunData_data] at h
  cases sl with
  | gen k a b vs =>
    dsimp only [typeRunData, Slice.data, Slice.Data.isSwap, Slice.Data.offset,
      Slice.Data.inputs, Slice.Data.outputs] at h
    simp only [Bool.false_eq_true, ite_false] at h
    split_ifs at h
    cases h
    simp only [Slice.cost, List.length_append, List.length_take, List.length_drop]
    omega
  | swap k =>
    dsimp only [typeRunData, Slice.data, Slice.Data.isSwap, Slice.Data.offset] at h
    simp only [ite_true] at h
    split_ifs at h
    cases h
    simp only [Slice.cost, List.length_append, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]
    omega

private theorem length_encColor (c : Color) : (encColor c).length = 1 := by
  cases c <;> rfl

private theorem length_encColors (cs : List Color) :
    (encList encColor cs).length = 3 * cs.length := by
  rw [length_encList]
  simp [length_encColor, Nat.mul_comm]

private abbrev encTypes := encOption (encList encColor)

private theorem typeStep_growth (state : Option (List Color)) (sl : Slice) :
    (encTypes (typeStep state sl)).length ≤ (encTypes state).length + 3 * sl.cost := by
  cases state with
  | none => simp [typeStep, encTypes]
  | some cs =>
    change (encTypes (sl.typeRun cs)).length ≤ _
    cases h : sl.typeRun cs with
    | none => simp [encTypes]
    | some out =>
      have hl := typeRun_length_le sl cs out h
      simp only [encTypes, encOption_some, List.length_cons, length_encColors]; omega

private theorem computableInPolyTime_typeFold :
    ComputableInPolyTime (fun w : Word => w.foldl typeStep (some [])) encWord encTypes := by
  let _ : ListEncoding encSlice encWord := by unfold encWord; infer_instance
  let _ : SizedListEncoding encSlice encWord := by unfold encWord; infer_instance
  have hs := computableInPolyTime_typeStep.comp
    (show ComputableInPolyTime (fun p : (Bool × Option (List Color)) × Slice => (p.1.2, p.2))
      (encPair (encPair encBool encTypes) encSlice) (encPair encTypes encSlice) by fun_prop)
  exact ComputableInPolyTime.foldlWith_of_bounded_growth
    (step := fun (_ : Bool) state sl => typeStep state sl)
    (ComputableInPolyTime.const false) ComputableInPolyTime.id'
    (ComputableInPolyTime.const (some [])) hs
    (growth := fun w => 3 * (encWord w).length)
    (PolyBounded.of_polynomiallyBounded (fun w => (encWord w).length) (by fun_prop))
    (fun w state sl hsl => (typeStep_growth state sl).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left 3 ((List.le_sum_of_mem (List.mem_map.mpr ⟨sl, hsl, rfl⟩)).trans
        (Word.cost_le_length_encWord w))) _))

/-- Type-check a complete word from the empty color stack in polynomial time. -/
@[fun_prop]
private theorem Word.computableInPolyTime_typeRun_empty :
    ComputableInPolyTime (fun w : Word => w.typeRun []) encWord (encOption (encList encColor)) := by
  simpa only [← typeRun_eq_fold] using computableInPolyTime_typeFold

/-- Recognize well-typed closed diagram words in polynomial time. -/
@[fun_prop]
theorem Word.computableInPolyTime_wellTyped :
    ComputableInPolyTime (fun w : Word => decide (w.WellTyped [] [])) encWord encBool := by
  have := Word.computableInPolyTime_typeRun_empty
  unfold Word.WellTyped
  fun_prop

end Cslib.Complexity.NCL
