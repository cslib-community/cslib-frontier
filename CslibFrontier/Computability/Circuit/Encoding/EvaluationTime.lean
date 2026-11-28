/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Evaluation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time evaluation of circuit codes over finite signatures and carriers

For any `Signature` with finitely many operation symbols `[Finite σ.Op]` and any finite carrier
`[Finite U]`, the total gate-list evaluator `Cslib.Circuits.evalCode` runs in polynomial time on
framed input lists (`encList eU`) and binary-indexed gate lists (`encList (Circuit.encGate eOp)`).
Each step dispatches on the finite operation tag (`ComputableInPolyTime.finite_cases`), reads its
arguments by capped binary lookup (`listGetD_binary`), applies the finite gate table, and appends
one carrier value whose encoded length is bounded by a constant depending only on `(U, eU)`.

Both `CslibFrontier.Computability.Circuit.Boolean.EvaluationTime` and
`CslibFrontier.Computability.Circuit.Arithmetic.EvaluationTime` specialize these certificates.

## Main definitions

* `Cslib.Circuits.evalOutputs`: evaluate all output wire numbers listed in a raw circuit code.

## Main results

* `Cslib.Circuits.Circuit.evalOutputs_code`: `evalOutputs` on a typed circuit's code produces
  `List.ofFn (c.eval I x)`.
* `Cslib.Circuits.computableInPolyTime_evalCode`: polynomial-time evaluation of gate lists over a
  finite operation set and finite carrier.
* `Cslib.Circuits.computableInPolyTime_evalOutput`,
  `Cslib.Circuits.computableInPolyTime_evalOutputs`: polynomial-time evaluation of one or all
  designated binary output wire numbers.
-/

public section

namespace Cslib.Circuits

open Turing.MultiTapeTM ComputableInPolyTime

section MultiOutput

universe u v

/-- Evaluate all output wires listed in `code.2` after running the gate list `code.1` on `x`. -/
@[expose]
def evalOutputs {σ : Signature.{v}} {U : Type u} (I : Interpretation σ U) (d : U)
    (code : List (σ.Op × List ℕ) × List ℕ) (x : List U) : List U :=
  let vals := evalCode I d x code.1
  code.2.map fun o => vals.getD o d

/-- On the code of a typed circuit, `evalOutputs` computes the list of output values. -/
theorem Circuit.evalOutputs_code {σ : Signature.{v}} {U : Type u} {n m : ℕ}
    (c : Circuit σ n m) (I : Interpretation σ U) (d : U) (x : Fin n → U) :
    evalOutputs I d c.code (List.ofFn x) = List.ofFn (c.eval I x) := by
  refine List.ext_getElem (by simp [evalOutputs, Circuit.code]) fun j hj₁ hj₂ => ?_
  simp only [evalOutputs, List.getElem_map, Circuit.code, List.getElem_ofFn]
  exact (c.eval_eq_getD I d x ⟨j, by simpa using hj₂⟩).symm

end MultiOutput

section FiniteCarrier

variable {σ : Signature} {U α : Type} [Finite σ.Op] [Finite U]
  {eOp : σ.Op ↪ List Bool} {eU : U ↪ List Bool} {encIn : α ↪ List Bool}

private theorem polyTime_step (I : Interpretation σ U) (d : U) :
    ComputableInPolyTime (fun p : List U × (σ.Op × List ℕ) =>
      p.1 ++ [I p.2.1 fun a => p.2.2[a.val]?.elim d (p.1.getD · d)])
      (encPair (encList eU) (Circuit.encGate eOp)) (encList eU) := by
  have harg (i : ℕ) : ComputableInPolyTime (fun p : List U × (σ.Op × List ℕ) =>
      p.2.2[i]?.elim d (p.1.getD · d))
      (encPair (encList eU) (Circuit.encGate eOp)) eU :=
    optionElimWithInput (getElem? (snd _ _).snd' (const i)) (const d)
      (listGetD_binary d (fst _ _).fst' (snd _ _))
  exact listAppend' (.fst _ _) (cons' (finite_cases (tagEncoding := eOp)
    (branch := fun op (p : List U × (σ.Op × List ℕ)) =>
      I op fun a => p.2.2[a.val]?.elim d (p.1.getD · d))
    (snd _ _).fst' fun op => (of_finite (encIn := encPi eU) (encOut := eU) (I op)).comp
      (pi fun a => harg a.val)) (.const []))

/-- **Polynomial-time evaluation** of gate lists over a finite operation set and finite carrier,
charging the framed input list and binary-indexed gate list. -/
@[fun_prop]
protected theorem computableInPolyTime_evalCode (I : Interpretation σ U) (d : U)
    {x : α → List U} {gates : α → List (σ.Op × List ℕ)}
    (hx : ComputableInPolyTime x encIn (encList eU))
    (hgates : ComputableInPolyTime gates encIn (encList (Circuit.encGate eOp))) :
    ComputableInPolyTime (fun a => evalCode I d (x a) (gates a)) encIn (encList eU) := by
  let _ := Fintype.ofFinite U
  let bound := Finset.univ.sup fun u : U => (eU u).length
  refine ComputableInPolyTime.foldl_of_bounded_growth hgates hx
    (polyTime_step (eOp := eOp) (eU := eU) I d) (growth := 2 * bound + 1) fun _ _ => ?_
  simp only [evalCodeStep, encList_append, encList_cons, encList_nil, List.append_nil,
    List.length_append, length_frame]
  exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Finset.le_sup (f := fun u : U => (eU u).length) (Finset.mem_univ _))) 1) _

/-- Read a binary-indexed output wire from the computed gate trace in polynomial time. -/
@[fun_prop]
protected theorem computableInPolyTime_evalOutput (I : Interpretation σ U) (d : U)
    {x : α → List U} {gates : α → List (σ.Op × List ℕ)} {output : α → ℕ}
    (hx : ComputableInPolyTime x encIn (encList eU))
    (hgates : ComputableInPolyTime gates encIn (encList (Circuit.encGate eOp)))
    (houtput : ComputableInPolyTime output encIn encNat) :
    ComputableInPolyTime (fun a => (evalCode I d (x a) (gates a)).getD (output a) d) encIn eU :=
  listGetD_binary d (Circuits.computableInPolyTime_evalCode I d hx hgates) houtput

/-- Evaluate every output wire listed by a runtime circuit code in polynomial time. -/
@[fun_prop]
protected theorem computableInPolyTime_evalOutputs (I : Interpretation σ U) (d : U)
    {code : α → List (σ.Op × List ℕ) × List ℕ} {x : α → List U}
    (hcode : ComputableInPolyTime code encIn (Circuit.encCode eOp))
    (hx : ComputableInPolyTime x encIn (encList eU)) :
    ComputableInPolyTime (fun a => evalOutputs I d (code a) (x a)) encIn (encList eU) :=
  mapWithInput hcode.snd' (listGetD_binary d
    ((Circuits.computableInPolyTime_evalCode I d hx hcode.fst').comp (fst encIn encNat))
    (snd encIn encNat))

end FiniteCarrier

end Cslib.Circuits
