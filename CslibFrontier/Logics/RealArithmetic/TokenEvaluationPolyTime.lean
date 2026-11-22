/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.ModularEvaluation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Polynomial-time transition for modular term evaluation

Each transition charges the encoded token, binary modulus, coordinate list, and residue stack.
It retains the unary variable ranks of the term encoding and charges the binary modular
arithmetic. This certifies one transition of the constructor-stream evaluator, adapting the
case dispatch of `TermModularFrames` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` to the frontier encodings.
-/

public section

namespace Cslib.Logic.RealArithmetic.Term

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private theorem pushResidue_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {value : γ → ℕ} {stack : γ → List ℕ}
    (hvalue : ComputableInPolyTime value enc encNat)
    (hstack : ComputableInPolyTime stack enc (encList encNat)) :
    ComputableInPolyTime (fun a => some (value a :: stack a)) enc
      (encOption (encList encNat)) :=
  (optionSome _).comp ((cons encNat).comp (hvalue.prod hstack))

private def combineResidues (op : ℕ × ℕ → ℕ) (p : ℕ) (stack : List ℕ) : Option (List ℕ) :=
  if stack.tail.isEmpty then none
  else some (op (stack.headD 0, stack.tail.headD 0) % p :: stack.tail.tail)

private theorem combineResidues_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {op : ℕ × ℕ → ℕ} (hop : ComputableInPolyTime op (encPair encNat encNat) encNat)
    {modulus : γ → ℕ} {stack : γ → List ℕ}
    (hp : ComputableInPolyTime modulus enc encNat)
    (hs : ComputableInPolyTime stack enc (encList encNat)) :
    ComputableInPolyTime (fun a => combineResidues op (modulus a) (stack a)) enc
      (encOption (encList encNat)) := by
  have ht := (listTail encNat).comp hs
  have hl := (headD (encA := encNat) 0).comp hs
  have hr := (headD (encA := encNat) 0).comp ht
  have hvalue := binary_mod' (hop.comp (hl.prod hr)) hp
  exact ((listIsEmpty' encNat).comp ht).ite' (.const none)
    (pushResidue_polyTime hvalue ((listTail encNat).comp ht))

/-- Evaluate one constructor token in polynomial time. The modulus, coordinates and stack
entries use binary naturals, and the token's variable rank uses the term encoding's unary rank.
The result is an optional framed residue list. -/
theorem evalTokenStep_polyTime {γ : Type} {enc : γ ↪ List Bool} {n : ℕ}
    {modulus : γ → ℕ} {point stack : γ → List ℕ} {token : γ → ℤ ⊕ Fin n ⊕ Unit ⊕ Unit}
    (hp : ComputableInPolyTime modulus enc encNat)
    (hx : ComputableInPolyTime point enc (encList encNat))
    (hs : ComputableInPolyTime stack enc (encList encNat))
    (ht : ComputableInPolyTime token enc (encTermTokenEncoding n)) :
    ComputableInPolyTime (fun a => evalTokenStep (modulus a) (point a) (token a) (stack a))
      enc (encOption (encList encNat)) := by
  have hz := snd enc encIntBin
  have hc := pushResidue_polyTime (intBin_emodNat' hz (hp.comp (fst enc encIntBin)))
    (hs.comp (fst enc encIntBin))
  let rank := encFinEnum (Fin n)
  have hi := finVal (snd enc rank)
  have hcoord := listGetDWithInput (hx.comp (fst enc rank)) hi 0
  have hv := pushResidue_polyTime (binary_mod' hcoord (hp.comp (fst enc rank)))
    (hs.comp (fst enc rank))
  have hpUnit := hp.comp (fst enc encUnit)
  have hsUnit := hs.comp (fst enc encUnit)
  let add (a : γ) (_ : Unit) := combineResidues (fun p => p.1 + p.2) (modulus a) (stack a)
  let mul (a : γ) (_ : Unit) := combineResidues (fun p => p.1 * p.2) (modulus a) (stack a)
  let op (a : γ) (tag : Unit ⊕ Unit) := tag.elim (add a) (mul a)
  let var (a : γ) (i : Fin n) := some ((point a).getD i.val 0 % modulus a :: stack a)
  let varOrOp (a : γ) (tag : Fin n ⊕ Unit ⊕ Unit) := tag.elim (var a) (op a)
  have ho := sumElimSnd (left := add) (right := mul) none
    (combineResidues_polyTime binary_add hpUnit hsUnit)
    (combineResidues_polyTime binary_mul hpUnit hsUnit)
  have hvarOrOp := sumElimSnd (left := var) (right := op) none hv ho
  have h := sumElimWithInput
    (left := fun a z => some ((z % (modulus a : ℤ)).toNat :: stack a)) (right := varOrOp)
    none ht hc hvarOrOp
  apply h.of_enc_eq
  intro a
  apply congrArg (encOption (encList encNat))
  rcases token a with z | (i | (_ | _))
  · rfl
  · simp only [evalTokenStep, Sum.elim_inr, Sum.elim_inl, List.getD_eq_getElem?_getD, var, varOrOp]
  all_goals
    dsimp only [varOrOp, op, add, mul, Sum.elim]
    rcases stack a with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> rfl

end Cslib.Logic.RealArithmetic.Term
