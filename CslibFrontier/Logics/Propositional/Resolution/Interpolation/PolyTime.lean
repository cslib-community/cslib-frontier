/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Logics.Propositional.Resolution.Interpolation.Extraction
public import CslibFrontier.Logics.Propositional.Resolution.Interpolation.MonotoneExtraction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Extracting interpolants in polynomial time

The extraction of interpolant circuits from resolution refutations
(`Cslib.Logic.PL.CNF.interpolantCode`) runs in polynomial time
(`Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`). Its input is the number `n` of
inputs of the circuit in unary, as in `Cslib.Circuits.Boolean.encCircuit`, then the two formulas
and the lines; a variable is a shared variable in binary or a private variable in any encoding with
decidable equality, and clauses and formulas are encoded as lists, as in
`CslibFrontier.Logics.Propositional.CNF.PolyTime`. Its output is the code of the circuit in the
binary encoding `Cslib.Circuits.Boolean.encCode`.

Together with `Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`, this is the effective form of
feasible interpolation [Krajíček, Theorem 6.1][Krajicek1997], [Pudlák, Theorem 1][Pudlak1997]:
the interpolant circuit of a refutation whose shared variables are below `n` is computed from its
lines in polynomial time. The bound is not explicit; each line is justified by scanning all pairs
of earlier lines and all literals of the first, so the running time is polynomial in the number of
lines and their widths.

The same holds for the monotone interpolant (`Cslib.Logic.PL.CNF.monotoneInterpolantCode`), from
the same input, with its output in the binary encoding of monotone circuits
`Cslib.Circuits.Monotone.encCode`
(`Cslib.Logic.PL.CNF.computableInPolyTime_monotoneInterpolantCode`), sharing the polynomial-time
line search and fixed-stride code assembly of `Cslib.Logic.PL.Interpolant.gatesOf`.
Together with `Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`, this is the effective
form of monotone feasible interpolation [Pudlák, Theorem 2][Pudlak1997].

## Main results

* `Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`: the extraction runs in polynomial
  time.
* `Cslib.Logic.PL.CNF.computableInPolyTime_monotoneInterpolantCode`: so does the extraction of the
  monotone interpolant.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {Y Z : Type}

namespace Interpolant

variable {encY : Y ↪ List Bool} {encZ : Z ↪ List Bool}

/-! ### Variables and step search -/

/-- Mapping the right summand while fixing `ℕ` on the left is polynomial-time. -/
private theorem sumMap_id {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encA encB) :
    ComputableInPolyTime (Sum.map id f : ℕ ⊕ α → ℕ ⊕ β) (encSum encNat encA)
      (encSum encNat encB) := by
  have heq : (Sum.map id f : ℕ ⊕ α → ℕ ⊕ β) = Sum.elim Sum.inl (fun a => Sum.inr (f a)) := by
    funext x
    cases x <;> rfl
  rw [heq]
  fun_prop

/-- The embedding of the `A`-variables is polynomial-time. -/
private theorem sumMap_inl :
    ComputableInPolyTime (Sum.map id Sum.inl : ℕ ⊕ Y → ℕ ⊕ (Y ⊕ Z)) (encSum encNat encY)
      (encSum encNat (encSum encY encZ)) :=
  sumMap_id (sumInl _ _)

/-- The embedding of the `B`-variables is polynomial-time. -/
private theorem sumMap_inr :
    ComputableInPolyTime (Sum.map id Sum.inr : ℕ ⊕ Z → ℕ ⊕ (Y ⊕ Z)) (encSum encNat encZ)
      (encSum encNat (encSum encY encZ)) :=
  sumMap_id (sumInr _ _)

/-- A candidate step is encoded as the tuple of its fields, with unary positions. -/
private enc_structure encStep (V : Type) (encV : V ↪ List Bool) : Step V where
  left : (encClause encV), leftIndex : encUnary,
  right : (encClause encV), rightIndex : encUnary, pivot : encV

/-- Candidate resolution steps are listed in polynomial time. -/
private theorem candidates_polyTime {V : Type} {encV : V ↪ List Bool} :
    ComputableInPolyTime (candidates (V := V)) (encList (encClause encV))
      (encList (encStep V encV)) := by
  have hzip := (ComputableInPolyTime.zipIdx (encClause encV))
  unfold candidates
  refine flatMapWithInput hzip (flatMapWithInput (hzip.comp (fst _ _))
    (mapWithInput (fst _ _).snd'.fst' ?_))
  exact encStep_mk_polyTime V encV (fst _ _).fst'.snd'.fst' (fst _ _).fst'.snd'.snd'
    (fst _ _).snd'.fst' (fst _ _).snd'.snd' (snd _ _).fst'

section PolymorphicPolyTime

variable [DecidableEq Y] [DecidableEq Z]

/-- Resolvents are computed in polynomial time. -/
private theorem resolvent_polyTime :
    ComputableInPolyTime (fun q : (Clause (ℕ ⊕ (Y ⊕ Z)) × Clause (ℕ ⊕ (Y ⊕ Z))) × (ℕ ⊕ (Y ⊕ Z)) =>
        q.1.1.resolvent q.1.2 q.2)
      (encPair (encPair (encClause (encSum encNat (encSum encY encZ)))
        (encClause (encSum encNat (encSum encY encZ))))
        (encSum encNat (encSum encY encZ)))
      (encClause (encSum encNat (encSum encY encZ))) := by
  unfold Clause.resolvent
  have hq := id' (encIn := encPair (encPair (encClause (encSum encNat (encSum encY encZ)))
    (encClause (encSum encNat (encSum encY encZ))))
    (encSum encNat (encSum encY encZ)))
  exact listAppend' (filterWithInput hq.fst'.fst'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const true)))))
    (filterWithInput hq.fst'.snd'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const false)))))

/-- Fixed-stride gates of a line are computed in polynomial time whenever the resolution-step gate
builder `step` is polynomial-time. -/
private theorem lineGatesOf_polyTime {Op : Type} {encOp : Op ↪ List Bool}
    (s : ℕ) (constOp : Bool → Op)
    {step : CNF (ℕ ⊕ Y) → ℕ → ℕ → ℕ → (ℕ ⊕ (Y ⊕ Z)) → List (Op × List ℕ)}
    (hstep : ComputableInPolyTime
      (fun r : (CNF (ℕ ⊕ Y) × ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        step r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2)
      (encPair (encPair (encCNFOver (encSum encNat encY))
        (encPair encNat (encPair encNat encNat))) (encSum encNat (encSum encY encZ)))
      (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))) =>
          lineGatesOf s constOp (step q.1.2.1) q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
      (encPair (encPair encUnary (encPair (encCNFOver (encSum encNat encY))
          (encCNFOver (encSum encNat encZ))))
        (encPair (encList (encClause (encSum encNat (encSum encY encZ))))
          (encClause (encSum encNat (encSum encY encZ)))))
      (encList (Circuit.encGate encOp)) := by
  have hq := id' (encIn := encPair (encPair encUnary
    (encPair (encCNFOver (encSum encNat encY)) (encCNFOver (encSum encNat encZ))))
    (encPair (encList (encClause (encSum encNat (encSum encY encZ))))
      (encClause (encSum encNat (encSum encY encZ)))))
  have hc := hq.snd'.snd'
  have hE := hq.snd'.fst'
  have hmemA := decide_mem ((CNF.computableInPolyTime_relabel (sumMap_inl (encZ := encZ))).comp
    hq.fst'.snd'.fst') hc
  have hmemB := decide_mem ((CNF.computableInPolyTime_relabel (sumMap_inr (encY := encY))).comp
    hq.fst'.snd'.snd') hc
  have hbin := ComputableInPolyTime.unary_to_binary
  have hp := id' (encIn := encPair (encPair (encPair encUnary
    (encPair (encCNFOver (encSum encNat encY)) (encCNFOver (encSum encNat encZ))))
    (encPair (encList (encClause (encSum encNat (encSum encY encZ))))
      (encClause (encSum encNat (encSum encY encZ)))))
    (encStep (ℕ ⊕ (Y ⊕ Z)) (encSum encNat (encSum encY encZ))))
  have ht := hp.snd'
  have hc₁ := encStep_left_polyTime _ _ ht
  have hc₂ := encStep_right_polyTime _ _ ht
  have hv := encStep_pivot_polyTime _ _ ht
  have htest := decide_and (decide_mem hc₁ (hv.prod (const true)))
    (decide_and (decide_mem hc₂ (hv.prod (const false)))
      (decide_eq' (resolvent_polyTime.comp ((hc₁.prod hc₂).prod hv)) hp.fst'.snd'.snd'))
  have hfind := findWithInput (test := fun q t => decide ((t.pivot, true) ∈ t.left ∧
    (t.pivot, false) ∈ t.right ∧ t.left.resolvent t.right t.pivot = q.2.2))
    (candidates_polyTime.comp hE) htest
  have hfind_eq : (fun q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
      (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))) => findStep q.2.1 q.2.2) =
      fun x => (candidates x.2.1).find? fun t =>
        decide ((t.pivot, true) ∈ t.left ∧ (t.pivot, false) ∈ t.right ∧
          t.left.resolvent t.right t.pivot = x.2.2) := by
    funext q
    unfold findStep
    refine congrArg (List.find? · (candidates q.2.1)) (funext fun t => ?_)
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  have hm := hp.fst'.fst'.fst'
  have hbody := hstep.comp
    (((hp.fst'.fst'.snd'.fst').prod
      ((hbin.comp (unary_add' hm (unary_mul' (const s)
        ((length_list _).comp hp.fst'.snd'.fst')))).prod
      ((hbin.comp (unary_add' (unary_add' hm
        (unary_mul' (const s) (encStep_leftIndex_polyTime _ _ ht))) (const (s - 1)))).prod
      (hbin.comp (unary_add' (unary_add' hm
        (unary_mul' (const s) (encStep_rightIndex_polyTime _ _ ht))) (const (s - 1))))))).prod hv)
  unfold lineGatesOf
  exact ite_decide hmemA (const _) (ite_decide hmemB (const _)
    (optionElimWithInput (body := fun (q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))))
        (t : Step (ℕ ⊕ (Y ⊕ Z))) =>
      step q.1.2.1 (q.1.1 + s * q.2.1.length) (q.1.1 + s * t.leftIndex + (s - 1))
        (q.1.1 + s * t.rightIndex + (s - 1)) t.pivot) (by rw [hfind_eq]; exact hfind) (const _)
      hbody))

/-- Fixed-stride interpolant code extraction runs in polynomial time whenever its resolution-step
gate builder `step` does. -/
private theorem codeOf_polyTime {Op : Type} {encOp : Op ↪ List Bool}
    (s : ℕ) (constOp : Bool → Op)
    {step : CNF (ℕ ⊕ Y) → ℕ → ℕ → ℕ → (ℕ ⊕ (Y ⊕ Z)) → List (Op × List ℕ)}
    (hstep : ComputableInPolyTime
      (fun r : (CNF (ℕ ⊕ Y) × ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        step r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2)
      (encPair (encPair (encCNFOver (encSum encNat encY))
        (encPair encNat (encPair encNat encNat))) (encSum encNat (encSum encY encZ)))
      (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun p : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
        List (Clause (ℕ ⊕ (Y ⊕ Z))) =>
          (gatesOf s constOp (step p.2.1.1) p.1 p.2.1.1 p.2.1.2 p.2.2.reverse,
            [outputWireOf s p.1 p.2.2.reverse]))
      (encPair encUnary (encPair (encPair (encCNFOver (encSum encNat encY))
        (encCNFOver (encSum encNat encZ)))
        (encList (encClause (encSum encNat (encSum encY encZ))))))
      (Circuit.encCode encOp) := by
  have hp := id' (encIn := encPair encUnary (encPair (encPair
    (encCNFOver (encSum encNat encY)) (encCNFOver (encSum encNat encZ)))
    (encList (encClause (encSum encNat (encSum encY encZ))))))
  have hrev := (ComputableInPolyTime.listReverse
    (encClause (encSum encNat (encSum encY encZ))))
  have hzip := (ComputableInPolyTime.zipIdx
    (encClause (encSum encNat (encSum encY encZ))))
  have htake := (ComputableInPolyTime.takeUnary
    (encClause (encSum encNat (encSum encY encZ))))
  have hbin := ComputableInPolyTime.unary_to_binary
  have hlines := hrev.comp hp.snd'.snd'
  have hgates := flatMapWithInput (f := fun (p : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (e : Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) =>
        lineGatesOf s constOp (step p.2.1.1) p.1 p.2.1.1 p.2.1.2 (p.2.2.reverse.take e.2) e.1)
    (hzip.comp hlines) ((lineGatesOf_polyTime s constOp hstep).comp
      (((fst _ _).fst'.prod (fst _ _).snd'.fst').prod
        ((htake.comp ((hlines.comp (fst _ _)).prod (snd _ _).snd')).prod (snd _ _).fst')))
  have hempty := mapWithInput (f := fun (_ : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) => c.isEmpty) hlines
    ((ComputableInPolyTime.listIsEmpty'
      (encPair (encSum encNat (encSum encY encZ)) encBool)).comp (snd _ _))
  have hidx := (ComputableInPolyTime.idxOf encBool).comp
    (hempty.prod (const true))
  have hout := hbin.comp (unary_add' (unary_add' hp.fst' (unary_mul' (const s) hidx))
    (const (s - 1)))
  exact hgates.prod (cons' hout (const []))

end PolymorphicPolyTime

/-! ### De Morgan gates -/

/-- The gates of a De Morgan resolution step are computed in polynomial time from the wires, in
binary, and the variable. -/
private theorem resolventGates_polyTime :
    ComputableInPolyTime (fun r : (CNF (ℕ ⊕ Y) × ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        resolventGates r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2)
      (encPair (encPair (encCNFOver (encSum encNat encY))
        (encPair encNat (encPair encNat encNat))) (encSum encNat (encSum encY encZ)))
      (encList encGate) := by
  have heq : ∀ base w₁ w₂ (v : ℕ ⊕ (Y ⊕ Z)), resolventGates base w₁ w₂ v =
      v.elim
        (fun i =>
          [(.not, [i]), (.and, [base, w₁]), (.and, [i, w₂]), (.or, [base + 1, base + 2])])
        (fun yz => yz.elim
          (fun _ =>
            [(.const false, []), (.const false, []), (.const false, []), (.or, [w₁, w₂])])
          (fun _ =>
            [(.const false, []), (.const false, []), (.const false, []), (.and, [w₁, w₂])])) := by
    rintro _ _ _ (_ | _ | _) <;> rfl
  simp only [heq]
  fun_prop

end Interpolant

variable [DecidableEq Y] [DecidableEq Z]

/-- **Extracting interpolants in polynomial time.** The code of the interpolant circuit of a
resolution refutation (`Cslib.Logic.PL.CNF.interpolantCode`) is computed in polynomial time from
the number of inputs in unary, the two formulas and the lines of the refutation. Shared variables
are written in binary, private variables in any encodings `encY` and `encZ`, and the circuit code
in the binary encoding `Cslib.Circuits.Boolean.encCode`. On a refutation whose shared variables
are below the number of inputs, the code is that of a circuit computing an interpolant
(`Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`). -/
theorem CNF.computableInPolyTime_interpolantCode (encY : Y ↪ List Bool) (encZ : Z ↪ List Bool) :
    ComputableInPolyTime (fun ((n, (A, B), ls) : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
        List (Clause (ℕ ⊕ (Y ⊕ Z)))) => CNF.interpolantCode n A B ls)
      (encPair encUnary (encPair (encPair (encCNFOver (encSum encNat encY))
        (encCNFOver (encSum encNat encZ)))
        (encList (encClause (encSum encNat (encSum encY encZ))))))
      encCode := by
  unfold CNF.interpolantCode Interpolant.gates Interpolant.outputWire
  exact Interpolant.codeOf_polyTime 4 Op.const
    (step := fun _ => Interpolant.resolventGates) Interpolant.resolventGates_polyTime

/-! ### Monotone gates -/

namespace MonotoneInterpolant

variable {encY : Y ↪ List Bool} {encZ : Z ↪ List Bool}

omit [DecidableEq Y] [DecidableEq Z] in
/-- The polarity test is polynomial-time. -/
private theorem positive_polyTime :
    ComputableInPolyTime (positive (X := ℕ) (Y := Y))
      (encCNFOver (encSum encNat encY)) encBool := by
  have hlit : ComputableInPolyTime
      (fun p : (CNF (ℕ ⊕ Y) × Clause (ℕ ⊕ Y)) × Literal (ℕ ⊕ Y) => p.2.1.isRight || p.2.2)
      (encPair (encPair (encCNFOver (encSum encNat encY))
        (encClause (encSum encNat encY))) (encPair (encSum encNat encY) encBool))
      encBool := by
    have hr : ∀ v : ℕ ⊕ Y, v.isRight = v.elim (fun _ => false) (fun _ => true) := by
      rintro (_ | _) <;> rfl
    simp only [hr]
    fun_prop
  exact allWithEncoding (test := fun p : CNF (ℕ ⊕ Y) × Clause (ℕ ⊕ Y) =>
    p.2.all fun l => l.1.isRight || l.2) (allWithEncoding hlit id' (snd _ _)) id' id'

omit [DecidableEq Y] [DecidableEq Z] in
/-- The gates of a monotone resolution step are computed in polynomial time from the formula `A`,
the wires in binary, and the variable. -/
private theorem resolventGates_polyTime :
    ComputableInPolyTime (fun r : (CNF (ℕ ⊕ Y) × ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        resolventGates (positive r.1.1) r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2)
      (encPair (encPair (encCNFOver (encSum encNat encY))
        (encPair encNat (encPair encNat encNat))) (encSum encNat (encSum encY encZ)))
      (encList Monotone.encGate) := by
  have heq : ∀ pos base w₁ w₂ (v : ℕ ⊕ (Y ⊕ Z)), resolventGates pos base w₁ w₂ v =
      v.elim
        (fun i => if pos then [(.or, [i, w₁]), (.and, [base, w₂])]
          else [(.and, [i, w₂]), (.or, [base, w₁])])
        (fun yz => yz.elim
          (fun _ => [(.const false, []), (.or, [w₁, w₂])])
          (fun _ => [(.const false, []), (.and, [w₁, w₂])])) := by
    rintro _ _ _ _ (_ | _ | _) <;> rfl
  have hpos := positive_polyTime (encY := encY)
  simp only [heq]
  fun_prop

end MonotoneInterpolant

/-- **Extracting monotone interpolants in polynomial time.** The code of the monotone interpolant
circuit of a resolution refutation (`Cslib.Logic.PL.CNF.monotoneInterpolantCode`) is computed in
polynomial time from the number of inputs in unary, the two formulas and the lines of the
refutation, encoded as for `Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`; the circuit
code is written in the binary encoding `Cslib.Circuits.Monotone.encCode`. On a refutation whose
shared variables are below the number of inputs and occur only positively in `A` or only
negatively in `B`, the code is that of a monotone circuit computing an interpolant
(`Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`). -/
theorem CNF.computableInPolyTime_monotoneInterpolantCode (encY : Y ↪ List Bool)
    (encZ : Z ↪ List Bool) :
    ComputableInPolyTime (fun ((n, (A, B), ls) : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
        List (Clause (ℕ ⊕ (Y ⊕ Z)))) => CNF.monotoneInterpolantCode n A B ls)
      (encPair encUnary (encPair (encPair (encCNFOver (encSum encNat encY))
        (encCNFOver (encSum encNat encZ)))
        (encList (encClause (encSum encNat (encSum encY encZ))))))
      Monotone.encCode := by
  unfold CNF.monotoneInterpolantCode MonotoneInterpolant.gates MonotoneInterpolant.outputWire
  exact Interpolant.codeOf_polyTime 2 Monotone.Op.const
    (step := fun A => MonotoneInterpolant.resolventGates (MonotoneInterpolant.positive A))
    MonotoneInterpolant.resolventGates_polyTime

end Cslib.Logic.PL
