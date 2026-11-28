/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.Compression
import CslibFrontier.Logics.Propositional.CNF.PolyTimeWithInput
import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
import CslibFrontier.Computability.Complexity.CookLevin.Encoding

/-!
# Polynomial time for the checked decoders

The words and circuits of `Cslib.Circuits.Boolean.SymAnd.Compression` are computed in polynomial
time from `x` (and the guessed word `e`): the lengths `wordLength`, `steps`, `width`, the output
variable `outVar`, the check formula `checkFormula` (the run tableau of every copy, renumbered into
its block by a renaming computed from the copy), the prefixes of the copies of `G`, and the codes of
the circuits `guessed`, `checkCircuit` and `decoderCircuit`. This is the uniformity of the
compression step of [Williams2014], Lemma 3.1.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.Compression.computableInPolyTime_checkFormula`: the check formula.
* `Cslib.Circuits.Boolean.SymAnd.Compression.computableInPolyTime_checkCircuit_code`: the code of
  the check circuit.
* `Cslib.Circuits.Boolean.SymAnd.Compression.computableInPolyTime_decoderCircuit_code`: the code of
  the decoder.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Lemma 3.1]
  [Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInPolyTime
  Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Complexity.CookLevin Cslib.Logic.PL

namespace Compression

/-! ### Polynomial time -/

section PolyTime

variable {α : Type} {encIn : α ↪ List Bool}

/-- The word `unaryWord n j` is polynomial-time from `n` and `j` in unary. -/
theorem computableInPolyTime_unaryWord {n j : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => unaryWord (n a) (j a)) encIn encBits := by
  unfold unaryWord
  have h1 := ComputableInPolyTime.replicate (encA := encBool) hj
    (ComputableInPolyTime.const (encIn := encIn) true)
  have h2 := ComputableInPolyTime.replicate (encA := encBool)
    (unary_sub' hn hj) (ComputableInPolyTime.const (encIn := encIn) false)
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.listToBits.comp h1)
    (ComputableInPolyTime.listToBits.comp h2)

end PolyTime

/-- **The query bit is polynomial-time** when the function `F` and the width `J` of the
unary index are. -/
theorem computableInPolyTime_queryBit {J : List Bool → ℕ}
    {F : List Bool × List Bool → List Bool}
    (hJ : ComputableInPolyTime J encBits encUnary)
    (hF : ComputableInPolyTime F (encPair encBits encBits) encBits) :
    ComputableInPolyTime (queryBit J F) encBits encBool := by
  have hx : ComputableInPolyTime _root_.Turing.MultiTapeTM.unframe encBits encBits :=
    ComputableInPolyTime.unframe
  have hd : ComputableInPolyTime _root_.Turing.MultiTapeTM.dropFrame encBits encBits :=
    ComputableInPolyTime.dropFrame
  have hJx : ComputableInPolyTime (fun w => J (_root_.Turing.MultiTapeTM.unframe w)) encBits
      encUnary := hJ.comp hx
  have hi := bitsDropWithInput hd hJx
  have hF' := hF.comp (hx.prod hi)
  have hc : ComputableInPolyTime (fun w => ((_root_.Turing.MultiTapeTM.dropFrame w).take
      (J (_root_.Turing.MultiTapeTM.unframe w))).count true) encBits encUnary :=
    countWithInput (ComputableInPolyTime.bitsToList.comp (bitsTakeWithInput hd hJx))
      (ComputableInPolyTime.const true)
  exact bitsGetDWithInput hF' hc false

/-- **The run bit is polynomial-time** when the widths `J` and `V` are. -/
theorem computableInPolyTime_runBit {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
    (tm : MultiTapeTM k Bool State) (cT dT : ℕ) {J V : List Bool → ℕ}
    (hJ : ComputableInPolyTime J encBits encUnary)
    (hV : ComputableInPolyTime V encBits encUnary) :
    ComputableInPolyTime (runBit tm cT dT J V) encBits encBool := by
  have hx : ComputableInPolyTime _root_.Turing.MultiTapeTM.unframe encBits encBits :=
    ComputableInPolyTime.unframe
  have hd : ComputableInPolyTime _root_.Turing.MultiTapeTM.dropFrame encBits encBits :=
    ComputableInPolyTime.dropFrame
  have hJx : ComputableInPolyTime (fun w => J (_root_.Turing.MultiTapeTM.unframe w)) encBits
      encUnary := hJ.comp hx
  have hVx : ComputableInPolyTime (fun w => V (_root_.Turing.MultiTapeTM.unframe w)) encBits
      encUnary := hV.comp hx
  have hj : ComputableInPolyTime (fun w => ((_root_.Turing.MultiTapeTM.dropFrame w).take
      (J (_root_.Turing.MultiTapeTM.unframe w))).count true) encBits encUnary :=
    countWithInput (ComputableInPolyTime.bitsToList.comp (bitsTakeWithInput hd hJx))
      (ComputableInPolyTime.const true)
  have hv : ComputableInPolyTime (fun w => (((_root_.Turing.MultiTapeTM.dropFrame w).drop
      (J (_root_.Turing.MultiTapeTM.unframe w))).take
        (V (_root_.Turing.MultiTapeTM.unframe w))).count true) encBits encUnary :=
    countWithInput (ComputableInPolyTime.bitsToList.comp
      (bitsTakeWithInput (bitsDropWithInput hd hJx) hVx)) (ComputableInPolyTime.const true)
  have hrest := bitsDropWithInput hd (unary_add' hJx hVx)
  have hu : ComputableInPolyTime (fun w => queryWord (J (_root_.Turing.MultiTapeTM.unframe w))
      (_root_.Turing.MultiTapeTM.unframe w) (((_root_.Turing.MultiTapeTM.dropFrame w).take
        (J (_root_.Turing.MultiTapeTM.unframe w))).count true)
      ((_root_.Turing.MultiTapeTM.dropFrame w).drop (J (_root_.Turing.MultiTapeTM.unframe w) +
        V (_root_.Turing.MultiTapeTM.unframe w)))) encBits encBits := by
    unfold queryWord
    exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.frame.comp hx) (computableInPolyTime_unaryWord hJx hj)) hrest
  have hlen := ComputableInPolyTime.length_bits_comp hu
  have hT : ComputableInPolyTime (fun w => cT * ((queryWord
      (J (_root_.Turing.MultiTapeTM.unframe w)) (_root_.Turing.MultiTapeTM.unframe w)
      (((_root_.Turing.MultiTapeTM.dropFrame w).take
        (J (_root_.Turing.MultiTapeTM.unframe w))).count true)
      ((_root_.Turing.MultiTapeTM.dropFrame w).drop (J (_root_.Turing.MultiTapeTM.unframe w) +
        V (_root_.Turing.MultiTapeTM.unframe w)))).length + 1) ^ dT) encBits encUnary := by
    fun_prop
  have htv := (computableInPolyTime_trueVars tm).comp
    (((ComputableInPolyTime.const ([] : List Bool)).prod hu).prod hT)
  have hidx : ComputableInPolyTime (Var.index (k := k) (State := State)) encVar encUnary :=
    ComputableInPolyTime.of_eq fun _ => rfl
  exact decide_mem (hidx.map.comp htv) hv

section PolyTime

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] {a J : List Bool → ℕ}

/-- The length of the query words is polynomial-time. -/
theorem computableInPolyTime_wordLength
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (wordLength a J) encBits encUnary := by
  unfold wordLength
  fun_prop

/-- The number of steps of the run on the query words is polynomial-time. -/
theorem computableInPolyTime_steps (cT dT : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (steps cT dT a J) encBits encUnary := by
  have := computableInPolyTime_wordLength ha hJ
  unfold steps
  fun_prop

/-- The width of variable numbers is polynomial-time. -/
theorem computableInPolyTime_width (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (width cT dT cI a J) encBits encUnary := by
  have := computableInPolyTime_wordLength ha hJ
  have := computableInPolyTime_steps cT dT ha hJ
  unfold width
  fun_prop

set_option linter.unusedDecidableInType false in
/-- The number of the output variable is polynomial-time. -/
theorem computableInPolyTime_outVar (k : ℕ) (State : Type) [Fintype State] [DecidableEq State]
    (cT dT : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (outVar (k := k) (State := State) cT dT a J) encBits encUnary := by
  have hs := computableInPolyTime_steps cT dT ha hJ
  have hh := computableInPolyTime_holds (k := k) (State := State)
  have h := hh.comp (hs.prod (ComputableInPolyTime.const (encIn := encBits)
    (Feature.out (k := k) (State := State) (.one true))))
  exact (ComputableInPolyTime.of_eq (encOut := encUnary) (f := fun v : Var k State => v.index)
    fun _ => rfl).comp h

/-- The prefixes of the copies of `G` in the check circuit are polynomial-time. -/
theorem computableInPolyTime_checkPrefixes (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (checkPrefixes cT dT cI a J) encBits (encList encBits) := by
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hr := ComputableInPolyTime.range.comp (unary_mul' hJ hW)
  unfold checkPrefixes
  refine mapWithInput (f := fun x p => unaryWord (J x) (p / width cT dT cI a J x) ++
    unaryWord (width cT dT cI a J x) (p % width cT dT cI a J x)) hr ?_
  have hJ' : ComputableInPolyTime (fun p : List Bool × ℕ => J p.1) (encPair encBits encUnary)
      encUnary := by fun_prop
  have hW' : ComputableInPolyTime (fun p : List Bool × ℕ => width cT dT cI a J p.1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hp : ComputableInPolyTime (fun p : List Bool × ℕ => p.2) (encPair encBits encUnary)
      encUnary := by fun_prop
  exact ComputableInPolyTime.bitsAppend
    (computableInPolyTime_unaryWord hJ' (unary_div' hp hW'))
    (computableInPolyTime_unaryWord hW' (unary_mod' hp hW'))

set_option linter.unusedDecidableInType false in
/-- The prefixes of the copies of `G` in the decoder are polynomial-time. -/
theorem computableInPolyTime_decoderPrefixes (k : ℕ) (State : Type) [Fintype State]
    [DecidableEq State] (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (decoderPrefixes (k := k) (State := State) cT dT cI a J) encBits
      (encList encBits) := by
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hv := computableInPolyTime_outVar k State cT dT ha hJ
  unfold decoderPrefixes
  refine mapWithInput (f := fun x j => unaryWord (J x) j ++
    unaryWord (width cT dT cI a J x) (outVar (k := k) (State := State) cT dT a J x))
    (ComputableInPolyTime.range.comp hJ) ?_
  have hJ' : ComputableInPolyTime (fun p : List Bool × ℕ => J p.1) (encPair encBits encUnary)
      encUnary := by fun_prop
  have hW' : ComputableInPolyTime (fun p : List Bool × ℕ => width cT dT cI a J p.1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hv' : ComputableInPolyTime (fun p : List Bool × ℕ =>
      outVar (k := k) (State := State) cT dT a J p.1) (encPair encBits encUnary) encUnary := by
    fun_prop
  have hp : ComputableInPolyTime (fun p : List Bool × ℕ => p.2) (encPair encBits encUnary)
      encUnary := by fun_prop
  exact ComputableInPolyTime.bitsAppend (computableInPolyTime_unaryWord hJ' hp)
    (computableInPolyTime_unaryWord hW' hv')

end PolyTime

section PolyTime

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {tm : MultiTapeTM k Bool State} {cT dT cI : ℕ} {a J : List Bool → ℕ}

/-- The clauses of copy `j`, with the run tableau relabelled in one step. -/
theorem blockClauses_eq (x : List Bool) (j : ℕ) :
    blockClauses tm cT dT cI a J x j =
      (runTableau tm [] (wordLength a J x) (steps cT dT a J x)).relabel
          (fun v => j * width cT dT cI a J x + Var.index v) ++
        (List.range (wordLength a J x)).flatMap (certClauses cT dT cI a J x j) := by
  simp only [blockClauses, tableauOf, CNF.relabel, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Clause.relabel, List.map_map, Prod.map_comp_map]
  rfl

/-- The input clauses of copy `j` are polynomial-time. -/
theorem computableInPolyTime_certClauses
    (hJ : ComputableInPolyTime J encBits encUnary) (hW : ComputableInPolyTime
      (width cT dT cI a J) encBits encUnary) :
    ComputableInPolyTime
      (fun q : (List Bool × ℕ) × ℕ => certClauses cT dT cI a J q.1.1 q.1.2 q.2)
      (encPair (encPair encBits encUnary) encUnary) encCNF := by
  have hx : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.1.1)
      (encPair (encPair encBits encUnary) encUnary) encBits := by fun_prop
  have hj : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.1.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hp : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => q.2)
      (encPair (encPair encBits encUnary) encUnary) encUnary := by fun_prop
  have hJ' : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => J q.1.1)
      (encPair (encPair encBits encUnary) encUnary) encUnary := hJ.comp hx
  have hW' : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ => width cT dT cI a J q.1.1)
      (encPair (encPair encBits encUnary) encUnary) encUnary := hW.comp hx
  have hlen := ComputableInPolyTime.length_bits_comp hx
  have hbound : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      2 * q.1.1.length + 1 + J q.1.1) (encPair (encPair encBits encUnary) encUnary)
      encUnary := by fun_prop
  have hvar : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      q.1.2 * width cT dT cI a J q.1.1 + Nat.pair 1 q.2)
      (encPair (encPair encBits encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (unary_add' (unary_mul' hj hW') (ComputableInPolyTime.unary_pair.comp
        ((ComputableInPolyTime.const 1).prod hp)))
  have hlive : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      J q.1.1 * width cT dT cI a J q.1.1 + (q.2 - (2 * q.1.1.length + 1 + J q.1.1)))
      (encPair (encPair encBits encUnary) encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (unary_add' (unary_mul' hJ' hW') (unary_sub' hp hbound))
  have hbit : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      (frame q.1.1 ++ unaryWord (J q.1.1) q.1.2).getD q.2 false)
      (encPair (encPair encBits encUnary) encUnary) encBool :=
    bitsGetDWithInput (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.frame.comp hx)
      (computableInPolyTime_unaryWord hJ' hj)) hp false
  have hc := unary_lt' hp hbound
  have hthen : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      [[(q.1.2 * width cT dT cI a J q.1.1 + Nat.pair 1 q.2,
        (frame q.1.1 ++ unaryWord (J q.1.1) q.1.2).getD q.2 false)]])
      (encPair (encPair encBits encUnary) encUnary) encCNF :=
    cons' (cons' (hvar.prod hbit) (const [])) (const [])
  have helse : ComputableInPolyTime (fun q : (List Bool × ℕ) × ℕ =>
      [[(q.1.2 * width cT dT cI a J q.1.1 + Nat.pair 1 q.2, true),
          (J q.1.1 * width cT dT cI a J q.1.1 + (q.2 - (2 * q.1.1.length + 1 + J q.1.1)), false)],
        [(q.1.2 * width cT dT cI a J q.1.1 + Nat.pair 1 q.2, false),
          (J q.1.1 * width cT dT cI a J q.1.1 + (q.2 - (2 * q.1.1.length + 1 + J q.1.1)), true)]])
      (encPair (encPair encBits encUnary) encUnary) encCNF :=
    cons' (cons' (hvar.prod (const true)) (cons' (hlive.prod (const false)) (const [])))
      (cons' (cons' (hvar.prod (const false)) (cons' (hlive.prod (const true)) (const [])))
        (const []))
  refine (ComputableInPolyTime.ite' hc hthen helse).of_enc_eq fun q => congrArg _ ?_
  simp only [certClauses, decide_eq_true_eq]

end PolyTime

section PolyTime

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] {a J : List Bool → ℕ}

/-- **The check formula is polynomial-time**: the run tableaux of the copies are renumbered into
their blocks by a renaming computed from the copy and the width. -/
theorem computableInPolyTime_checkFormula (tm : MultiTapeTM k Bool State) (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) :
    ComputableInPolyTime (checkFormula tm cT dT cI a J) encBits encCNF := by
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hL := computableInPolyTime_wordLength ha hJ
  have hS := computableInPolyTime_steps cT dT ha hJ
  have hL' : ComputableInPolyTime (fun p : List Bool × ℕ => wordLength a J p.1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hS' : ComputableInPolyTime (fun p : List Bool × ℕ => steps cT dT a J p.1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hW' : ComputableInPolyTime (fun p : List Bool × ℕ => width cT dT cI a J p.1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hblock : ComputableInPolyTime
      (fun p : List Bool × ℕ => blockClauses tm cT dT cI a J p.1 p.2)
      (encPair encBits encUnary) encCNF := by
    simp only [blockClauses_eq]
    have hq : ComputableInPolyTime (fun p : List Bool × ℕ =>
        (([] : List Bool), (wordLength a J p.1, steps cT dT a J p.1)))
        (encPair encBits encUnary) (encPair encBits (encPair encUnary encUnary)) :=
      (ComputableInPolyTime.const ([] : List Bool)).prod (hL'.prod hS')
    have hrt : ComputableInPolyTime (fun p : List Bool × ℕ =>
        runTableau tm [] (wordLength a J p.1) (steps cT dT a J p.1))
        (encPair encBits encUnary) (encCNFOver encVar) :=
      ComputableInPolyTime.comp (g := fun p : List Bool × ℕ =>
        (([] : List Bool), (wordLength a J p.1, steps cT dT a J p.1)))
        (f := fun q : List Bool × ℕ × ℕ => runTableau tm q.1 q.2.1 q.2.2)
        (computableInPolyTime_runTableau tm) hq
    have hidx : ComputableInPolyTime (Var.index (k := k) (State := State)) encVar encUnary :=
      ComputableInPolyTime.of_eq fun _ => rfl
    have hj : ComputableInPolyTime
        (fun q : (List Bool × ℕ) × Var k State => q.1.2)
        (encPair (encPair encBits encUnary) encVar) encUnary := by fun_prop
    have hW'' : ComputableInPolyTime
        (fun q : (List Bool × ℕ) × Var k State => width cT dT cI a J q.1.1)
        (encPair (encPair encBits encUnary) encVar) encUnary := by fun_prop
    have hf : ComputableInPolyTime
        (fun q : (List Bool × ℕ) × Var k State =>
          q.1.2 * width cT dT cI a J q.1.1 + Var.index q.2)
        (encPair (encPair encBits encUnary) encVar) encNat :=
      ComputableInPolyTime.unary_to_binary.comp
        (unary_add' (unary_mul' hj hW'') (hidx.comp (ComputableInPolyTime.snd _ _)))
    refine ComputableInPolyTime.listAppend'
      (CNF.computableInPolyTime_relabelWithInput
        (f := fun (p : List Bool × ℕ) (v : Var k State) =>
          p.2 * width cT dT cI a J p.1 + Var.index v) hrt hf) ?_
    exact flatMapWithInput (f := fun (p : List Bool × ℕ) (c : ℕ) =>
      certClauses cT dT cI a J p.1 p.2 c) (ComputableInPolyTime.range.comp hL')
      (computableInPolyTime_certClauses hJ hW)
  exact flatMapWithInput (f := fun (x : List Bool) (j : ℕ) => blockClauses tm cT dT cI a J x j)
    (ComputableInPolyTime.range.comp hJ) hblock

/-- **The circuit `G` decoded from the guessed word has a polynomial-time code.** -/
theorem computableInPolyTime_guessed_code (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) (dG : ℕ) :
    ComputableInPolyTime (fun p : List Bool × List Bool =>
      (guessed cT dT cI a J dG p.1 p.2).code)
      (encPair encBits encBits) (Circuit.encCode Unbounded.encExtOp) := by
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hr : ComputableInPolyTime (fun p : List Bool × List Bool =>
      J p.1 + width cT dT cI a J p.1 + a p.1) (encPair encBits encBits) encUnary := by
    fun_prop
  have he : ComputableInPolyTime (fun p : List Bool × List Bool => p.2)
      (encPair encBits encBits) encBits := by fun_prop
  have hopt := computableInPolyTime_decodeExtWitness hr he dG
  have hfallback : ComputableInPolyTime (fun p : List Bool × List Bool =>
      ([(Unbounded.ExtOp.ac (.or 0), ([] : List ℕ))],
        [J p.1 + width cT dT cI a J p.1 + a p.1]))
      (encPair encBits encBits) (Circuit.encCode Unbounded.encExtOp) :=
    (ComputableInPolyTime.const [(Unbounded.ExtOp.ac (.or 0), ([] : List ℕ))]).prod
      ((ComputableInPolyTime.unary_to_binary.comp hr).cons' (ComputableInPolyTime.const []))
  have hbody : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (Σ n, Circuit Unbounded.extSignature n 1) =>
        s.2.2.code)
      (encPair (encPair encBits encBits) (Unbounded.encExtCircuit 1))
      (Circuit.encCode Unbounded.encExtOp) :=
    (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).snd'.comp (ComputableInPolyTime.snd _ _)
  have h := ComputableInPolyTime.optionElimWithInput
    (value := fun p : List Bool × List Bool =>
      (decodeExtWitness dG (J p.1 + width cT dT cI a J p.1 + a p.1) p.2).map
        fun W => (⟨J p.1 + width cT dT cI a J p.1 + a p.1, W⟩ :
          Σ n, Circuit Unbounded.extSignature n 1))
    (fallback := fun p : List Bool × List Bool =>
      ([(Unbounded.ExtOp.ac (.or 0), ([] : List ℕ))],
        [J p.1 + width cT dT cI a J p.1 + a p.1]))
    (body := fun _ c => c.2.code) hopt hfallback hbody
  refine h.of_enc_eq fun p => congrArg _ ?_
  unfold guessed
  cases hd : decodeExtWitness dG (J p.1 + width cT dT cI a J p.1 + a p.1) p.2 with
  | none => rfl
  | some W => simp

end PolyTime

section PolyTime

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] {a J : List Bool → ℕ}

/-- **The code of the check circuit is polynomial-time** from `x` and the guessed word `e`. -/
theorem computableInPolyTime_checkCircuit_code (tm : MultiTapeTM k Bool State) (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) (dG : ℕ) :
    ComputableInPolyTime (fun p : List Bool × List Bool =>
      (checkCircuit tm cT dT cI a J dG p.1 p.2).code)
      (encPair encBits encBits) (Circuit.encCode Unbounded.encExtOp) := by
  simp only [code_checkCircuit]
  have hW := computableInPolyTime_width cT dT cI ha hJ
  have hx : ComputableInPolyTime (fun p : List Bool × List Bool => p.1)
      (encPair encBits encBits) encBits := by fun_prop
  have ha' : ComputableInPolyTime (fun p : List Bool × List Bool => a p.1)
      (encPair encBits encBits) encUnary := by fun_prop
  have hn : ComputableInPolyTime (fun p : List Bool × List Bool =>
      J p.1 * width cT dT cI a J p.1 + a p.1) (encPair encBits encBits) encNat := by
    have : ComputableInPolyTime (fun p : List Bool × List Bool =>
        J p.1 * width cT dT cI a J p.1 + a p.1) (encPair encBits encBits) encUnary := by
      fun_prop
    exact ComputableInPolyTime.unary_to_binary.comp this
  have hΦ : ComputableInPolyTime (fun p : List Bool × List Bool =>
      checkFormula tm cT dT cI a J p.1) (encPair encBits encBits) encCNF :=
    (computableInPolyTime_checkFormula tm cT dT cI ha hJ).comp hx
  have hprefix : ComputableInPolyTime (fun p : List Bool × List Bool =>
      checkPrefixes cT dT cI a J p.1) (encPair encBits encBits) (encList encBits) :=
    (computableInPolyTime_checkPrefixes cT dT cI ha hJ).comp hx
  exact Circuit.computableInPolyTime_compCode
    (ComputableInPolyTime.unary_to_binary.comp ha')
    (Unbounded.computableInPolyTime_cnfCheckCode hn hΦ)
    (Unbounded.computableInPolyTime_withInputsCode ha'
      (Unbounded.computableInPolyTime_evalTableCode ha'
        (computableInPolyTime_guessed_code cT dT cI ha hJ dG) hprefix))

set_option linter.unusedDecidableInType false in
/-- **The code of the decoder is polynomial-time** from `x` and the guessed word `e`, when the
output variable is within the width. -/
theorem computableInPolyTime_decoderCircuit_code (k : ℕ) (State : Type) [Fintype State]
    [DecidableEq State] (cT dT cI : ℕ)
    (ha : ComputableInPolyTime a encBits encUnary)
    (hJ : ComputableInPolyTime J encBits encUnary) (dG : ℕ)
    (hv : ∀ x, outVar (k := k) (State := State) cT dT a J x ≤ width cT dT cI a J x) :
    ComputableInPolyTime (fun p : List Bool × List Bool =>
      (decoderCircuit (k := k) (State := State) cT dT cI a J dG p.1 p.2).code)
      (encPair encBits encBits) (Circuit.encCode Unbounded.encExtOp) := by
  simp only [fun p : List Bool × List Bool => code_decoderCircuit (k := k) (State := State)
    (cT := cT) (dT := dT) (cI := cI) (a := a) (J := J) dG p.1 p.2 (hv p.1)]
  have hx : ComputableInPolyTime (fun p : List Bool × List Bool => p.1)
      (encPair encBits encBits) encBits := by fun_prop
  have ha' : ComputableInPolyTime (fun p : List Bool × List Bool => a p.1)
      (encPair encBits encBits) encUnary := by fun_prop
  have hprefix : ComputableInPolyTime (fun p : List Bool × List Bool =>
      decoderPrefixes (k := k) (State := State) cT dT cI a J p.1)
      (encPair encBits encBits) (encList encBits) :=
    (computableInPolyTime_decoderPrefixes k State cT dT cI ha hJ).comp hx
  exact Unbounded.computableInPolyTime_evalTableCode ha'
    (computableInPolyTime_guessed_code cT dT cI ha hJ dG) hprefix

end PolyTime

end Compression

end Cslib.Circuits.Boolean.SymAnd
