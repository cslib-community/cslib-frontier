/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Source
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time circuit instruction emission

Offsets and loop counts use unary encodings; fragment tags use a fixed finite enumeration.
Clause scans and the remaining circuit assembly are indexed list operations.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.encProgram`: instruction lists with unary offsets.
* `Cslib.Complexity.NCL.QBF.Emit.source`: instructions for a normalized source instance.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.computableInPolyTime_source`: instruction emission is
  polynomial-time in the upstream source encoding.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open _root_.Turing.MultiTapeTM

/-- A list of Boolean clause masks, with both list levels framed by the standard encoding. -/
abbrev encMasks := encList (encList encBool)

/-- Encode a fixed fragment tag by its enumeration rank. -/
@[expose] def encOpcode : Opcode ↪ List Bool := encFinEnum Opcode

/-- Encode instruction lists using unary offsets and fixed fragment tags. -/
@[expose] def encProgram : Program ↪ List Bool := encList (encPair encUnary encOpcode)

/-- Emit instructions for the normalized source's quantifiers and literal masks. -/
@[expose]
def source (x : PrenexCNF) : Program := circuit (Source.prepare x).1 (Source.prepare x).2

/-- Emitting one literal position is polynomial-time in its offset and two Boolean flags. -/
@[fun_prop]
theorem computableInPolyTime_collect {α : Type} {input : α ↪ List Bool}
    {k : α → ℕ} {seen bit : α → Bool}
    (hk : ComputableInPolyTime k input encUnary)
    (hs : ComputableInPolyTime seen input encBool)
    (hb : ComputableInPolyTime bit input encBool) :
    ComputableInPolyTime (fun x => collect (k x) (seen x) (bit x)) input encProgram := by
  unfold collect encProgram
  fun_prop

private abbrev encScan :=
  encPair encUnary (encPair encUnary (encPair (encList encBool) encBool))

private theorem computableInPolyTime_seen {α : Type} {input : α ↪ List Bool}
    {m : α → List Bool} {i : α → ℕ} {seen : α → Bool}
    (hm : ComputableInPolyTime m input (encList encBool))
    (hi : ComputableInPolyTime i input encUnary)
    (hs : ComputableInPolyTime seen input encBool) :
    ComputableInPolyTime (fun x => seen x || ((m x).take (i x)).any id) input encBool := by
  have ht : ComputableInPolyTime (fun x => (m x).take (i x)) input (encList encBool) :=
    ComputableInPolyTime.listTakeWithInput hm hi
  exact hs.bool_or' (ComputableInPolyTime.anyWithInput ht (ComputableInPolyTime.snd _ encBool))

private theorem computableInPolyTime_scanData :
    ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => scan p.1 p.2.1 p.2.2.1 p.2.2.2)
      encScan encProgram := by
  have hk : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => p.1)
      encScan encUnary := by unfold encScan; fun_prop
  have hn : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => p.2.1)
      encScan encUnary := by unfold encScan; fun_prop
  have hm : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => p.2.2.1)
      encScan (encList encBool) := by unfold encScan; fun_prop
  have hs : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => p.2.2.2)
      encScan encBool := by unfold encScan; fun_prop
  have hp := ComputableInPolyTime.fst encScan encUnary
  have hi := ComputableInPolyTime.snd encScan encUnary
  have ha : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List Bool × Bool) × ℕ => p.1.1 + p.2)
      (encPair encScan encUnary) encUnary := by unfold encScan; fun_prop
  have hb := ComputableInPolyTime.listGetDWithInput (hm.comp hp) hi false
  have hc := computableInPolyTime_collect ha
    (computableInPolyTime_seen (hm.comp hp) hi (hs.comp hp)) hb
  have hr : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool => List.range p.2.1)
      encScan (encList encUnary) := by fun_prop
  have hf := ComputableInPolyTime.flatMapWithInput
    (encB := encPair encUnary encOpcode)
    (f := fun p i => collect (p.1 + i) (p.2.2.2 || (p.2.2.1.take i).any id)
      (p.2.2.1.getD i false)) hr hc
  have he := computableInPolyTime_seen hm hn hs
  have hl : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool × Bool =>
      [(p.1 + p.2.1, Opcode.fixed)]) encScan encProgram := by
    unfold encProgram encScan
    fun_prop
  exact hf.listAppend' (he.ite (ComputableInPolyTime.const []) hl)

/-- The indexed sweep is polynomial-time in the bundle width, offset and literal mask. -/
@[fun_prop]
theorem computableInPolyTime_scan {α : Type} {input : α ↪ List Bool}
    {k n : α → ℕ} {m : α → List Bool} {seen : α → Bool}
    (hk : ComputableInPolyTime k input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input (encList encBool))
    (hs : ComputableInPolyTime seen input encBool) :
    ComputableInPolyTime (fun x => scan (k x) (n x) (m x) (seen x)) input encProgram :=
  computableInPolyTime_scanData.comp (hk.prod (hn.prod (hm.prod hs)))

private abbrev encNetwork : (ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encUnary encMasks)

private theorem computableInPolyTime_conjoinRow :
    ComputableInPolyTime (fun p : (ℕ × ℕ × List (List Bool)) × List Bool =>
      scan p.1.1 p.1.2.1 p.2 false ++ [(p.1.1 + p.1.2.1, Opcode.conj)])
      (encPair encNetwork (encList encBool)) encProgram := by
  have hc : ComputableInPolyTime (fun p : (ℕ × ℕ × List (List Bool)) × List Bool =>
      scan p.1.1 p.1.2.1 p.2 false) (encPair encNetwork (encList encBool)) encProgram := by
    apply computableInPolyTime_scan
    all_goals unfold encNetwork; fun_prop
  have hj : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List (List Bool)) × List Bool => [(p.1.1 + p.1.2.1, Opcode.conj)])
      (encPair encNetwork (encList encBool)) encProgram := by
    unfold encNetwork encProgram
    fun_prop
  exact hc.listAppend' hj

private theorem computableInPolyTime_conjoinData :
    ComputableInPolyTime (fun p : ℕ × ℕ × List (List Bool) => conjoin p.1 p.2.1 p.2.2)
      encNetwork encProgram := by
  have hl : ComputableInPolyTime (fun p : ℕ × ℕ × List (List Bool) => p.2.2)
      encNetwork encMasks := by unfold encNetwork; fun_prop
  unfold conjoin encProgram
  exact ComputableInPolyTime.flatMapWithInput hl computableInPolyTime_conjoinRow

/-- Assemble clause rows from polynomial-time offsets, widths and mask matrices. -/
@[fun_prop]
theorem computableInPolyTime_conjoin {α : Type} {input : α ↪ List Bool}
    {k n : α → ℕ} {ms : α → List (List Bool)}
    (hk : ComputableInPolyTime k input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime ms input encMasks) :
    ComputableInPolyTime (fun x => conjoin (k x) (n x) (ms x)) input encProgram := by
  change ComputableInPolyTime
    ((fun p : ℕ × ℕ × List (List Bool) => conjoin p.1 p.2.1 p.2.2) ∘
      (fun x => (k x, n x, ms x))) input encProgram
  have hp : ComputableInPolyTime (fun x => (k x, n x, ms x)) input encNetwork := by
    unfold encNetwork
    exact hk.prod (hn.prod hm)
  exact computableInPolyTime_conjoinData.comp hp

private theorem computableInPolyTime_networkData :
    ComputableInPolyTime (fun p : ℕ × ℕ × List (List Bool) => network p.1 p.2.1 p.2.2)
      encNetwork encProgram := by
  have heq (k n : ℕ) (ms : List (List Bool)) : network k n ms =
      if ms.isEmpty then [(k + n, Opcode.start)] else
        scan k n (ms.headD []) false ++ conjoin k n ms.tail := by
    cases ms <;> rfl
  simp only [heq]
  unfold encNetwork encProgram
  fun_prop

/-- Emit a network from polynomial-time offsets, widths and mask matrices. -/
@[fun_prop]
theorem computableInPolyTime_network {α : Type} {input : α ↪ List Bool}
    {k n : α → ℕ} {ms : α → List (List Bool)}
    (hk : ComputableInPolyTime k input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime ms input encMasks) :
    ComputableInPolyTime (fun x => network (k x) (n x) (ms x)) input encProgram :=
  computableInPolyTime_networkData.comp (hk.prod (hn.prod hm))

/-- Quantifier tags and offsets are emitted in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_chain :
    ComputableInPolyTime (fun p : ℕ × List Quantifier => chain p.1 p.2)
      (encPair encUnary (encList Source.encQuantifier)) encProgram := by
  have htag : ComputableInPolyTime (fun q : Quantifier =>
      match q with | .ex => Opcode.ex | .all => Opcode.all)
      Source.encQuantifier encOpcode := by
    let _ : Finite Quantifier := Finite.of_injective
      (fun q : Quantifier => match q with | .ex => false | .all => true)
      (by intro a b h; cases a <;> cases b <;> simp_all)
    exact ComputableInPolyTime.of_finite _
  have hc :=
    ((ComputableInPolyTime.fst (encPair encUnary (encList Source.encQuantifier))
      Source.encQuantifier).fst').prod
      (htag.comp (ComputableInPolyTime.snd
        (encPair encUnary (encList Source.encQuantifier)) Source.encQuantifier))
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.snd _ _) hc

private theorem computableInPolyTime_terminalData :
    ComputableInPolyTime (fun p : ℕ × ℕ × List (List Bool) => terminal p.1 p.2.1 p.2.2)
      encNetwork encProgram := by
  unfold terminal encNetwork encProgram
  fun_prop

/-- Emit a terminal from polynomial-time offsets, widths and mask matrices. -/
@[fun_prop]
theorem computableInPolyTime_terminal {α : Type} {input : α ↪ List Bool}
    {k p : α → ℕ} {ms : α → List (List Bool)}
    (hk : ComputableInPolyTime k input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hm : ComputableInPolyTime ms input encMasks) :
    ComputableInPolyTime (fun x => terminal (k x) (p x) (ms x)) input encProgram :=
  computableInPolyTime_terminalData.comp (hk.prod (hp.prod hm))

/-- Emit all instructions of a prepared circuit in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_circuit :
    ComputableInPolyTime (fun p : List Quantifier × List (List Bool) => circuit p.1 p.2)
      Source.encPrepared encProgram := by
  have hq : ComputableInPolyTime (fun p : List Quantifier × List (List Bool) => p.1)
      Source.encPrepared (encList Source.encQuantifier) := by unfold Source.encPrepared; fun_prop
  have hc := computableInPolyTime_chain.comp ((ComputableInPolyTime.const 0).prod hq)
  have ht : ComputableInPolyTime (fun p : List Quantifier × List (List Bool) =>
      terminal 0 p.1.length p.2) Source.encPrepared encProgram := by
    apply computableInPolyTime_terminal (ComputableInPolyTime.const 0)
    · exact (ComputableInPolyTime.length_list Source.encQuantifier).comp hq
    · unfold Source.encPrepared
      fun_prop
  exact ((ComputableInPolyTime.const [(0, Opcode.output)]).listAppend' hc).listAppend' ht

/-- The complete instruction emitter is polynomial-time in upstream binary source data. -/
@[fun_prop]
theorem computableInPolyTime_source :
    ComputableInPolyTime source encPrenexCNF encProgram :=
  computableInPolyTime_circuit.comp Source.computableInPolyTime_prepare

end Cslib.Complexity.NCL.QBF.Emit
