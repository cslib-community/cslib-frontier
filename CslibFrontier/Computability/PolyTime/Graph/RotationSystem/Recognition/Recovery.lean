/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Query
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryInvariants
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Native bounded candidate recovery

All raw labels are binary. Unary iteration counts come only from actual endpoint fibers and
vertex lists. Split queries are temporary; loop states contain orders and one candidate block,
never systems or query history. Successful candidates use the existing certificate checker.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM
open scoped RotationCertificate

/-- Framed fixed/free input followed by the binary current vertex. -/
abbrev encWordInput := encPair encFixedRotationInput encNat

/-- Framed input/vertex pair followed by a framed binary dart block. -/
abbrev encBlockInput := encPair encWordInput (encList encNat)

/-- Framed input/vertex pair followed by an optional framed binary dart block. -/
abbrev encAdvanceInput := encPair encWordInput (encOption (encList encNat))

private theorem redirectEnd_polyTime : ComputableInPolyTime
    (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => redirectEnd p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encNat (encList encNat)) (encPair encNat encNat)) encNat := by
  unfold redirectEnd
  fun_prop

private theorem redirectEnd_polyTime' {α : Type} {enc : α ↪ List Bool}
    {n i v : α → ℕ} {block : α → List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hb : ComputableInPolyTime block enc (encList encNat))
    (hi : ComputableInPolyTime i enc encNat)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => redirectEnd (n x) (block x) (i x) (v x)) enc encNat := by
  simpa only [Function.comp_def] using redirectEnd_polyTime.comp ((hn.prod hb).prod (hi.prod hv))

attribute [local fun_prop] redirectEnd_polyTime'

/-- The split is a native list construction even on malformed raw labels and blocks. -/
theorem split_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => split p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  unfold split encBlockInput encWordInput
  refine encFixedRotationInput_mk_polyTime (encGraph_mk_polyTime (by fun_prop) ?_) ?_
  · apply ComputableInPolyTime.listAppend'
    · apply ComputableInPolyTime.mapWithInput (by fun_prop)
      have hi : ComputableInPolyTime
          (fun p : ((FixedRotationInput × ℕ) × List ℕ) × ((ℕ × ℕ) × ℕ) => 2 * p.2.2)
          (encPair (encPair (encPair encFixedRotationInput encNat) (encList encNat))
            (encPair (encPair encNat encNat) encUnary)) encNat :=
        ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
      exact (redirectEnd_polyTime' (by fun_prop) (by fun_prop) hi (by fun_prop)).prod
        (redirectEnd_polyTime' (by fun_prop) (by fun_prop)
          (ComputableInPolyTime.binary_add' hi (ComputableInPolyTime.const 1)) (by fun_prop))
    · fun_prop
  · have hm : ComputableInPolyTime
        (fun p : (FixedRotationInput × ℕ) × List ℕ => 2 * p.1.1.graph.edges.length)
        (encPair (encPair encFixedRotationInput encNat) (encList encNat)) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    fun_prop

private theorem split_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {v : α → ℕ} {block : α → List ℕ}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hv : ComputableInPolyTime v enc encNat)
    (hb : ComputableInPolyTime block enc (encList encNat)) :
    ComputableInPolyTime (fun x => split (I x) (v x) (block x)) enc encFixedRotationInput := by
  simpa only [Function.comp_def] using split_polyTime.comp ((hI.prod hv).prod hb)

/-- Only actual unused fiber darts are scanned as candidates. -/
theorem remaining_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => remaining p.1.1 p.1.2 p.2)
    encBlockInput (encList encNat) := by
  unfold remaining encBlockInput encWordInput
  fun_prop

private theorem remaining_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {v : α → ℕ} {block : α → List ℕ}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hv : ComputableInPolyTime v enc encNat)
    (hb : ComputableInPolyTime block enc (encList encNat)) :
    ComputableInPolyTime (fun x => remaining (I x) (v x) (block x)) enc (encList encNat) := by
  simpa only [Function.comp_def] using remaining_polyTime.comp ((hI.prod hv).prod hb)

attribute [local fun_prop] split_polyTime' remaining_polyTime'

/-- First-candidate search actually calls the concrete native XOR query on each ephemeral split. -/
theorem nextCandidate_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => nextCandidate p.1.1 p.1.2 p.2)
    encBlockInput (encOption encNat) := by
  unfold nextCandidate
  apply ComputableInPolyTime.findWithInput remaining_polyTime
  unfold encBlockInput encWordInput
  fun_prop

private theorem nextCandidate_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {v : α → ℕ} {block : α → List ℕ}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hv : ComputableInPolyTime v enc encNat)
    (hb : ComputableInPolyTime block enc (encList encNat)) :
    ComputableInPolyTime (fun x => nextCandidate (I x) (v x) (block x)) enc (encOption encNat) := by
  simpa only [Function.comp_def] using nextCandidate_polyTime.comp ((hI.prod hv).prod hb)

attribute [local fun_prop] nextCandidate_polyTime'

private theorem optionGuardStep_polyTime {α β δ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (encD : δ ↪ List Bool)
    {opt : α → Option β} {guard : α → β → Bool}
    {step : α → β → Option δ} {extend : α → β → δ → β}
    (hopt : ComputableInPolyTime opt encA (encOption encB))
    (hg : ComputableInPolyTime (fun p : α × β => guard p.1 p.2) (encPair encA encB) encBool)
    (hs : ComputableInPolyTime (fun p : α × β => step p.1 p.2)
      (encPair encA encB) (encOption encD))
    (he : ComputableInPolyTime (fun q : (α × β) × δ => extend q.1.1 q.1.2 q.2)
      (encPair (encPair encA encB) encD) encB) :
    ComputableInPolyTime
      (fun a => (opt a).elim none fun b =>
        if guard a b then some b else (step a b).elim none fun d => some (extend a b d))
      encA (encOption encB) :=
  ComputableInPolyTime.optionElimWithInput hopt (ComputableInPolyTime.const none)
    (ComputableInPolyTime.ite' (encC := encBool) hg
      ((ComputableInPolyTime.optionSome encB).comp (ComputableInPolyTime.snd encA encB))
      (ComputableInPolyTime.optionElimWithInput hs (ComputableInPolyTime.const none)
        ((ComputableInPolyTime.optionSome encB).comp he)))

/-- A block step has native time independent of query feasibility or input validity. -/
theorem advance_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × Option (List ℕ) => advance p.1.1 p.1.2 p.2)
    encAdvanceInput (encOption (encList encNat)) := by
  unfold advance encAdvanceInput encWordInput
  apply optionGuardStep_polyTime encNat <;> fun_prop

/-- Bounded word recovery is native polynomial-time on all raw input/vertex pairs. The loop
stores only one optional block and adds at most one bounded dart per iteration. -/
theorem recoverWord_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × ℕ => recoverWord p.1 p.2)
    encWordInput (encOption (encList encNat)) := by
  have hf : ComputableInPolyTime
      (fun p : FixedRotationInput × ℕ => fiber p.1.graph p.2) encWordInput (encList encNat) := by
    unfold encWordInput; fun_prop
  have hm : ComputableInPolyTime
      (fun p : FixedRotationInput × ℕ => p.1.graph.edges.length) encWordInput encUnary := by
    unfold encWordInput; fun_prop
  unfold recoverWord
  apply ComputableInPolyTime.iterateWith_of_bounded_growth
    (par := fun p : FixedRotationInput × ℕ => p)
    (step := fun p state => advance p.1 p.2 state)
    ComputableInPolyTime.id'
    (by fun_prop)
    ((ComputableInPolyTime.optionSome (encList encNat)).comp
      (ComputableInPolyTime.ite' (encC := encBool) (by fun_prop) (ComputableInPolyTime.const [])
        (ComputableInPolyTime.cons' ((ComputableInPolyTime.headD 0).comp hf)
          (ComputableInPolyTime.const []))))
    advance_polyTime
    (((PolyBounded.const 4).mul hm.polyBounded).add (.const 1))
  intro p state
  exact (length_enc_advance p.1 p.2 state).trans (by omega)

private theorem recoverWord_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {v : α → ℕ}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => recoverWord (I x) (v x)) enc (encOption (encList encNat)) := by
  simpa only [Function.comp_def] using recoverWord_polyTime.comp (hI.prod hv)

/-- Replacement of a complete order is native; supplied vertex labels stay binary. -/
theorem prescribe_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => prescribe p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  unfold prescribe encBlockInput encWordInput
  apply encFixedRotationInput_mk_polyTime (by fun_prop)
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop)) (by fun_prop))
    (by fun_prop) (by fun_prop)

private theorem prescribe_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {v : α → ℕ} {block : α → List ℕ}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hv : ComputableInPolyTime v enc encNat)
    (hb : ComputableInPolyTime block enc (encList encNat)) :
    ComputableInPolyTime (fun x => prescribe (I x) (v x) (block x)) enc encFixedRotationInput := by
  simpa only [Function.comp_def] using prescribe_polyTime.comp ((hI.prod hv).prod hb)

attribute [local fun_prop] recoverWord_polyTime' prescribe_polyTime'

/-- A complete-vertex step uses only the current optional state and a binary vertex. -/
theorem completeVertex_polyTime : ComputableInPolyTime
    (fun p : Option FixedRotationInput × ℕ => completeVertex p.1 p.2)
    (encPair (encOption encFixedRotationInput) encNat) (encOption encFixedRotationInput) := by
  unfold completeVertex
  apply optionGuardStep_polyTime (encList encNat) <;> fun_prop

/-- Native outer recovery stores only original-graph orders. The prefix bound is proved from
the actual implementation, with no resource-provider premise. -/
theorem recoverOrders_polyTime : ComputableInPolyTime recoverOrders
    encFixedRotationInput (encOption encFixedRotationInput) := by
  have hn : ComputableInPolyTime (fun I : FixedRotationInput => I.graph.vertices.length)
      encFixedRotationInput encUnary := by fun_prop
  have hm : ComputableInPolyTime (fun I : FixedRotationInput => I.graph.edges.length)
      encFixedRotationInput encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun I : FixedRotationInput => I.orders.length)
      encFixedRotationInput encUnary := by fun_prop
  have hb : PolyBounded (fun I => (encFixedRotationInput I).length)
      (fun I => (encFixedRotationInput I).length + 1 +
        I.graph.vertices.length * outerGrowth I) := by
    unfold outerGrowth
    exact (PolyBounded.self.add (.const 1)).add
      (hn.polyBounded.mul (hw.polyBounded.mul ((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hm.polyBounded).mul
          (((PolyBounded.const 4).mul hm.polyBounded).add (.const 1))).add (.const 1)))))
  unfold recoverOrders
  apply ComputableInPolyTime.foldl' (by fun_prop)
    (ComputableInPolyTime.optionSome encFixedRotationInput) completeVertex_polyTime hb
  intro I i hi
  rcases completeVertex_fold I ((List.range I.graph.vertices.length).take i) with
    hn | ⟨J, hj, _, _, hb⟩
  · rw [hn, encOption_none, List.length_nil]
    exact Nat.zero_le _
  · rw [hj, encOption_some, List.length_cons]
    have hlen : ((List.range I.graph.vertices.length).take i).length ≤
        I.graph.vertices.length := by simp
    exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (outerGrowth I) hlen) _)

/-- Native cyclic successor lookup, with unary word position and binary word entries. -/
theorem nextInWord_polyTime : ComputableInPolyTime
    (fun p : List ℕ × ℕ => nextInWord p.1 p.2)
    (encPair (encList encNat) encUnary) encNat := by
  unfold nextInWord
  fun_prop

private theorem nextInWord_polyTime' {α : Type} {enc : α ↪ List Bool}
    {word : α → List ℕ} {i : α → ℕ}
    (hw : ComputableInPolyTime word enc (encList encNat))
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => nextInWord (word x) (i x)) enc encNat := by
  simpa only [Function.comp_def] using nextInWord_polyTime.comp (hw.prod hi)

attribute [local fun_prop] nextInWord_polyTime'

/-- Assemble one binary successor per original dart using saturating binary endpoint lookup. -/
theorem certificate_polyTime : ComputableInPolyTime certificate
    encFixedRotationInput encRotationCertificate := by
  unfold certificate
  apply encRotationCertificate_mk_polyTime
  apply ComputableInPolyTime.mapWithInput (encA := encNat) (by fun_prop)
  exact nextInWord_polyTime' (by fun_prop)
    (ComputableInPolyTime.idxOfWithInput (by fun_prop) (by fun_prop))

/-- Framed fixed/free input followed by an existing binary successor certificate. -/
abbrev encFixedCertificate := encPair encFixedRotationInput encRotationCertificate

/-- The supplied complete-word guard is native on all raw words and successor tables. -/
theorem verifyFixed_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × RotationCertificate => verifyFixed p.1 p.2)
    encFixedCertificate encBool := by
  unfold verifyFixed encFixedCertificate
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.optionElimWithInput (by fun_prop) (ComputableInPolyTime.const true)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  fun_prop

private theorem verifyFixed_polyTime' {α : Type} {enc : α ↪ List Bool}
    {I : α → FixedRotationInput} {c : α → RotationCertificate}
    (hI : ComputableInPolyTime I enc encFixedRotationInput)
    (hc : ComputableInPolyTime c enc encRotationCertificate) :
    ComputableInPolyTime (fun x => verifyFixed (I x) (c x)) enc encBool := by
  simpa only [Function.comp_def] using verifyFixed_polyTime.comp (hI.prod hc)

attribute [local fun_prop] verifyFixed_polyTime'

/-- The complete concrete candidate driver has native polynomial time on every raw input.
Its sound guard uses the existing numerical checker; completeness remains separate. -/
theorem recover_polyTime : ComputableInPolyTime recover encFixedRotationInput
    (encOption encRotationCertificate) := by
  unfold recover
  apply ComputableInPolyTime.ite' (encC := encBool) query_polyTime _
    (ComputableInPolyTime.const none)
  apply ComputableInPolyTime.optionElimWithInput recoverOrders_polyTime
    (ComputableInPolyTime.const none)
  have hc : ComputableInPolyTime
      (fun p : FixedRotationInput × FixedRotationInput => certificate p.2)
      (encPair encFixedRotationInput encFixedRotationInput) encRotationCertificate :=
    certificate_polyTime.comp (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.ite' (encC := encBool) (by fun_prop)
    ((ComputableInPolyTime.optionSome encRotationCertificate).comp hc)
    (ComputableInPolyTime.const none)

private theorem numVars_binary_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun F : Cslib.Logic.PL.CSP Rel V => F.numVars)
      (encCSP encRel encV) encNat := by
  have hu := (Cslib.Logic.PL.CNF.computableInPolyTime_numVars encV).comp
    (CSP.computableInPolyTime_varCNF encRel encV)
  simpa only [Function.comp_def, Cslib.Logic.PL.CSP.numVars_varCNF] using
    ComputableInPolyTime.unary_to_binary.comp hu

/-- Fixing the full orders after a free vertex prefix scans the listed graph only. Its raw
binary cutoff is compared with labels, never converted into a unary scan bound. -/
theorem freePrefix_polyTime : ComputableInPolyTime
    (fun p : Graph × ℕ => freePrefix p.1 p.2)
    (encPair encGraph encNat) encFixedRotationInput := by
  unfold freePrefix
  apply encFixedRotationInput_mk_polyTime (by fun_prop)
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.binary_lt' (by fun_prop) (by fun_prop))
    (ComputableInPolyTime.const none) (by fun_prop)

private theorem freePrefix_polyTime' {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {k : α → ℕ}
    (hG : ComputableInPolyTime G enc encGraph)
    (hk : ComputableInPolyTime k enc encNat) :
    ComputableInPolyTime (fun x => freePrefix (G x) (k x)) enc encFixedRotationInput := by
  simpa only [Function.comp_def] using freePrefix_polyTime.comp (hG.prod hk)

/-- Original CSP scopes compile through the existing dense incidence graph. Binary source
names are compared as bit strings; relation semantics and declared arity fund no scans. -/
theorem ofCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (ofCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) encFixedRotationInput := by
  exact freePrefix_polyTime' (CSP.computableInPolyTime_incidenceGraph encRel encV)
    (numVars_binary_polyTime encRel encV)

/-- Bare original CSP recovery is a native polynomial-time program using the concrete XOR
solver and the existing original-position certificate checker, on every raw encoded CSP. -/
theorem recoverCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (recoverCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) (encOption encRotationCertificate) := by
  have hc := CSP.computableInPolyTime_verifyRotationCertificate encRel encV
  unfold recoverCSP
  apply ComputableInPolyTime.optionElimWithInput
    (recover_polyTime.comp (ofCSP_polyTime encRel encV)) (ComputableInPolyTime.const none)
  exact ComputableInPolyTime.ite' (encC := encBool) hc (by fun_prop)
    (ComputableInPolyTime.const none)

end Cslib.Complexity.Graph.RotationRecognition
