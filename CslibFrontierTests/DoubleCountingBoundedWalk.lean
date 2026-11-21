/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk.Runtime

/-! # Bounded walk on the original input

The supplied edge routine reads bit zero of the original input. Changing that bit changes
the result of the same walk. The clock and workspace checks cover arbitrary selectors.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingBoundedWalk

open Turing MultiTapeTM ComputableInSpace NondeterministicQueryMachine
open Turing.DoubleCounting.BoundedWalk
open Cslib.DoubleCounting.Scan

private def edge : QueryMachine (Option Bool) where
  init := none
  query _ := 0
  next := fun (_, answer) => some (answer.getD false)
  halted := Option.isSome
  emit _ := []
  finish _ := []

private def start (_ _ : Fin 3) : Option Bool := none

private def verdict (s : Option Bool) : Bool := s.getD false

private theorem edge_halts (input : List Bool) (u v : Fin 3) :
    edge.halted (edge.runFrom input (start u v) 1) = true := by
  cases input <;> rfl

private theorem edge_agrees (input : List Bool) (u v : Fin 3) :
    verdict (edge.runFrom input (start u v) 1) = input.headD false := by
  cases input <;> rfl

private def moving : Registers 3 := ⟨0, 1, 1⟩

/-- Stopping at the initial target is valid at zero remaining fuel. -/
example :
    (machine edge start verdict 1 ⟨0, 0, 0⟩).run [] (selectors 1 ([] : List (Fin 3))) =
      .done (some 0) := by
  rw [run_selectors edge start verdict 1 _ [] (fun _ _ => false)
    (edge_halts []) (edge_agrees [])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A continuation with exhausted fuel rejects even if the edge callback would agree. -/
example :
    (machine edge start verdict 1 ⟨0, 1, 0⟩).run [true] (selectors (N := 3) 1 [1]) =
      .done none := by
  rw [run_selectors edge start verdict 1 _ [true] (fun _ _ => true)
    (edge_halts [true]) (edge_agrees [true])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A suspended caller can enter the same transition machine with a new target and fuel. -/
example :
    (machine edge start verdict 1 moving).replay [false] (selectors (N := 3) 1 [])
      (machine edge start verdict 1 ⟨0, 0, 0⟩).init = .done (some 0) := by
  rw [← run_withInit, machine_withInit]
  rw [run_selectors edge start verdict 1 _ [false] (fun _ _ => false)
    (edge_halts [false]) (edge_agrees [false])]
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure]

/-- A complete one-edge selector on the input identifies its destination even in a longer word. -/
example (tail : List (Fin 3)) (h : selectors (N := 3) 1 [1] <+: selectors 1 tail) :
    tail = [1] :=
  (eq_of_selectors_prefix 1 h).symm

/-- Rank three is outside the three-vertex domain. -/
example :
    (machine edge start verdict 1 moving).run [true] [true, true, true, false] = .done none :=
  run_invalid_vertex edge start verdict 1 moving [true] [true, true] rfl rfl

/-- The same proposed edge succeeds on a one bit and fails on a zero bit of the original tape. -/
example :
    (machine edge start verdict 1 moving).run [true] (selectors (N := 3) 1 [1]) = .done (some 0) ∧
    (machine edge start verdict 1 moving).run [false] (selectors (N := 3) 1 [1]) = .done none := by
  constructor
  · rw [run_selectors edge start verdict 1 _ [true] (fun _ _ => true)
      (edge_halts [true]) (edge_agrees [true])]
    simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]
  · rw [run_selectors edge start verdict 1 _ [false] (fun _ _ => false)
      (edge_halts [false]) (edge_agrees [false])]
    simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]

/-- The same bounds also apply to invalid destination and failed-call prefixes. -/
example (input bits : List Bool) :
    (machine edge start verdict 1 moving).HaltsWithin input 10 ∧
      (encState (encOption encBool) ((machine edge start verdict 1 moving).run input bits)).length
        ≤ 61 := by
  have hlength (u v : Fin 3) (t : ℕ) (_ : t ≤ 1) :
      (encOption encBool (edge.runFrom input (start u v) t)).length ≤ 2 := by
    cases edge.runFrom input (start u v) t with
    | none => decide
    | some answer => cases answer <;> decide
  exact ⟨haltsWithin edge start verdict 1 moving input,
    length_run_le edge start verdict 1 moving input (encOption encBool) 2 hlength bits⟩

private def budget (input : List Bool) : ℕ := Nat.log2 input.length + 10

/-- An enclosing caller can load the boundary and decode the returned fuel in native space. -/
example :
    ComputableInSpace (fun (r : Registers 3) => (machine edge start verdict 1 r).init)
      (encRegisters 3) (encState (encOption encBool)) (fun r => (encRegisters 3 r).length) ∧
    ComputableInSpace (remainingFuel (N := 3) (τ := Option Bool))
      (encState (encOption encBool)) (encOption encNat)
      (fun s => (encState (encOption encBool) s).length) :=
  ⟨init_budget edge start verdict 1 (of_inO ComputableInDegree.id'.inO_one),
    remainingFuel_inSpace (encOption encBool)⟩

private theorem edgeNext_inSpace :
    ComputableInSpace edge.next (QueryMachine.encStateRead (encOption encBool))
      (encOption encBool) (fun p => (QueryMachine.encStateRead (encOption encBool) p).length) :=
  budget_optionSome (budget_optionGetD false (snd (encOption encBool) (encOption encBool)))

/-- The same walk has native routines with one space envelope for all selector paths. -/
private theorem routines : Nonempty (Routines (machine edge start verdict 1 moving)
    (fun _ : List Bool => (machine edge start verdict 1 moving).init) encBits budget) := by
  have hstart : ComputableInSpace (fun p : Fin 3 × Fin 3 => start p.1 p.2)
      (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat))
      (encOption encBool) (fun p =>
        (encPair (Fin.valEmbedding.trans encNat) (Fin.valEmbedding.trans encNat) p).length) :=
    budget_const none (.refl _)
  have hresult : ComputableInSpace id (encOption encBool) (encOption encBool)
      (fun s => (encOption encBool s).length) := of_inO ComputableInDegree.id'.inO_one
  refine Turing.DoubleCounting.BoundedWalk.exists_routines edge start verdict 1 moving
    (encOption encBool) hstart (budget_const 0 (.refl _)) edgeNext_inSpace
    (budget_optionIsSome hresult) (budget_optionGetD false hresult) (fun _ => moving) ?_ ?_ ?_ ?_
  · exact (ComputableInSpace.constZero moving).mono_le fun _ => Nat.zero_le _
  · intro input
    rw [budget, encBits_apply]
    omega
  · intro input
    unfold budget
    have h : 6 ≤ 10 := by decide
    exact h.trans (Nat.le_add_left _ _)
  · intro input u v t _
    have h : (encOption encBool (edge.runFrom input (start u v) t)).length ≤ 2 := by
      cases edge.runFrom input (start u v) t with
      | none => decide
      | some answer => cases answer <;> decide
    exact h.trans (by unfold budget; omega)

/-- Compiling the same-input test gives one successful occurrence list for the valid walk. -/
example : ∃ R : Routines (machine edge start verdict 1 moving)
    (fun _ : List Bool => (machine edge start verdict 1 moving).init) encBits budget,
    R.machine.RunsInSpace [true] (R.k * (2 * (R.c * budget [true]) + 1)) ∧
      (∃ t, R.machine.RunsInTime [true] t) ∧
      ∃! indices, ∃ final,
        Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg [true]) indices =
          some (selectors (N := 3) 1 [1], final) ∧ final.Halted ∧ final.output = [true] := by
  obtain ⟨R⟩ := routines
  refine ⟨R, R.runsInSpace [true], ?_, ?_⟩
  · exact R.exists_runsInTime [true] (haltsWithin edge start verdict 1 moving [true])
  refine (native_firstHalting_accept_iff edge start verdict 1 moving (fun _ => moving) R
    [true] (fun _ _ => true) (edge_halts [true]) (edge_agrees [true]) _).mpr ⟨[1], 0, rfl, ?_⟩
  simp [walkM, readNext, bind, StateT.bind, pure, StateT.pure, moving]

private def runtimeStart (enabled : Bool) (_ _ : ℕ) : Option Bool :=
  if enabled then none else some false

private def indexedEdge : QueryMachine (Option Bool) :=
  { edge with query := fun s => (s.getD false).toNat }

/-- A single set of read certificates covers every runtime dimension and state. -/
example :
    let initial := Runtime.entry indexedEdge runtimeStart verdict 1 false moving
    let M := Runtime.machine indexedEdge runtimeStart verdict 1 initial
    let enc := Runtime.encState encBool (encOption encBool)
    let size s := (enc s).length
    ComputableInSpace M.query enc encNat size ∧
      ComputableInSpace M.halted enc encBool size ∧
      ComputableInSpace Runtime.remainingFuel enc (encOption encNat) size := by
  intro initial M enc size
  refine ⟨Runtime.query_inSpace indexedEdge runtimeStart verdict 1 initial encBool
    (encOption encBool) ?_,
    Runtime.halted_inSpace indexedEdge runtimeStart verdict 1 initial encBool (encOption encBool),
    Runtime.remainingFuel_inSpace encBool (encOption encBool)⟩
  exact of_finite (fun s : Option Bool => (s.getD false).toNat)

/-- The same runtime transition machine re-enters a four-vertex graph and reads the original
input while running the selected one-edge walk. -/
example :
    let initial := Runtime.entry edge runtimeStart verdict 1 false moving
    let r : Registers 4 := ⟨0, 1, 1⟩
    let next := Runtime.entry edge runtimeStart verdict 1 true r
    let M := (Runtime.machine edge runtimeStart verdict 1 initial).withInit next
    let bits := selectors (N := 4) 1 [1]
    M.FirstHalting [true] bits next ∧ Runtime.remainingFuel (M.run [true] bits) = some 0 := by
  intro initial r next M bits
  have hhalt (u v : Fin 4) :
      edge.halted (edge.runFrom [true] (runtimeStart true u.val v.val) 1) = true := by rfl
  have hedge (u v : Fin 4) :
      verdict (edge.runFrom [true] (runtimeStart true u.val v.val) 1) = true := by rfl
  have hresult :
      (walkM readNext (fun _ _ => pure true) r.target r.fuel r.current [1]).1 = some 0 := by
    simp [r, walkM, readNext, bind, StateT.bind, pure, StateT.pure]
  obtain ⟨hfirst, hfuel⟩ := (firstHalting_remainingFuel_iff edge
    (fun u v : Fin 4 => runtimeStart true u.val v.val) verdict 1 r [true]
    (fun _ _ => true) hhalt hedge bits 0).mpr ⟨[1], rfl, hresult⟩
  dsimp only [M]
  rw [Runtime.machine_withInit]
  exact ⟨(Runtime.firstHalting_iff edge runtimeStart verdict 1 true r [true] bits).mpr hfirst,
    (Runtime.remainingFuel_run edge runtimeStart verdict 1 true r [true] bits).trans hfuel⟩

/-- The runtime state envelope also covers arbitrary rejecting selector prefixes. -/
example (input bits : List Bool) :
    let r : Registers 4 := ⟨0, 1, 1⟩
    let initial := Runtime.entry edge runtimeStart verdict 1 true r
    let M := Runtime.machine edge runtimeStart verdict 1 initial
    M.HaltsWithin input 12 ∧
      (Runtime.encState encBool (encOption encBool) (M.run input bits)).length ≤ 83 := by
  intro r initial M
  have hcallee (u v : Fin 4) (t : ℕ) (_ : t ≤ 1) :
      (encOption encBool (edge.runFrom input (runtimeStart true u.val v.val) t)).length ≤ 2 := by
    cases edge.runFrom input (runtimeStart true u.val v.val) t with
    | none => decide
    | some answer => cases answer <;> decide
  refine ⟨Runtime.haltsWithin edge runtimeStart verdict 1 true r input,
    (Runtime.length_run_le edge runtimeStart verdict 1 true r input bits encBool
      (encOption encBool) 2 hcallee).trans ?_⟩
  decide

private def runtimeDimension (p : Bool × ℕ) := if p.1 then 4 else 2

private def runtimeRegisters (p : Bool × ℕ) : Registers (runtimeDimension p) :=
  ⟨⟨0, by dsimp [runtimeDimension]; cases p.1 <;> decide⟩,
    ⟨if p.1 then 3 else 1, by dsimp [runtimeDimension]; cases p.1 <;> decide⟩, p.2⟩

/-- A single native entry routine loads a two- or four-vertex graph and the supplied fuel. -/
example :
    let enc := encPair encBool encNat
    ComputableInSpace (fun p => Runtime.entry edge runtimeStart verdict 1 p.1 (runtimeRegisters p))
      enc (Runtime.encState encBool (encOption encBool)) (fun p => (enc p).length) := by
  intro enc
  have hcontext := fst encBool encNat
  refine Runtime.entry_budget edge runtimeStart verdict 1 encBool (encOption encBool)
    hcontext (budget_finite (fun b : Bool => if b then 4 else 2) hcontext)
    ?_ ?_ (snd encBool encNat)
  · exact budget_const 0 (.refl _)
  · exact budget_finite (fun b : Bool => if b then 3 else 1) hcontext

/-- The same native call update works at two dimensions with a runtime clock remainder. -/
example :
    let enc := encPair encBool encNat
    let dest (p : Bool × ℕ) := (runtimeRegisters p).target
    let callee (p : Bool × ℕ) := if p.1 then some true else none
    let initial := Runtime.entry edge runtimeStart verdict 1 false moving
    let M := Runtime.machine edge runtimeStart verdict 1 initial
    ComputableInSpace (fun p => M.next
      (⟨p.1, runtimeDimension p, Nat.zero_lt_of_lt (dest p).isLt,
        .call (runtimeRegisters p) (dest p) p.2 (callee p)⟩, some p.1, false))
      enc (Runtime.encState encBool (encOption encBool)) (fun p => (enc p).length) := by
  intro enc dest callee initial M
  have hflag := fst encBool encNat
  have hclock := snd encBool encNat
  have hdim := budget_finite (encC := encNat) (fun b : Bool => if b then 4 else 2) hflag
  have hdest := budget_finite (encC := encNat) (fun b : Bool => if b then 3 else 1) hflag
  have hregisters := registersWord_budget (r := runtimeRegisters)
    (budget_const 0 (.refl _)) hdest hclock
  have hresult : ComputableInSpace id (encOption encBool) (encOption encBool)
      (fun s => (encOption encBool s).length) := of_inO ComputableInDegree.id'.inO_one
  have hcallee := budget_finite (encC := encOption encBool)
    (fun b : Bool => if b then some true else none) hflag
  have hwalk := advanceCall_budget (r := runtimeRegisters) (v := dest)
    edgeNext_inSpace (budget_optionIsSome hresult) (budget_optionGetD false hresult)
    hdim hregisters hdest hclock hcallee (budget_optionSome hflag)
    (budget_const false (.refl _))
  refine (Runtime.state_budget (positive := fun p => Nat.zero_lt_of_lt (dest p).isLt)
    encBool (encOption encBool) hflag hdim hwalk).of_enc_eq fun p => ?_
  dsimp only [M]
  rw [Runtime.machine_next_call]
  rfl

/-- One choice certificate covers a valid rank at width three and an out-of-range rank
at width two, with fuel and adjacency context supplied by the caller. -/
example :
    let enc := encPair encBool encNat
    let reader (p : Bool × ℕ) : Turing.DoubleCounting.NondeterministicChoice.State :=
      let width := if p.1 then 3 else 2
      ⟨true, false, ⟨runtimeDimension p, width, width, width, false⟩⟩
    let initial := Runtime.entry edge runtimeStart verdict 1 false moving
    let M := Runtime.machine edge runtimeStart verdict 1 initial
    ComputableInSpace (fun p => M.next
      (⟨p.1, runtimeDimension p, Nat.zero_lt_of_lt (runtimeRegisters p).current.isLt,
        .choose (runtimeRegisters p) (reader p)⟩, none, false))
      enc (Runtime.encState encBool (encOption encBool)) (fun p => (enc p).length) := by
  intro enc reader initial M
  have hctx := fst encBool encNat
  have hdim := budget_finite (encC := encNat) (fun b : Bool => if b then 4 else 2) hctx
  have hwidth := budget_finite (encC := encNat) (fun b : Bool => if b then 3 else 2) hctx
  have hdest := budget_finite (encC := encNat) (fun b : Bool => if b then 3 else 1) hctx
  have hregisters := registersWord_budget (r := runtimeRegisters)
    (budget_const 0 (.refl _)) hdest (snd encBool encNat)
  have hreader : ComputableInSpace reader enc Turing.DoubleCounting.NondeterministicChoice.encState
      (fun p => (enc p).length) := Turing.DoubleCounting.NondeterministicChoice.encState_mk_budget
    (budget_const true (.refl _)) (budget_const false (.refl _))
    (Turing.DoubleCounting.VertexReader.encState_mk_budget hdim hwidth hwidth hwidth
      (budget_const false (.refl _)))
  have hstart (v : (p : Bool × ℕ) → Fin (runtimeDimension p))
      (_ : ComputableInSpace (fun p => (v p).val) enc encNat (fun p => (enc p).length)) :
      ComputableInSpace (fun p => runtimeStart p.1 (runtimeRegisters p).current.val (v p).val)
        enc (encOption encBool) (fun p => (enc p).length) :=
    budget_finite (fun b : Bool => if b then none else some false) hctx
  have hwalk := advanceChoice_budget (dimension := runtimeDimension) (r := runtimeRegisters)
    (reader := reader) (start := fun p u v => runtimeStart p.1 u.val v.val) 1
    hdim hregisters hreader (budget_const false (.refl _)) hstart
  refine (Runtime.state_budget
    (positive := fun p => Nat.zero_lt_of_lt (runtimeRegisters p).current.isLt)
    encBool (encOption encBool) hctx hdim hwalk).of_enc_eq fun p => ?_
  dsimp only [M]
  rw [Runtime.machine_next_choice]

/-- The complete runtime transition accepts any encoded phase, including after re-entry
at a different dimension and with an input-dependent callee reply. -/
example :
    let initial := Runtime.entry edge runtimeStart verdict 1 false moving
    let enc := Runtime.encStep encBool (encOption encBool)
    ComputableInSpace (Runtime.machine edge runtimeStart verdict 1 initial).next
      enc (Runtime.encState encBool (encOption encBool)) (fun p => (enc p).length) := by
  intro initial enc
  have hresult : ComputableInSpace id (encOption encBool) (encOption encBool)
      (fun s => (encOption encBool s).length) := of_inO ComputableInDegree.id'.inO_one
  exact Runtime.next_inSpace edge runtimeStart verdict 1 initial encBool (encOption encBool)
    (budget_finite (fun b : Bool => if b then none else some false)
      (fst encBool (encPair encNat encNat)))
    edgeNext_inSpace (budget_optionIsSome hresult) (budget_optionGetD false hresult)

end CslibFrontierTests.DoubleCountingBoundedWalk
