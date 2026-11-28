/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-!
# Native linear-workspace compact-graph routines

All runtime numbers use binary encodings. The table and register indices are fixed, so the
algorithms below use finitely many linear-workspace arithmetic routines. These certificates
charge no copy of the original input word: the edge routine receives only its length, two IDs,
and the single supplied symbol. The time bound is unrestricted.

The routines take the radix as a computed argument, so they serve every radix, such as one stored
by the caller.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.readRegisters_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.valid_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.nextRegisters_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.matchesEntry_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.fitsB_budget`: register-level space-budget routines.
* `Turing.MultiTapeNTM.ConfigurationGraph.queryIndex_budget`: compute the only input query.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_budget`: evaluate an edge locally.
* `Turing.MultiTapeNTM.ConfigurationGraph.bad_budget`: recognize an accepting halted vertex.
* `Turing.MultiTapeNTM.ConfigurationGraph.overflow_budget`: recognize a step leaving the radix.
* `Turing.MultiTapeNTM.ConfigurationGraph.radix_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.vertexBound_budget`,
  `Turing.MultiTapeNTM.ConfigurationGraph.startID_budget`: the radix, size and start of the graph.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open MultiTapeTM ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

private theorem all_inSpace {ι : Type} (l : List ι) {f : ι → α → Bool}
    (hf : ∀ i, ComputableInSpace (f i) enc encBool S) :
    ComputableInSpace (fun a => (l.map fun i => f i a).all id) enc encBool S := by
  induction l with
  | nil => exact budget_const true
  | cons i l ih => exact budget_boolAnd (hf i) ih

private theorem any_inSpace {ι : Type} (l : List ι) {f : ι → α → Bool}
    (hf : ∀ i, ComputableInSpace (f i) enc encBool S) :
    ComputableInSpace (fun a => l.any fun i => f i a) enc encBool S := by
  induction l with
  | nil => exact budget_const false
  | cons i l ih => exact budget_boolOr (hf i) ih

variable {k : ℕ} {State : Type} [Fintype State]
  {B n u v : α → ℕ} {symbol : α → Option Bool}

/-- Reading any fixed register preserves a common space budget. -/
theorem readRegisters_budget (hB : ComputableInSpace B enc encNat S)
    (hu : ComputableInSpace u enc encNat S) (i : Register k) :
    ComputableInSpace (fun a => readRegisters (B a) (u a) i) enc encNat S :=
  budget_comp_linear (component_inSpace i) (budget_prod hB hu)

/-- Computing the configuration radix for a fixed exponent preserves the space budget
of the binary input length. -/
theorem radix_budget (D : ℕ) (hn : ComputableInSpace n enc encNat S) :
    ComputableInSpace (fun a => radix D (n a)) enc encNat S :=
  budget_natPow (budget_natAdd hn (budget_const 2)) D

/-- The ambient graph size is computable from the radix. -/
theorem vertexBound_budget (hB : ComputableInSpace B enc encNat S) :
    ComputableInSpace (fun a => vertexBound (k := k) (B a)) enc encNat S :=
  budget_natPow hB (Fintype.card (Register k))

/-- Syntactic validity of a packed ID preserves a common space budget. -/
theorem valid_budget (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S) :
    ComputableInSpace (fun a => valid (k := k) (State := State) (B a) (n a) (u a))
      enc encBool S := by
  have hr := readRegisters_budget (k := k) hB hu
  have hh := all_inSpace (List.ofFn fun i : Fin k => i)
    (fun i => budget_natLt (hr (.head i)) (budget_const 3))
  refine (budget_boolAnd (budget_boolAnd (budget_boolAnd
    (budget_boolAnd (budget_natLt hu (vertexBound_budget (k := k) hB))
      (budget_natLt (hr .inputPos) (budget_natAdd hn (budget_const 2))))
    (budget_natLt (hr .control) (budget_const (Fintype.card (Option State)))))
    (budget_natLt (hr .output) (budget_const 3))) hh).of_enc_eq fun a => ?_
  congr 1
  simp [valid, List.map_ofFn, Function.comp_def]

private theorem inputSymbol_budget {p : α → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S) :
    ComputableInSpace (fun a => inputSymbol (n a) (p a) (symbol a))
      enc (encOption encBool) S := by
  have hc := budget_boolOr (budget_natIsZero hp) (budget_natEq hp (budget_natSucc hn))
  simpa only [inputSymbol, Bool.or_eq_true, decide_eq_true_eq] using
    budget_ite hc (budget_const none) hs

/-- Updating any fixed register by a fixed native action preserves a common space budget. -/
theorem nextRegisters_budget {r : α → Register k → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S)
    (act : Action k Bool State) (i : Register k) :
    ComputableInSpace (fun a => nextRegisters (n a) (r a) act i) enc encNat S := by
  cases i with
  | inputPos =>
    cases hm : act.inputTape with
    | neg => simpa only [nextRegisters, hm, inputMove] using budget_natPred (hr .inputPos)
    | zero => simpa only [nextRegisters, hm, inputMove] using hr .inputPos
    | pos =>
      simpa only [nextRegisters, hm, inputMove] using
        budget_natMin (budget_natSucc (hr .inputPos)) (budget_natSucc hn)
  | control => exact budget_const _
  | output =>
    cases ho : act.output with
    | none => simpa only [nextRegisters, ho, outputStep] using hr .output
    | some b =>
      simpa only [nextRegisters, ho, outputStep, decide_eq_true_eq] using
        budget_ite (budget_natIsZero (hr .output))
          (budget_const (encB := encNat) (if b then 1 else 2)) (budget_const 2)
  | head i | left i | right i =>
    have hh : ComputableInSpace
        (fun a => (act.workTapes i).1.elim (r a (.head i)) symbolCode) enc encNat S := by
      cases (act.workTapes i).1 with
      | none => exact hr (.head i)
      | some b => exact budget_const _
    have hthree : ComputableInSpace (fun _ : α => 3) enc encNat S := budget_const 3
    cases hm : (act.workTapes i).2 <;>
      simp only [nextRegisters, tapeStep, hm] <;>
      first
      | exact hh
      | exact hr _
      | exact budget_natMod (hr _) hthree
      | exact budget_natDiv (hr _) hthree
      | exact budget_natAdd hh (budget_natMul hthree (hr _))

/-- Checking whether decoded registers match a fixed table entry preserves a common space budget. -/
theorem matchesEntry_budget {r : α → Register k → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (t : Instruction k State) :
    ComputableInSpace (fun a => matchesEntry (n a) (r a) (symbol a) t) enc encBool S := by
  have hc := budget_natEq (hr .control) (budget_const (stateCode (some t.1)))
  have hi := budget_finite (encC := encBool) (fun b : Option Bool => decide (b = t.2.1))
    (inputSymbol_budget hn (hr .inputPos) hs)
  have hh := all_inSpace (List.ofFn fun i : Fin k => i)
    (fun i => budget_natEq (hr (.head i)) (budget_const (symbolCode (t.2.2.1 i))))
  apply (budget_boolAnd (budget_boolAnd hc hi) hh).of_enc_eq
  intro a
  congr 1
  dsimp only [matchesEntry]
  rw [List.map_ofFn]
  rfl

/-- Checking that every register fits below the radix preserves a common space budget. -/
theorem fitsB_budget {r : α → Register k → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S) :
    ComputableInSpace (fun a => fitsB (B a) (r a)) enc encBool S := by
  simpa only [fitsB, List.all_map, Function.comp_def, id_eq] using
    all_inSpace (Finset.univ.toList : List (Register k)) (fun i => budget_natLt (hr i) hB)

/-- Local edge evaluation preserves any budget covering the short arguments. -/
theorem edgeWithSymbol_budget (ntm : MultiTapeNTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S) :
    ComputableInSpace (fun a => edgeWithSymbol ntm (B a) (n a) (u a) (v a) (symbol a))
      enc encBool S := by
  have hr := readRegisters_budget (k := k) hB hu
  have hh := budget_boolAnd
    (budget_natEq (hr .control) (budget_const (stateCode (none : Option State))))
    (budget_natEq hv hu)
  have hentry (t : Instruction k State) :=
    let hnxt := nextRegisters_budget hn hr t.2.2.2
    budget_boolAnd (budget_boolAnd (matchesEntry_budget hn hr hs t) (fitsB_budget hB hnxt))
      (budget_natEq hv (pack_inSpace hB hnxt))
  exact budget_boolAnd (budget_boolAnd (valid_budget hB hn hu) (valid_budget hB hn hv))
    (budget_boolOr hh (any_inSpace (instructions ntm) hentry))

/-- The overflow test preserves any budget covering the short arguments. -/
theorem overflow_budget (ntm : MultiTapeNTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S) :
    ComputableInSpace (fun a => overflow ntm (B a) (n a) (u a) (symbol a))
      enc encBool S := by
  have hr := readRegisters_budget (k := k) hB hu
  have hentry (t : Instruction k State) :=
    budget_boolAnd (matchesEntry_budget hn hr hs t)
      (budget_finite (encC := encBool) not
        (fitsB_budget hB (nextRegisters_budget hn hr t.2.2.2)))
  exact budget_boolAnd (valid_budget hB hn hu) (any_inSpace (instructions ntm) hentry)

/-- Compute the only input query in native deterministic linear workspace. -/
theorem queryIndex_budget (hB : ComputableInSpace B enc encNat S)
    (hu : ComputableInSpace u enc encNat S) :
    ComputableInSpace (fun a => queryIndex (k := k) (B a) (u a)) enc encNat S :=
  budget_natPred (readRegisters_budget hB hu .inputPos)

/-- Recognize the accepting halted vertices in native deterministic linear workspace. -/
theorem bad_budget (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S) :
    ComputableInSpace (fun a => bad (State := State) (k := k) (B a) (n a) (u a))
      enc encBool S := by
  have hr := readRegisters_budget (k := k) hB hu
  exact budget_boolAnd (budget_boolAnd (valid_budget hB hn hu)
    (budget_natEq (hr .control) (budget_const (stateCode (none : Option State)))))
    (budget_natEq (hr .output) (budget_const 1))

/-- Compute the input-independent start ID from the radix. -/
theorem startID_budget (ntm : MultiTapeNTM k Bool State)
    (hB : ComputableInSpace B enc encNat S) :
    ComputableInSpace (fun a => startID ntm (B a)) enc encNat S :=
  pack_inSpace hB (fun _ => budget_const _)

end Turing.MultiTapeNTM.ConfigurationGraph
