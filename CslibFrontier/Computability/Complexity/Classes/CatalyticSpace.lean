/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.Space

/-!
# Deterministic catalytic space

A native machine has ordinary work tapes and a distinguished last tape containing the
catalyst. The catalyst starts as an arbitrary binary word of the prescribed length. It
stays binary throughout the run, with blank read-only boundary cells, and must have
exactly its original contents at halting. The output bit is independent of the catalyst.

The ordinary budget counts the cells visited on the other work tapes. The input and
catalyst heads range over their respective finite tapes with boundary cells. The
addressability condition bounds the catalyst length by two to the power of the
ordinary space bound. The computation must halt for every catalyst with no time bound
beyond halting.

This follows [Koucký, Mertz, Pyne and Sami][KouckyMertzPyneSami2025], arXiv:2504.08444v1,
§2, Definitions 1–4. We use the native blank-initialized ordinary work tapes and encode
the final accept or reject decision by one bit on the write-only output. The logarithmic
specialization shifts the input length at zero.

## Main definitions

* `Cslib.Catalytic.initialConfig` and `Cslib.Catalytic.ValidRun`: the native configuration
  and restoring-run contract.
* `Cslib.Complexity.CSPACE` and `Cslib.Complexity.CL`: deterministic catalytic space and
  catalytic logspace.
-/

public section

namespace Cslib.Catalytic

open Turing Turing.MultiTapeNTM Turing.MultiTapeTM

variable {k : ℕ} {State : Type} {input : List Bool}

/-- Initialize an ordinary configuration with the supplied word on its last work tape. -/
@[expose] def initialConfig (initial : State) (input catalyst : List Bool) :
    Cfg (k + 1) Bool State input :=
  wordsCfg input (some initial) (Fin.lastCases catalyst (fun _ => [])) []

/-- The total number of visited cells on the ordinary work tapes. -/
@[expose] def freeSpaceUsed {M : MultiTapeNTM (k + 1) Bool State}
    (p : M.RunPath input) : ℕ :=
  ∑ i : Fin k, p.spaceUsedByTape i.castSucc

/-- A halted run that uses the allotted ordinary space and restores its catalyst.
The catalyst uses one bit per cell, and its two blank boundary cells cannot be written. -/
structure ValidRun {M : MultiTapeNTM (k + 1) Bool State}
    (p : M.RunPath input) (catalyst : List Bool) (space : ℕ) (answer : Bool) : Prop where
  /-- The machine starts with this catalyst and empty ordinary work tapes. -/
  starts : p.head = initialConfig M.q₀ input catalyst
  /-- The machine reaches a halting configuration. -/
  halted : p.last.Halted
  /-- The write-only output encodes the decision. -/
  output : p.last.output = [answer]
  /-- Only the ordinary work tapes are charged to this bound. -/
  freeSpace_le : freeSpaceUsed p ≤ space
  /-- The head stays on the catalyst or one of its two boundary cells. -/
  catalystHead : ∀ c ∈ p, -1 ≤ c.workTapePos (Fin.last k) ∧
    c.workTapePos (Fin.last k) ≤ (catalyst.length : ℤ)
  /-- Every cell of the catalyst holds a bit, and all exterior cells remain blank. -/
  catalystCells : ∀ c ∈ p, ∀ i : ℤ, (c.workTapes (Fin.last k) i).isSome ↔
    0 ≤ i ∧ i < (catalyst.length : ℤ)
  /-- Restoration includes every cell of the borrowed tape. -/
  restored : p.last.workTapes (Fin.last k) = p.head.workTapes (Fin.last k)

end Cslib.Catalytic

namespace Cslib.Complexity

open Turing

variable {α : Type}

/-- Deterministic catalytic space, with separately specified ordinary budget and catalyst length
as functions of encoded input length. One finite-state machine works for every initial catalyst. -/
@[expose] def CSPACE (enc : α ↪ List Bool) (space catalystLength : ℕ → ℕ) : Set (Set α) :=
  {A | (∀ n, catalystLength n ≤ 2 ^ space n) ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeTM (k + 1) Bool State),
      ∀ (a : α) (catalyst : List Bool), catalyst.length = catalystLength (enc a).length →
        ∃ (p : M.RunPath (enc a)) (answer : Bool),
          Catalytic.ValidRun p catalyst (space (enc a).length) answer ∧
            (answer = true ↔ a ∈ A)}

/-- Catalytic logspace has logarithmic ordinary space and a polynomial-length catalyst. -/
@[expose] def CL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ c d : ℕ, A ∈ CSPACE enc
    (fun n => c * (Nat.log2 n + 1)) (fun n => (n + 1) ^ d)}

end Cslib.Complexity
