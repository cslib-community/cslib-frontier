/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode

/-!
# Problem instances, output encoding, and output register for Word-RAM 2-SAT

Defines `Instance` together with `Instance.totalLits`, `Instance.encode`, `Instance.outAddrBase`,
`Instance.wordBound`, and `Instance.encode_length`, as well as `encodeAssignment`, `answerWords`,
`decodeAnswer`, and `Reg.outBase`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode

/-- A `CNF (Fin n)` instance for the word-RAM 2-SAT solver. -/
structure Instance where
  /-- Number of Boolean variables. -/
  n : ℕ
  /-- Input formula over `Fin n`. -/
  φ : CNF (Fin n)

namespace Instance

/-- Total literal occurrences across all clauses of `G.φ`. -/
@[expose] def totalLits (G : Instance) : ℕ :=
  (G.φ.map List.length).sum

/-- Word-list encoding `[n, |φ|] ++ φ.flatMap (encodeClauseBy Fin.val)`. -/
@[expose] def encode (G : Instance) : List ℕ :=
  G.n :: G.φ.length :: G.φ.flatMap (encodeClauseBy Fin.val)

/-- Output header address `G.encode.length + 1`, immediately past the input in `State.init`. -/
@[expose] def outAddrBase (G : Instance) : ℕ :=
  G.encode.length + 1

/-- Linear word-size envelope covering input length, literal codes, and scratch memory addresses. -/
@[expose] def wordBound (G : Instance) : ℕ :=
  32 * (G.n + G.φ.length + G.totalLits + 1)

private theorem length_flatMap_encodeClauseBy {n : ℕ} :
    ∀ cs : CNF (Fin n),
      (cs.flatMap (encodeClauseBy Fin.val)).length = cs.length + (cs.map List.length).sum
  | [] => rfl
  | c :: cs => by
    simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy, List.length_cons,
      List.map_cons, List.sum_cons, length_flatMap_encodeClauseBy cs]
    omega

/-- Length of `G.encode` in words. -/
theorem encode_length (G : Instance) :
    G.encode.length = 2 + G.φ.length + G.totalLits := by
  simp only [encode, totalLits, List.length_cons, length_flatMap_encodeClauseBy]
  omega

end Instance

/-- Encode an assignment `σ : Fin n → Bool` as `1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]`. -/
@[expose] def encodeAssignment {n : ℕ} (σ : Fin n → Bool) : List ℕ :=
  1 :: (List.finRange n).map fun v => (σ v).toNat

/-- Canonical word-list output of the 2-SAT solver on `G`. -/
@[expose] def answerWords (G : Instance) : List ℕ :=
  match solveFin G.n G.φ with
  | none => []
  | some σ => encodeAssignment σ

/-- Decode a word list returned by `program` back to `Option (Fin G.n → Bool)`. -/
@[expose] def decodeAnswer (G : Instance) : List ℕ → Option (Fin G.n → Bool)
  | [] => none
  | _ :: bits => some fun v => bits.getD v.val 0 != 0


namespace Reg

/-- Output-list header register (`G.outAddrBase`). -/
abbrev outBase : Fin 28 := ⟨7, by decide⟩

end Reg

end Cslib.Algorithms.WordRAM.TwoSAT
