/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.WordRAM.Function

/-!
# Public `ElimInstance` Bundle and Serialization

Defines the word-list factor serializer `encodeFactor` and the public `ElimInstance` bundle
(including `initState`, `result`, `maxEntry`, `encode`, `wordBound`, `stepBound`, `ofCSP`, and
`result_ofCSP`) for bucket elimination on the exact-basis Word-RAM. Kept free of `Realization` and
`Tactic.Realize` dependencies so pure clients stay lightweight.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.encodeFactor`: word-array serialization of a
  `FactorTable ℕ ℕ`.
* `Cslib.Algorithms.WordRAM.VariableElimination.ElimInstance`: input bundle (`domain`, `declared`,
  `order`, `factors`) together with its encoding, word-width bound, and step-bound functions.

## Main results

* `Cslib.Algorithms.WordRAM.VariableElimination.ElimInstance.result_ofCSP`: connects
  `ElimInstance.ofCSP` to `CSP.partitionFunctionOn`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP

/-- Word-array serialization of a factor table: `[f.scope.length, f.entries.size] ++ f.scope ++
f.entries.toList`. -/
@[expose] def encodeFactor (f : FactorTable ℕ ℕ) : List ℕ :=
  [f.scope.length, f.entries.size] ++ f.scope ++ f.entries.toList

/-- Word-RAM input bundle for bucket (variable) elimination over explicit `ℕ`-valued radix-indexed
factor tables at finite domain size `domain`. -/
structure ElimInstance where
  /-- Domain size `d` (variables range over `0, ..., domain - 1`). -/
  domain : ℕ
  /-- Declared variables to contract over (`ElimState.remaining` initially). -/
  declared : List ℕ
  /-- Supplied variable elimination order. -/
  order : List ℕ
  /-- Initial explicit radix-indexed factor tables. -/
  factors : List (FactorTable ℕ ℕ)

namespace ElimInstance

/-- Initial pure elimination state `ElimState.ofFactors inst.factors inst.declared`. -/
@[expose] def initState (inst : ElimInstance) : ElimState ℕ ℕ :=
  ElimState.ofFactors inst.factors inst.declared

/-- Pure contracted scalar result
`(eliminateOrder inst.domain inst.order inst.initState).result`. -/
@[expose] def result (inst : ElimInstance) : ℕ :=
  (eliminateOrder inst.domain inst.order inst.initState).result

/-- Maximum entry across all initial factor tables (`0` if all tables are empty). -/
@[expose] def maxEntry (inst : ElimInstance) : ℕ :=
  (inst.factors.map fun f => f.entries.toList.foldl max 0).foldl max 0

/-- Word-array serialization of `inst`:
`[inst.domain, inst.declared.length, inst.order.length, inst.factors.length] ++ inst.declared ++
inst.order ++ inst.factors.flatMap encodeFactor`. -/
@[expose] def encode (inst : ElimInstance) : List ℕ :=
  [inst.domain, inst.declared.length, inst.order.length, inst.factors.length] ++
    inst.declared ++ inst.order ++ inst.factors.flatMap encodeFactor

/-- Word-value upper bound covering literal constants, peak memory frontier across the entire
elimination run, radix powers `(max 1 domain) ^ max S W`, and intermediate/final weighted sums
`(max 1 domain) ^ order.length * (max 1 maxEntry) ^ factors.length`. -/
@[expose] def wordBound (inst : ElimInstance) : ℕ :=
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  5 + (inst.encode.length + 1 + 4 * M +
      T * (R + 4 + 8 * M + 2 * (M * SW) + (max 1 d) ^ W)) +
    (max 1 d) ^ SW +
    (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M

/-- Upper bound on the oracle memory cost (`memoryCost`) of bucket elimination along `inst.order`,
exponential only in `W = maxJointScopeLen` (`(max 1 domain) ^ W`) with amortized `M + T` bucket
factor evaluations. -/
@[expose] def stepBound (inst : ElimInstance) : ℕ :=
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  5 + 9 * M +
    T * (1 + (12 + 3 * R + M * (8 + SW) + W + 4 * (max 1 d) ^ W)) +
    (M + T) * (3 + SW * (4 + W) + (max 1 d) ^ W * (5 + SW * W))

/-- Compile a `ℕ`-weighted `CSP Rel ℕ` over finite domain `D ≃ Fin d` with declared variable list
`declared` and elimination order `order` into an `ElimInstance`. -/
@[expose] def ofCSP {Rel D : Type*} [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) (F : CSP Rel ℕ)
    (declared order : List ℕ) : ElimInstance :=
  { domain := d
    declared := declared
    order := order
    factors := FactorTable.ofCSP d e wt F }

/-- `ElimInstance.ofCSP` evaluates to `F.partitionFunctionOn wt declared.toFinset` whenever
`declared` contains all occurring variables of `F` and `order` covers `declared`. -/
theorem result_ofCSP {Rel D : Type*} [Fintype D] [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) {F : CSP Rel ℕ}
    {declared order : List ℕ}
    (hvars : F.vars.toFinset ⊆ declared.toFinset)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    (ofCSP d e wt F declared order).result = F.partitionFunctionOn wt declared.toFinset :=
  result_eliminateOrder_ofCSP d e wt hvars hcover

end ElimInstance

end Cslib.Algorithms.WordRAM.VariableElimination
