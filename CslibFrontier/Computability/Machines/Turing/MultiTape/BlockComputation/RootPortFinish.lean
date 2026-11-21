/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededPredecessorFinish
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Testing one parent port of a seeded group

A candidate parent edge supplies a tagged row and a tagged column key from the endpoint machine.
The port selects one key, evaluates its shared seed, and extracts its radix-64 digit at the
requested coordinate. The decision checks both the candidate's prefix bound and group
membership. The coordinate is supplied in unary so that constructing the radix power has
polynomial cost in the actual input length.
-/

public section

namespace Turing.MultiTapeTM.RootPortFinish

open Cslib ComputableInPolyTime
open SeededPredecessor (Context encContext)

/-- One side of one group in a coordinate of the packing. -/
structure Port where
  /-- Select the column key when true and the row key when false. -/
  column : Bool
  /-- Radix-64 digit position starting from the least significant digit. -/
  coordinate : ℕ
  /-- Group number to compare with the digit. -/
  group : ℕ

/-- The side bit and unary coordinate are framed, followed by the binary group number. -/
enc_structure encPort : Port where column : encBool, coordinate : encUnary, group : encNat

/-- The port and seed metadata share the actual candidate endpoint lookup. -/
structure Input where
  /-- Side, coordinate and requested group. -/
  port : Port
  /-- Seed, prefix bound and candidate edge index. -/
  context : Context
  /-- Tagged row and column, or rejection by the parent endpoint lookup. -/
  endpoint : Option (ℕ × ℕ)

/-- Framed port and seed followed by the tagged binary endpoint pair. -/
enc_structure encInput : Input where
  port : encPort, context : encContext, endpoint : SeededPredecessorFinish.encEnds

/-- The selected digit of the radix-64 label, computed on a tagged vertex key. -/
@[expose] def symbol (c : Context) (i key : ℕ) : ℕ :=
  TrinomialArithmetic.runSelected
    ⟨c.universeSize, 6 * c.labelLength, c.c0, c.c1, c.c2, c.c3, key⟩ / 64 ^ i % 64

/-- Use the selected endpoint key to check strict precedence and group membership. -/
@[expose] def run (a : Input) : Bool :=
  if a.endpoint.isSome then
    let e := a.endpoint.getD (0, 0)
    decide (a.context.candidate < a.context.edge ∧
      symbol a.context a.port.coordinate (if a.port.column then e.2 else e.1) = a.port.group)
  else false

@[simp] theorem run_none (p : Port) (c : Context) : run ⟨p, c, none⟩ = false := rfl

@[simp] theorem run_some (p : Port) (c : Context) (e : ℕ × ℕ) :
    run ⟨p, c, some e⟩ = decide (c.candidate < c.edge ∧
      symbol c p.coordinate (if p.column then e.2 else e.1) = p.group) := rfl

/-- Hashing a computed key and extracting one unary-indexed digit is polynomial time. -/
theorem computableInPolyTime_symbol {α : Type} {enc : α ↪ List Bool}
    {c : α → Context} {i key : α → ℕ} (hc : ComputableInPolyTime c enc encContext)
    (hi : ComputableInPolyTime i enc encUnary) (hkey : ComputableInPolyTime key enc encNat) :
    ComputableInPolyTime (fun a => symbol (c a) (i a) (key a)) enc encNat := by
  have hs := TrinomialArithmetic.encSelectedInput_mk_polyTime
    (SeededPredecessor.encContext_universeSize_polyTime hc)
    (unary_mul' (const 6) (SeededPredecessor.encContext_labelLength_polyTime hc))
    (SeededPredecessor.encContext_c0_polyTime hc) (SeededPredecessor.encContext_c1_polyTime hc)
    (SeededPredecessor.encContext_c2_polyTime hc) (SeededPredecessor.encContext_c3_polyTime hc) hkey
  exact binary_mod' (binary_div' (TrinomialArithmetic.computableInPolyTime_runSelected.comp hs)
    (binary_pow' (const 64) hi)) (const 64)

/-- The finite machine rejects missing endpoints and charges all seed arithmetic on the short
port, seed and endpoint record. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encBool := by
  have he : ComputableInPolyTime Input.endpoint encInput SeededPredecessorFinish.encEnds := by
    fun_prop
  have hen := optionGetDWithInput he (const (encOut := encPair encNat encNat) (0, 0))
  have hp : ComputableInPolyTime Input.port encInput encPort := by fun_prop
  have hc : ComputableInPolyTime Input.context encInput encContext := by fun_prop
  have hs := computableInPolyTime_symbol hc (encPort_coordinate_polyTime hp)
    (ite' (encPort_column_polyTime hp) hen.snd' hen.fst')
  have hgroup := decide_eq' hs (encPort_group_polyTime hp)
  have hprefix := binary_lt' (SeededPredecessor.encContext_candidate_polyTime hc)
    (SeededPredecessor.encContext_edge_polyTime hc)
  exact ite' he.optionIsSome
    (decide_and hprefix hgroup) (const false)

end Turing.MultiTapeTM.RootPortFinish
