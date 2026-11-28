/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.RepeatedSquaring.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Tabulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Generating repeated Boolean squaring in logarithmic space

A generator enumerates the squarings, the matrix entries in each squaring, and the
intermediate vertex in each entry. It writes the binary wire numbers in program order.

## Main results

* `computableInLogSpace_iterate_squareGateList` emits all gate lines with a prescribed
  logspace relabeling of the wire addresses.

## References

The circuit is the Boolean matrix-powering construction of [Arora and Barak,
Chapter 6, Exercise 9(b–c), 2007 draft][AroraBarak07].
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInLogSpace

private abbrev Gate := Unbounded.Op × List ℕ
private abbrev gateEncoding := Circuit.encGate Unbounded.encOp

private theorem squareOutputWire_unary {α : Type} {enc : α ↪ List Bool} {N r i : α → ℕ}
    (hN : ComputableInLogSpace N enc encUnary) (hr : ComputableInLogSpace r enc encUnary)
    (hi : ComputableInLogSpace i enc encUnary) :
    ComputableInLogSpace (fun a => squareOutputWire (N a) (r a) (i a)) enc encUnary := by
  unfold squareOutputWire
  exact ite_decide (unaryEq hr (const 0)) hi (by fun_prop)

/-- Logspace generation of the gate list of repeated matrix squaring, after applying the
given wire numbering. Numerical dimensions, round counts and address arguments are unary.
The generated circuit lines use native operation tags and binary wire addresses. -/
theorem computableInLogSpace_iterate_squareGateList
    {N rounds : ℕ → ℕ} {wire : ℕ → ℕ → ℕ}
    (hN : ComputableInLogSpace N encUnary encUnary)
    (hr : ComputableInLogSpace rounds encUnary encUnary)
    (hw : ComputableInLogSpace (fun p : ℕ × ℕ => wire p.1 p.2) (encPair encUnary encUnary)
      encNat) :
    ComputableInLogSpace (fun n =>
      (List.ofFn fun r : Fin (rounds n) =>
        (squareGateList (N n) (N n * N n + r.val * (N n ^ 2 * (N n + 1)))
          (fun i => squareOutputWire (N n) r.val i.val)).map fun g =>
          (g.1, g.2.map (wire n))).flatten) encUnary
      (encList (Circuit.encGate Unbounded.encOp)) := by
  let andGate (n r o k : ℕ) : Gate :=
    (.and 2, [wire n (squareOutputWire (N n) r (k + N n * (o / N n))),
      wire n (squareOutputWire (N n) r (o % N n + N n * k))])
  let operand (n r o k : ℕ) := wire n
    (N n * N n + r * (N n ^ 2 * (N n + 1)) + o * (N n + 1) + k)
  let block (n r o : ℕ) :=
    ((List.range (N n)).map (andGate n r o)) ++
      [(Unbounded.Op.or (N n), (List.range (N n)).map (operand n r o))]
  let cells (n r : ℕ) := (List.range (N n * N n)).flatMap (block n r)
  let gates (n : ℕ) := (List.range (rounds n)).flatMap (cells n)
  have hwire {α : Type} {enc : α ↪ List Bool} {a i : α → ℕ}
      (ha : ComputableInLogSpace a enc encUnary) (hi : ComputableInLogSpace i enc encUnary) :
      ComputableInLogSpace (fun x => wire (a x) (i x)) enc encNat :=
    hw.comp' (pair ha hi)
  have hand {α : Type} {enc : α ↪ List Bool} {n r o k : α → ℕ}
      (hn : ComputableInLogSpace n enc encUnary) (hr : ComputableInLogSpace r enc encUnary)
      (ho : ComputableInLogSpace o enc encUnary) (hk : ComputableInLogSpace k enc encUnary) :
      ComputableInLogSpace (fun a => andGate (n a) (r a) (o a) (k a)) enc gateEncoding := by
    have h := hN.comp' hn
    dsimp only [andGate]
    apply pair (const (Unbounded.Op.and 2))
    apply listCons (hwire hn (squareOutputWire_unary h hr (by fun_prop)))
    exact listCons (hwire hn (squareOutputWire_unary h hr (by fun_prop))) (const [])
  have hoperand {α : Type} {enc : α ↪ List Bool} {n r o k : α → ℕ}
      (hn : ComputableInLogSpace n enc encUnary) (hr : ComputableInLogSpace r enc encUnary)
      (ho : ComputableInLogSpace o enc encUnary) (hk : ComputableInLogSpace k enc encUnary) :
      ComputableInLogSpace (fun a => operand (n a) (r a) (o a) (k a)) enc encNat := by
    have h := hN.comp' hn
    exact hwire hn (by fun_prop)
  let enc₁ := encPair encUnary encUnary
  let enc₂ := encPair enc₁ encUnary
  have n₁ := fst encUnary encUnary
  have r₁ := snd encUnary encUnary
  have n₂ := n₁.comp' (fst enc₁ encUnary)
  have r₂ := r₁.comp' (fst enc₁ encUnary)
  have o₂ := snd enc₁ encUnary
  have n₃ := n₂.comp' (fst enc₂ encUnary)
  have r₃ := r₂.comp' (fst enc₂ encUnary)
  have o₃ := o₂.comp' (fst enc₂ encUnary)
  have k₃ := snd enc₂ encUnary
  have hblock : ComputableInLogSpace (fun p : (ℕ × ℕ) × ℕ => block p.1.1 p.1.2 p.2)
      enc₂ (encList gateEncoding) := by
    have hN₂ := hN.comp' n₂
    have hop : ComputableInLogSpace
        (fun p : (ℕ × ℕ) × ℕ => Unbounded.Op.or (N p.1.1)) enc₂ Unbounded.encOp :=
      (unaryAdd (unaryMul (const 2) hN₂) (const 2)).congr fun _ => rfl
    have coords : UnaryTupleEncoding enc₂ := .pair (.pair .unary .unary) .unary
    exact listAppend (map_range coords hN₂ (hand n₃ r₃ o₃ k₃))
      (listCons (pair hop (map_range coords hN₂ (hoperand n₃ r₃ o₃ k₃))) (const []))
  have hcells : ComputableInLogSpace (fun p : ℕ × ℕ => cells p.1 p.2) enc₁
      (encList gateEncoding) :=
    (listFlatten gateEncoding).comp'
      (map_range (.pair .unary .unary) (unaryMul (hN.comp' n₁) (hN.comp' n₁)) hblock)
  have hgates : ComputableInLogSpace gates encUnary (encList gateEncoding) :=
    (listFlatten gateEncoding).comp' (map_range .unary hr hcells)
  apply hgates.congr_fun
  intro n
  simp only [gates, cells, block, andGate, operand, List.flatMap, List.map_range_eq_ofFn,
    squareGateList, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_append,
    List.map_cons, List.map_nil]
  rfl

end Cslib.Circuits.Boolean
