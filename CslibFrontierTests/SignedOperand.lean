/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SignedOperandRunner

open Turing Turing.MultiTapeTM Turing.MultiTapeATM SignedOperandRequest
open Cslib.ConvolutionOperand hiding Input encInput
open Polynomial
open Cslib.Circuits.Frontier.FastContraction (signedPorts)

private def sample (payload : List Bool) : Input :=
  ⟨⟨payload, 2, 1⟩, [true, false, true], [true, true, false, false],
    [false, false, false, true, false, false], false, [false, true, false]⟩

-- The six raw fields have exactly the serializer's existing framed layout.
example (x : Input) : encInput x = Cslib.CountingLeaf.encRawInput
    ⟨encContext x.context, x.count, x.width, x.path, x.carry, x.bit⟩ := encInput_eq x

-- Padded numeric words are normalized, while a potentially long payload is not inspected.
example (payload : List Bool) : Signed.source (query false (sample payload)) = some (1, 2) := by
  dsimp only [query, sample]
  decide

example (payload : List Bool) : Signed.source (query true (sample payload)) = some (0, 0) := by
  dsimp only [query, sample]
  decide

example (payload : List Bool) : request false true (sample payload) =
    ⟨payload, false, 1, 2, true⟩ := by
  have h : Signed.source (query false (sample payload)) = some (1, 2) := by
    dsimp only [query, sample]
    decide
  simp only [request, h, Option.getD_some]
  rfl

example (payload : List Bool) : request true false (sample payload) =
    ⟨payload, true, 0, 0, false⟩ := by
  have h : Signed.source (query true (sample payload)) = some (0, 0) := by
    dsimp only [query, sample]
    decide
  simp only [request, h, Option.getD_some]
  rfl

-- At the shift boundary the source is present; increasing that same shift by one disables it.
example (payload : List Bool) : Signed.source (query false
    {sample payload with path := [false, false, false, true, true, false]}) = some (1, 0) := by
  dsimp only [query, sample]
  decide

example (payload : List Bool) : Signed.source (query false
    {sample payload with path := [false, false, false, true, true, true]}) = none := by
  dsimp only [query, sample]
  decide

-- The unused fourth diagonal and zero precision make no operand request.
example (payload : List Bool) : Signed.source (query true
    {sample payload with path := [true, true, false, true, false, false]}) = none := rfl

example (payload : List Bool) : Signed.source (query false
    {sample payload with width := []}) = none := by
  dsimp only [query, sample]
  decide

-- A negative diagonal still routes to the actual operand coordinates, before the separate
-- correction port supplies the two's-complement adjustment.
example (payload : List Bool) : Signed.source (query true
    {sample payload with
      context := ⟨payload, 2, 0⟩
      path := [false, true, true, false, false, true]}) = some (2, 1) := by
  dsimp only [query, sample]
  decide

-- This physical caller works for an arbitrary child, with no halting assumption about it.
-- The carry component has no operand source, so its clock contains no child runtime.
example {K : ℕ} {S : Type} [Finite S] (right : Bool) (src : Fin K)
    (child : MultiTapeATM K Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C d : ℕ), ∀ (host : List Bool) (x : Input) (height unary : List Bool) (frontier : ℤ)
        (status claim : Bool), x.carry = true →
        let atm := leaf true claim
        let start := (CarrySaveLeaf.initial a host (encContext x.context) x.count x.width
          height x.bit x.path unary frontier status).withState (some atm.toPTM.initial)
        let time := C * (x.context.payload.length + shortSize x ^ d + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ claim = false) := by
  obtain ⟨a, Q, hQ, leaf, C, d, h⟩ := SignedOperandRunner.exists_runner right src child
  refine ⟨a, Q, hQ, leaf, C, d, ?_⟩
  intro host x height unary frontier status claim hcarry
  have hz : Signed.source (query right x) = none := by
    simp [Signed.source, query, Signed.ordinary, unpack, run, active, hcarry]
  have hr := h host x height unary frontier status claim 0 (by simp [hz])
  simpa [hz, hcarry] using hr

-- At half-degree zero all routes are padding. This checks the actual LeafBound/LeafCorrect
-- interface for every physical component, at any positive precision as well as precision zero,
-- while retaining an arbitrary child machine and arbitrary padded width words.
example {K : ℕ} {S : Type} [Finite S] (right : Bool) (src : Fin K)
    (child : MultiTapeATM K Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C d : ℕ), ∀ (host payload : List Bool) (index : ℕ) (count width : List Bool) (B : ℕ),
        let ctx : Context := ⟨payload, 0, index⟩
        let time := C * (payload.length +
          (index.size + count.length + width.length + B + 1) ^ d + 1)
        let scratch := CarrySaveLeaf.scratch a (encContext ctx) count width
        CarrySaveStream.LeafBound leaf time B host scratch ∧
          ∀ {p : ℕ} (u v : (ZMod (2 ^ p))[X]), ofBits width = p →
            CarrySaveStream.LeafCorrect
              (signedPorts u v 0 index (if right then 1 else 0)) leaf time B host scratch := by
  obtain ⟨a, Q, hQ, leaf, C, d, h⟩ := SignedOperandRunner.exists_leaves right src child
  refine ⟨a, Q, hQ, leaf, C, d, ?_⟩
  intro host payload index count width B ctx time scratch
  have hz (path bits : List Bool) (carry : Bool) :
      Signed.source (query right ⟨ctx, count, width, path, carry, bits⟩) = none := by
    simp [Signed.source, query, ctx, Signed.ordinary, unpack, run, active]
  have hs := h host ctx count width B 0 (by
    intro path bits carry claim _
    dsimp only
    intro hen
    change (Signed.source (query right ⟨ctx, count, width, path, carry, bits⟩)).isSome = true at hen
    simp only [hz, Option.isSome_none, Bool.false_eq_true] at hen)
  constructor
  · simpa [ctx, time, scratch] using hs.1
  · intro p u v hwidth
    have hc := hs.2 u v hwidth (by
      intro path bits carry claim _
      dsimp only
      intro hen
      change (Signed.source (query right ⟨ctx, count, width, path, carry, bits⟩)).isSome = true
        at hen
      simp only [hz, Option.isSome_none, Bool.false_eq_true] at hen)
    simpa [ctx, time, scratch] using hc
