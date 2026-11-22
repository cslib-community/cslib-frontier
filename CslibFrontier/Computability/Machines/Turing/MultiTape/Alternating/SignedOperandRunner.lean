/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafATM
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WorkTapeFamily
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.SignedOperandRequest
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedRouting

/-!
# Native continuations for the two signed operand ports

For either operand side, one finite family handles both component selectors and both bit claims.
It starts on the persistent carry-save tapes, serializes the actual local query, computes its
signed operand address, and either returns the zero-padding verdict or transfers control to the
supplied operand machine. The child clock is added once. Preparation is linear in the protected
payload and polynomial only in local word lengths and binary product indices.

The protected context tape has the explicit `SignedOperandRequest.encContext` representation;
the other physical words may be arbitrary. This module implements the routing and call, while
constructing the recursive operand machine remains part of #4728.
-/

public section

namespace Turing.MultiTapeATM.SignedOperandRunner

open MultiTapeTM SignedOperandRequest
open Cslib.ConvolutionOperand hiding Input encInput
open Polynomial Cslib.Circuits.Frontier.FastContraction

private theorem setup_le (x : Input) (n a l d D B : ℕ)
    (hn : n ≤ l * (x.context.payload.length + shortSize x ^ d + 1))
    (hd : d ≤ D) (hD : 1 ≤ D) (hb : a + 2 * l + 56 ≤ B) :
    x.path.length + 3 + (2 * (encInput x).length + 5) +
        (a * (x.context.payload.length + shortSize x ^ d + 1) + (2 * n + 16)) ≤
      B * (x.context.payload.length + shortSize x ^ D + 1) := by
  let size := x.context.payload.length + shortSize x ^ D + 1
  have hpos : 0 < shortSize x := by simp [shortSize]
  have hp := Nat.pow_le_pow_right hpos hd
  have hshort : shortSize x ≤ shortSize x ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos hD
  have hm : x.context.payload.length + shortSize x ^ d + 1 ≤ size := by
    dsimp only [size]
    omega
  have hlen := encInput_length_le x
  have hpath : x.path.length ≤ shortSize x := by unfold shortSize; omega
  have hprepare : x.path.length + 3 + (2 * (encInput x).length + 5) ≤ 40 * size := by
    dsimp only [size]
    omega
  have hlocal : a * (x.context.payload.length + shortSize x ^ d + 1) + (2 * n + 16) ≤
      (a + 2 * l + 16) * size := by
    have ha := Nat.mul_le_mul_left a hm
    have hl := hn.trans (Nat.mul_le_mul_left l hm)
    have hs : 1 ≤ size := by dsimp [size]; omega
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    omega
  calc
    _ ≤ 40 * size + (a + 2 * l + 16) * size := Nat.add_le_add hprepare hlocal
    _ = (a + 2 * l + 56) * size := by ring
    _ ≤ B * size := Nat.mul_le_mul_right size hb

/-- Starting from the physical carry-save leaf storage, prepare and invoke the requested
operand continuation. Padding returns the zero-bit claim without any child-halting premise.
The protected payload is charged linearly and the child run appears once in the clock. -/
theorem exists_runner {K : ℕ} {S : Type} [Finite S] (right : Bool) (src : Fin K)
    (child : MultiTapeATM K Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C d : ℕ), ∀ (host : List Bool) (x : Input) (height unary : List Bool) (frontier : ℤ)
        (status claim : Bool) (t : ℕ),
        let target := SharedWordFork.start src child host (encRequest (request right claim x)) 0
        let atm := leaf x.carry claim
        let start := (CarrySaveLeaf.initial a host (encContext x.context) x.count x.width
          height x.bit x.path unary frontier status).withState (some atm.toPTM.initial)
        let time := C * (x.context.payload.length + shortSize x ^ d + 1) + t
        ((Signed.source (query right x)).isSome = true → child.HaltsWithin t target) →
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            if (Signed.source (query right x)).isSome then child.AcceptsWithin t target
            else (!claim) = true) := by
  classical
  choose d hd using exists_word_inO right
  choose l hl using fun b => (hd b).length_le_time
  let cost (b : Bool) (x : Input) := x.context.payload.length + shortSize x ^ d b
  have guarded (b : Bool) := GuardedWord.exists_guarded_runner src child
    (fun x => (Signed.source (query right x)).isSome) (fun _ => !b)
    (fun x => encRequest (request right b x)) (cost b) (hd b)
  choose u R hR runner A hr using guarded
  let : ∀ b, Finite (R b) := hR
  obtain ⟨a, Q, hQ, family, hf⟩ := WorkTapeFamily.exists_family u R runner
  let := hQ
  let D := max 1 (max (d false) (d true))
  let coeff (b : Bool) := A b + 2 * l b + 56
  let B := max (coeff false) (coeff true)
  refine ⟨a, _, inferInstance, fun carry b => CarrySaveLeafATM.machine (family b) carry,
    B, D, ?_⟩
  intro host x height unary frontier status b t target atm start time hchild
  let w := encRequest (request right b x)
  let n := A b * (cost b x + 1) + (2 * w.length + 16) + t
  obtain ⟨hh, ha⟩ := hr b host x t hchild
  have hs := hf b host (encInput x) n
  obtain ⟨hhalt, hacc⟩ := CarrySaveLeafATM.spec (family b) host (encContext x.context)
    x.count x.width height x.bit x.path unary frontier status x.carry n (hs.1.mpr hh)
  have hlen := hl b x
  simp only [encBits_apply, word, List.length_append] at hlen
  have hn : w.length ≤ l b * (x.context.payload.length + shortSize x ^ d b + 1) := by
    change 3 + w.length ≤ _ at hlen
    omega
  have hD : d b ≤ D := by
    refine le_trans ?_ (Nat.le_max_right 1 _)
    cases b <;> first | apply Nat.le_max_left | apply Nat.le_max_right
  have hB : coeff b ≤ B := by cases b <;> first | apply Nat.le_max_left | apply Nat.le_max_right
  have hb := setup_le x w.length (A b) (l b) (d b) D B hn hD (Nat.le_max_left ..) hB
  have hclock : x.path.length + 3 + (2 * (encInput x).length + 5) + n ≤ time := by
    dsimp only [time, n, cost]
    omega
  refine ⟨hhalt.mono hclock, ⟨?_, ?_⟩⟩
  · intro h
    exact ha.mp (hs.2.mp (hacc.mp (h.of_halted_stepCoins hhalt)))
  · intro h
    exact (hacc.mpr (hs.2.mpr (ha.mpr h))).mono hclock

/-- The physical operand runner supplies the leaf contracts used by the streamed signed
product. Its continuation premises concern only enabled, bounded physical requests. Both the
linear context charge and the single child runtime are retained by the uniform leaf clock. -/
theorem exists_leaves {K : ℕ} {S : Type} [Finite S] (right : Bool) (src : Fin K)
    (child : MultiTapeATM K Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C d : ℕ), ∀ (host : List Bool) (ctx : Context) (count width : List Bool) (B t : ℕ),
        (∀ (path bits : List Bool) (carry claim : Bool), path.length + bits.length ≤ B →
          let x : Input := ⟨ctx, count, width, path, carry, bits⟩
          let target := SharedWordFork.start src child host (encRequest (request right claim x)) 0
          (Signed.source (query right x)).isSome = true → child.HaltsWithin t target) →
        let size := ctx.half.size + ctx.index.size + count.length + width.length + B + 1
        let time := C * (ctx.payload.length + size ^ d + 1) + t
        let scratch := CarrySaveLeaf.scratch a (encContext ctx) count width
        CarrySaveStream.LeafBound leaf time B host scratch ∧
          ∀ {p : ℕ} (u v : (ZMod (2 ^ p))[X]), ofBits width = p →
            (∀ (path bits : List Bool) (carry claim : Bool), path.length + bits.length ≤ B →
              let x : Input := ⟨ctx, count, width, path, carry, bits⟩
              let r := request right claim x
              let target := SharedWordFork.start src child host (encRequest r) 0
              (Signed.source (query right x)).isSome = true →
                (child.AcceptsWithin t target ↔
                  (if r.right then (v.coeff r.coefficient).val else
                    (u.coeff r.coefficient).val).testBit r.bit = r.claim)) →
            CarrySaveStream.LeafCorrect
              (signedPorts u v ctx.half ctx.index (if right then 1 else 0))
              leaf time B host scratch := by
  obtain ⟨a, Q, hQ, leaf, C, d, h⟩ := exists_runner right src child
  refine ⟨a, Q, hQ, leaf, C, d, ?_⟩
  intro host ctx count width B t hchild size time scratch
  have hphysical (height bits path unary : List Bool) (frontier : ℤ)
      (status carry claim : Bool) (hb : height.length + bits.length + path.length ≤ B) :
      let x : Input := ⟨ctx, count, width, path, carry, bits⟩
      let target := SharedWordFork.start src child host (encRequest (request right claim x)) 0
      let cfg := (CarrySaveLeaf.initial a host (encContext ctx) count width
        height bits path unary frontier status).withState (some (leaf carry claim).toPTM.initial)
      (leaf carry claim).HaltsWithin time cfg ∧ ((leaf carry claim).AcceptsWithin time cfg ↔
        if (Signed.source (query right x)).isSome then child.AcceptsWithin t target
        else (!claim) = true) := by
    intro x target cfg
    have hs := h host x height unary frontier status claim t
      (hchild path bits carry claim (by omega))
    have hsize : shortSize x ≤ size := by dsimp [shortSize, x, size]; omega
    have hclock : C * (x.context.payload.length + shortSize x ^ d + 1) + t ≤ time := by
      dsimp only [time]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left C
        (Nat.add_le_add_right (Nat.add_le_add_left (Nat.pow_le_pow_left hsize d) _) 1)) t
    refine ⟨hs.1.mono hclock, ⟨?_, ?_⟩⟩
    · intro ha
      exact hs.2.mp (ha.of_halted_stepCoins hs.1)
    · intro ha
      exact (hs.2.mpr ha).mono hclock
  constructor
  · intro height bits path unary frontier status carry claim _ hb
    exact (hphysical height bits path unary frontier status carry claim hb).1
  · intro p u v hwidth hvalue height bits path unary frontier status carry claim _ hb hbit
    let x : Input := ⟨ctx, count, width, path, carry, bits⟩
    have hg := (hphysical height bits path unary frontier status carry claim hb).2
    have he : (if (Signed.source (query right x)).isSome then
        child.AcceptsWithin t (SharedWordFork.start src child host
          (encRequest (request right claim x)) 0) else (!claim) = true) ↔
          signedRead u v (query right x) = claim := by
      cases hs : Signed.source (query right x) with
      | none => cases claim <;> simp [signedRead, hs]
      | some coordinate =>
        have hen : (Signed.source (query right x)).isSome = true := by simp [hs]
        have hc := hvalue path bits carry claim (by omega) hen
        have hright (y : Input) : (query right y).right = right := rfl
        simp only [x] at hs
        simpa only [signedRead, request, x, hs, hright, Option.getD_some, Option.elim_some,
          Option.isSome_some, ↓reduceIte] using hc
    have hv : signedRead u v (query right x) =
        Cslib.Circuits.Boolean.CarrySaveQuery.value
          (signedPorts u v ctx.half ctx.index (if right then 1 else 0))
          ⟨path, 0, carry, Cslib.BitString.lsbValue bits⟩ := by
      rw [value_port u v ctx.half ctx.index (if right then 1 else 0) path
        ⟨Cslib.BitString.lsbValue bits, hbit⟩ carry]
      cases right <;> simp [signedBit, query, x, hwidth, ofBits_eq_lsbValue]
    exact hg.trans (he.trans (by rw [hv]))

end Turing.MultiTapeATM.SignedOperandRunner
