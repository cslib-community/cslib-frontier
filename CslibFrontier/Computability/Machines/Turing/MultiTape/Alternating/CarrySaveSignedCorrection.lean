/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafATM
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedRouting
public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Signed.Correction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.MapOutput

/-!
# Native signed correction on persistent carry-save tapes

One finite machine family implements all five correction ports of the signed product gate.
It starts on the actual controller storage, writes the carry flag, rewinds and serializes the
physical fields, and checks the requested Boolean claim. Padded bit-index words are normalized
by the native predicate. The context, count and width words are charged linearly; only the
bounded path and bit-index lengths occur under a fixed polynomial.

The resulting `LeafBound` and `LeafCorrect` contracts have no operand-access premise. The two
operand ports remain the separate recursive continuations of `ReducedProduct.exists_evaluator`.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveSignedCorrection

open Polynomial MultiTapeTM Cslib.CountingLeaf Cslib.ConvolutionOperand.Signed
open Cslib.Circuits.Frontier.FastContraction

private noncomputable def claimRunner {k : ℕ} {S : Type} (runner : MultiTapeTM (k + 2) Bool S)
    (claim : Bool) : MultiTapeATM (k + 2) Bool S :=
  ofTMs (fun _ => runner.mapOutput (fun answer => answer == claim)) (fun _ => false)

private theorem claimRunner_spec {k : ℕ} {S : Type} (runner : MultiTapeTM (k + 2) Bool S)
    (host word : List Bool) (answer claim : Bool) (time : ℕ)
    (hr : runner.runFrom ((WorkTapePredicate.config host word).withState (some runner.q₀))
      time = (WorkTapePredicate.config host word [answer]).withState none) :
    let start := (WorkTapePredicate.config host word).withState
      (some (claimRunner runner claim).toPTM.initial)
    (claimRunner runner claim).HaltsWithin time start ∧
      ((claimRunner runner claim).AcceptsWithin time start ↔ answer = claim) := by
  have hm := runFrom_mapOutput runner (fun a => a == claim)
    ((WorkTapePredicate.config host word).withState (some runner.q₀)) time
  have hi :
      ((WorkTapePredicate.config (k := k) host word).withState (some runner.q₀)).mapOutput
        (fun a => a == claim) =
      (WorkTapePredicate.config host word).withState (some runner.q₀) := rfl
  rw [hi, hr] at hm
  constructor
  · rw [claimRunner, haltsWithin_ofTMs_const_iff]
    change ((runner.mapOutput (fun a => a == claim)).runFrom
      ((WorkTapePredicate.config host word).withState (some runner.q₀)) time).state = none
    rw [hm]
    rfl
  · rw [claimRunner, acceptsWithin_ofTMs_const_iff]
    change (((runner.mapOutput (fun a => a == claim)).runFrom
      ((WorkTapePredicate.config host word).withState (some runner.q₀)) time).state = none ∧
      ((runner.mapOutput (fun a => a == claim)).runFrom
        ((WorkTapePredicate.config host word).withState (some runner.q₀)) time).output = [true]) ↔ _
    rw [hm]
    simp [Cfg.mapOutput, WorkTapePredicate.config, tapesCfg, Cfg.withState]

private theorem prepare_le (c d B : ℕ) (context count width path bits : List Bool)
    (carry : Bool) (hb : path.length + bits.length ≤ B) :
    let q := CarrySaveLeaf.query context count width path bits carry
    path.length + 3 + (2 * (encRawInput q).length + 5) +
        c * (q.context.length + q.count.length + q.width.length +
          (q.path.length + q.bit.length + 2) ^ d + 1) ≤
      (c + 30) * (context.length + count.length + width.length + (B + 2) ^ (d + 1) + 1) := by
  intro q
  have hl := length_encRawInput_le q B hb
  have hp : (path.length + bits.length + 2) ^ d ≤ (B + 2) ^ (d + 1) :=
    (Nat.pow_le_pow_left (by omega) d).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ d))
  have hs : B + 2 ≤ (B + 2) ^ (d + 1) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (show 0 < B + 2 by omega) (show 1 ≤ d + 1 by omega)
  have hc := Nat.mul_le_mul_left c (Nat.add_le_add_right
    (Nat.add_le_add_left hp (context.length + count.length + width.length)) 1)
  dsimp only [q, CarrySaveLeaf.query] at hl ⊢
  rw [Nat.add_mul]
  omega

/-- A uniform finite family implements every correction port on the physical leaf storage.
All raw fields, including padded counters, are allowed. The five correction ports use the same
machine, independent of both polynomial operands and all product parameters. The two operand
ports are excluded explicitly. Preparation and native predicate evaluation are fully charged. -/
theorem exists_leaves :
    ∃ (k : ℕ) (Q : Type) (_ : Finite Q)
      (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool Q) (C d : ℕ),
      ∀ (input context count width : List Bool) (B : ℕ),
        let time := C * (context.length + count.length + width.length + (B + 2) ^ d + 1)
        let scratch := CarrySaveLeaf.scratch k context count width
        CarrySaveStream.LeafBound leaf time B input scratch ∧
          ∀ {p : ℕ} (u v : (ZMod (2 ^ p))[X]) (q i : ℕ) (j : Fin 7),
            j ≠ 0 → j ≠ 1 →
              CarrySaveStream.LeafCorrect (signedPorts u v q i j) leaf time B input scratch := by
  obtain ⟨d, hd⟩ := computableInO_rawCorrection
  obtain ⟨k, S, hS, runner, c, hr⟩ := WorkTapePredicate.exists_of_inO hd
  let := hS
  let leaf := fun carry claim => CarrySaveLeafATM.machine (claimRunner runner claim) carry
  refine ⟨k, _, inferInstance, leaf, c + 30, d + 1, ?_⟩
  intro input context count width B time scratch
  have hphysical (height bits path unary : List Bool) (frontier : ℤ)
      (status carry claim : Bool) (hb : height.length + bits.length + path.length ≤ B) :
      let cfg := (CarrySaveLeaf.initial k input context count width height bits path unary
        frontier status).withState (some (leaf carry claim).toPTM.initial)
      (leaf carry claim).HaltsWithin time cfg ∧
        ((leaf carry claim).AcceptsWithin time cfg ↔
          rawCorrection (CarrySaveLeaf.query context count width path bits carry) = claim) := by
    let x := CarrySaveLeaf.query context count width path bits carry
    let t := c * (x.context.length + x.count.length + x.width.length +
      (x.path.length + x.bit.length + 2) ^ d + 1)
    obtain ⟨hh, ha⟩ := claimRunner_spec runner input (encRawInput x) (rawCorrection x)
      claim t (hr x input)
    obtain ⟨hs, he⟩ := CarrySaveLeafATM.spec (claimRunner runner claim) input context count
      width height bits path unary frontier status carry t hh
    have hclock := prepare_le c d B context count width path bits carry (by omega)
    change path.length + 3 + (2 * (encRawInput x).length + 5) + t ≤ time at hclock
    refine ⟨hs.mono hclock, ⟨?_, ?_⟩⟩
    · intro h
      exact ha.mp (he.mp (h.of_halted_stepCoins hs))
    · intro h
      exact (he.mpr (ha.mpr h)).mono hclock
  constructor
  · intro height bits path unary frontier status carry claim _ hb
    exact (hphysical height bits path unary frontier status carry claim hb).1
  · intro p u v q i j hj₀ hj₁ height bits path unary frontier status carry claim _ hb hbit
    have h := (hphysical height bits path unary frontier status carry claim hb).2
    have he : rawCorrection (CarrySaveLeaf.query context count width path bits carry) =
        Cslib.Circuits.Boolean.CarrySaveQuery.value (signedPorts u v q i j)
          ⟨path, 0, carry, Cslib.BitString.lsbValue bits⟩ := by
      rw [value_port u v q i j path ⟨Cslib.BitString.lsbValue bits, hbit⟩ carry]
      simp only [signedBit, hj₀, hj₁, ↓reduceIte, rawCorrection, CarrySaveLeaf.query,
        correction, ofBits_eq_lsbValue]
      rfl
    exact h.trans (by rw [he])

end Turing.MultiTapeATM.CarrySaveSignedCorrection
