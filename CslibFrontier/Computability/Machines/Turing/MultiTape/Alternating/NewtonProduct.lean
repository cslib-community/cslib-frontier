/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct.Input
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.NewtonProductRequest
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# The native product branch of Newton inversion

One finite machine handles both kinds of Newton multiplication node. It computes the selected
predecessor stage from the actual operand request, preserves the coefficient-bit claim, and
passes that request to the supplied recursive machine. The signed product compiler supplies all
seven arithmetic ports. The predecessor stage is strictly smaller, and the recursive time is
added once. The opaque enclosing context remains outside every polynomial arithmetic budget.

`exists_evaluator` starts with one encoded request on a work tape and constructs every internal
product field. Its clock is linear in the enclosing payload and polynomial in the binary stage
and product metadata, plus one recursive call. The residue and correction branches and the
common recursive controller remain part of #4728.
-/

public section

namespace Turing.MultiTapeATM.NewtonProduct

open MultiTapeTM Cslib GaloisRingArith
open Cslib.Circuits.Frontier.FastContraction NewtonProductRequest

private theorem value_product (m p : ℕ) (x : List ℕ) (node : NewtonQuery.Node)
    (h : NewtonQuery.operation node = 2) :
    NewtonQuery.value m p x node =
      NewtonQuery.value m p x (NewtonQuery.child node false) *
        NewtonQuery.value m p x (NewtonQuery.child node true) := by
  cases node with
  | input => simp [NewtonQuery.operation] at h
  | factor _ => simp [NewtonQuery.operation] at h
  | product k => simp [NewtonQuery.value, NewtonQuery.child]
  | iterate k =>
    cases k with
    | zero => simp [NewtonQuery.operation] at h
    | succ k => simpa [NewtonQuery.value, NewtonQuery.child] using NewtonQuery.iterate_succ m p x k

private theorem exists_router {N : ℕ} {S : Type} [Finite S] (src : Fin N)
    (child : MultiTapeATM N Bool S) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM (u + 2) Bool Q) (C d : ℕ),
      ∀ (input : List Bool) (a : Input) (t : ℕ),
        let target := SharedWordFork.start src child input (encQuery (request a)) 0
        let start := SharedWordFork.start (Fin.natAdd u 0) atm input (encInput a) 0
        let time := C * (a.context.payload.length + shortSize a ^ d + 1) + t
        child.HaltsWithin t target → atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ child.AcceptsWithin t target) := by
  obtain ⟨d, hd⟩ := exists_word_inO
  obtain ⟨l, hl⟩ := hd.length_le_time
  obtain ⟨u, Q, hQ, atm, c, h⟩ := GuardedWord.exists_guarded_runner src child
    (fun _ : Input => true) (fun _ => false) (fun a => encQuery (request a))
    (fun a => a.context.payload.length + shortSize a ^ d) hd
  refine ⟨u, Q, hQ, atm, c + 2 * l + 16, d, ?_⟩
  intro input a t target start time hh
  have hs := h input a t (fun _ => hh)
  have hlen := hl a
  simp only [encBits_apply, word, List.length_append, List.length_cons, List.length_nil] at hlen
  have hclock : c * (a.context.payload.length + shortSize a ^ d + 1) +
      (2 * (encQuery (request a)).length + 16) + t ≤ time := by
    have hpos : 1 ≤ a.context.payload.length + shortSize a ^ d + 1 := by omega
    have hx := Nat.mul_le_mul_left 2 hlen
    have h16 := Nat.mul_le_mul_left 16 hpos
    simp only [Nat.mul_add, Nat.mul_one] at hx h16
    dsimp only [time]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    omega
  have hstart : start =
      (WorkTapePredicate.config input (encInput a)).withState (some atm.toPTM.initial) :=
    SharedWordFork.start_eq_workTape atm input (encInput a)
  rw [hstart]
  simp only [↓reduceIte] at hs
  refine ⟨hs.1.mono hclock, ⟨?_, ?_⟩⟩
  · intro ha
    exact hs.2.mp (ha.of_halted_stepCoins hs.1)
  · intro ha
    exact (hs.2.mpr ha).mono hclock

private theorem clock_bound (A D Cr dr : ℕ) :
    ∃ C E, ∀ (payload : List Bool) (stage : ℕ) (a : ReducedProductRequest.Metadata),
      A * ((encContext ⟨payload, stage⟩).length +
        ((ReducedProductRequest.encMetadata a).length + 1) ^ D + 1) +
        Cr * (payload.length +
          (stage.size + (2 * 3 ^ modulusExp a.scale).size + a.precision.size + 1) ^ dr + 1) ≤
      C * (payload.length +
        (stage.size + (ReducedProductRequest.encMetadata a).length + 1) ^ E + 1) := by
  let size (v : ℕ × ReducedProductRequest.Metadata) :=
    v.1.size + (ReducedProductRequest.encMetadata v.2).length + 1
  have hmeta : PolyBounded size
      (fun v : ℕ × ReducedProductRequest.Metadata =>
        (ReducedProductRequest.encMetadata v.2).length) :=
    PolyBounded.self.mono (fun _ => by dsimp [size]; omega)
  have hstage : PolyBounded size (fun v : ℕ × ReducedProductRequest.Metadata => v.1.size) :=
    PolyBounded.self.mono (fun _ => by dsimp [size]; omega)
  have hh := (ResidueInverse.half_polyTime.comp
    ReducedProductRequest.encMetadata_scale_deg.computableInPolyTime).polyBounded_length.comp hmeta
  have hhalf : PolyBounded size
      (fun v : ℕ × ReducedProductRequest.Metadata => 3 ^ modulusExp v.2.scale) := by
    simpa only [encUnary_apply, List.length_replicate, Function.comp_apply] using hh
  have hp : PolyBounded size
      (fun v : ℕ × ReducedProductRequest.Metadata => v.2.precision.size) := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using
      ReducedProductRequest.encMetadata_precision_deg.computableInPolyTime.polyBounded_length.comp
        hmeta
  have hroute := (((hstage.add ((PolyBounded.const 2).mul hhalf |>.mono
    (fun _ => Nat.size_le_self _))).add hp).add (.const 1)).pow dr
  let extra (v : ℕ × ReducedProductRequest.Metadata) :=
    A * (v.1.size + ((ReducedProductRequest.encMetadata v.2).length + 1) ^ D + 2) +
      Cr * ((v.1.size + (2 * 3 ^ modulusExp v.2.scale).size + v.2.precision.size + 1) ^ dr + 1)
  have he : PolyBounded size extra :=
    ((PolyBounded.const A).mul
      ((hstage.add ((hmeta.add (.const 1)).pow D)).add (.const 2))).add
        ((PolyBounded.const Cr).mul (hroute.add (.const 1)))
  have he' := he.comp (g := fun v : List Bool × ℕ × ReducedProductRequest.Metadata => v.2)
    PolyBounded.self
  obtain ⟨C, E, hbound⟩ := he'.exists_le_linear_add_pow
    (fun v => v.1.length) (2 * A + Cr) (fun _ => by dsimp [size]; omega)
  refine ⟨C, E, fun payload stage a => ?_⟩
  have h := hbound (payload, stage, a)
  simp only [encContext_apply, encContextFields, length_encPair, encBits_apply,
    encNat_apply, Nat.size_eq_bits_len]
  dsimp only [size, extra] at h
  nlinarith

/-- The actual finite product branch for Newton's shared iterates, from one encoded request.
The compiler derives the physical product layout itself. The recursive child receives only the
selected smaller predecessor and coefficient-bit claim. All routing and copying is charged;
the payload remains outside the polynomial and the recursive clock is added once. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S] (src : Fin N)
    (child : MultiTapeATM N Bool S) :
    ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM K Bool Q) (C D : ℕ),
      ∀ (input payload : List Bool) (m p t : ℕ) (x : List ℕ) (node : NewtonQuery.Node)
        (_ : NewtonQuery.operation node = 2) (i : Fin (modulus m).length),
        (∀ (right : Bool) (coefficient : Fin (2 * 3 ^ modulusExp m))
          (bit : Fin p) (claim : Bool),
          let req : Query := ⟨payload, NewtonQuery.address (NewtonQuery.child node right),
            coefficient.val, bit.val, claim⟩
          let target := SharedWordFork.start src child input (encQuery req) 0
          child.HaltsWithin t target ∧ (child.AcceptsWithin t target ↔
            ((representative m p (NewtonQuery.value m p x (NewtonQuery.child node right))).coeff
              coefficient.val).val.testBit bit.val = claim)) →
        ∀ (bit : Fin p) (claim : Bool),
          let a : ReducedProductRequest.Input :=
            ⟨encContext ⟨payload, NewtonQuery.address node⟩, ⟨m, p, i.val, bit.val, claim⟩⟩
          let start := SharedWordFork.start source atm input (ReducedProductRequest.encInput a) 0
          let time := C * (payload.length + ((NewtonQuery.address node).size +
            (ReducedProductRequest.encMetadata a.metadata).length + 1) ^ D + 1) + t
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ((representative m p (NewtonQuery.value m p x node)).coeff i.val).val.testBit bit.val =
              claim) := by
  obtain ⟨u, R, hR, router, Cr, dr, hr⟩ := exists_router src child
  let := hR
  obtain ⟨K, source, Q, hQ, atm, A, D, h⟩ :=
    ReducedProduct.Input.exists_evaluator (Fin.natAdd u 0) router
  obtain ⟨C, E, hclock⟩ := clock_bound A D Cr dr
  refine ⟨K, source, Q, hQ, atm, C, E, ?_⟩
  intro input payload m p t x node hnode i hchild bit claim a start time
  let q := 3 ^ modulusExp m
  let payload' := encContext ⟨payload, NewtonQuery.address node⟩
  let routeSize := (NewtonQuery.address node).size + (2 * q).size + p.size + 1
  let routeTime := Cr * (payload.length + routeSize ^ dr + 1) + t
  have hc (req : SignedOperandRequest.Request) (hpayload : req.payload = payload')
      (hcoeff : req.coefficient < 2 * q) (hbit : req.bit < p) :
      let target := SharedWordFork.start (Fin.natAdd u 0) router input
        (SignedOperandRequest.encRequest req) 0
      router.HaltsWithin routeTime target ∧ (router.AcceptsWithin routeTime target ↔
        (if req.right then
          ((representative m p (NewtonQuery.value m p x (NewtonQuery.child node true))).coeff
            req.coefficient).val else
          ((representative m p (NewtonQuery.value m p x (NewtonQuery.child node false))).coeff
            req.coefficient).val).testBit req.bit = req.claim) := by
    intro target
    let a : Input := ⟨⟨payload, NewtonQuery.address node⟩, req.right, req.coefficient,
      req.bit, req.claim⟩
    have he : SignedOperandRequest.encRequest req = encInput a := by
      rw [encInput_eq]
      congr 1
      cases req
      simp_all [a, payload']
    have request_eq := request_address payload node req.right req.coefficient req.bit req.claim
    have childSpec := hchild req.right ⟨req.coefficient, hcoeff⟩ ⟨req.bit, hbit⟩ req.claim
    have hh := hr input a t (by simpa only [a, request_eq] using childSpec.1)
    have hsize : shortSize a ≤ routeSize := by
      have hi := Nat.size_le_size hcoeff.le
      have hb := Nat.size_le_size hbit.le
      dsimp only [shortSize, a, routeSize]
      omega
    have hclock : Cr * (a.context.payload.length + shortSize a ^ dr + 1) + t ≤ routeTime := by
      dsimp only [routeTime, a]
      gcongr
    have ha : router.AcceptsWithin
        (Cr * (a.context.payload.length + shortSize a ^ dr + 1) + t)
        (SharedWordFork.start (Fin.natAdd u 0) router input (encInput a) 0) ↔
        (if req.right then
          ((representative m p (NewtonQuery.value m p x (NewtonQuery.child node true))).coeff
            req.coefficient).val else
          ((representative m p (NewtonQuery.value m p x (NewtonQuery.child node false))).coeff
            req.coefficient).val).testBit req.bit = req.claim := by
      refine hh.2.trans ?_
      rw [show request a =
          ⟨payload, NewtonQuery.address (NewtonQuery.child node req.right), req.coefficient,
            req.bit, req.claim⟩ from request_eq]
      refine childSpec.2.trans ?_
      cases req.right <;> rfl
    dsimp only [target]
    rw [he]
    exact ⟨hh.1.mono hclock, ⟨fun h => ha.mp (h.of_halted_stepCoins hh.1),
      fun h => (ha.mpr h).mono hclock⟩⟩
  have hs := h input payload' m p routeTime
    (NewtonQuery.value m p x (NewtonQuery.child node false))
    (NewtonQuery.value m p x (NewtonQuery.child node true)) i hc bit claim
  have hb := Nat.add_le_add_right (hclock payload (NewtonQuery.address node) a.metadata) t
  have htime : A * (payload'.length +
      ((ReducedProductRequest.encMetadata a.metadata).length + 1) ^ D + 1) + routeTime ≤ time := by
    dsimp only [routeTime, routeSize, q, time, a, payload'] at ⊢ hb
    omega
  have ha := hs.2.trans (by rw [← value_product m p x node hnode])
  exact ⟨hs.1.mono htime, ⟨fun h => ha.mp (h.of_halted_stepCoins hs.1),
    fun h => (ha.mpr h).mono htime⟩⟩

end Turing.MultiTapeATM.NewtonProduct
