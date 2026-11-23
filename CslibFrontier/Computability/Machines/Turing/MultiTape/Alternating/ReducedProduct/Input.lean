/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ReducedProductRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SourceWordInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromLeaves
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse

/-!
# Native reduced products from encoded requests

The compiler derives the modulus half-degree, convolution tree size and every physical evaluator
field from a single request word. The only supplied computation is the fixed finite machine
answering operand coefficient bits. Its runtime is charged once; initialization and navigation
are linear in the protected payload and polynomial in the binary metadata.

`exists_evaluator` starts from the request on one work tape. `exists_from_input` additionally
loads the ordinary framed request and source input. These are local product compilers; the
recursive contraction continuation and its global budget remain tracked by #4728.
-/

public section

namespace Turing.MultiTapeATM.ReducedProduct.Input

open MultiTapeTM Cslib GaloisRingArith
open Cslib.Circuits.Frontier.FastContraction
open Cslib.Circuits.Boolean.CarryLookahead.Query
open ReducedProductRequest

private def localSize (a : Metadata) : ℕ :=
  (3 ^ modulusExp a.scale).size + a.coefficient.size + (parameters a).count.size +
    a.precision.size + 1

private theorem localSize_poly : PolyBounded (fun a : Metadata => (encMetadata a).length)
    localSize := by
  have hhalf := ResidueInverse.half_polyTime.comp encMetadata_scale_deg.computableInPolyTime
  have hq := (ComputableInPolyTime.unary_to_binary.comp hhalf).polyBounded_length
  have hi := encMetadata_coefficient_deg.computableInPolyTime.polyBounded_length
  have hn := (CountingInput.encInput_count_deg.computableInPolyTime.comp
    parameters_polyTime).polyBounded_length
  have hp := encMetadata_precision_deg.computableInPolyTime.polyBounded_length
  unfold localSize
  simpa only [encNat_apply, Function.comp_apply, Nat.size_eq_bits_len] using
    (((hq.add hi).add hn).add hp).add (.const 1)

private def leafCost (Cc dc : ℕ) (Co dO : Bool → ℕ) (a : ReducedProductRequest.Input) : ℕ :=
  let n := (parameters a.metadata).count
  let p := a.metadata.precision
  let q := 3 ^ modulusExp a.metadata.scale
  let B := CarrySaveCountingRoot.sizeBudget n p
  let size := q.size + a.metadata.coefficient.size + n.size + p.size + B + 1
  Cc * ((SignedOperandRequest.encContext (context a)).length + n.size + p.size +
    (B + 2) ^ dc + 1) + Co false * (a.payload.length + size ^ dO false + 1) +
      Co true * (a.payload.length + size ^ dO true + 1)

private theorem leafCost_payload (Cc dc : ℕ) (Co dO : Bool → ℕ)
    (a : ReducedProductRequest.Input) :
    leafCost Cc dc Co dO a = leafCost Cc dc Co dO ⟨[], a.metadata⟩ +
      (2 * Cc + Co false + Co true) * a.payload.length := by
  simp only [leafCost, context, SignedOperandRequest.encContext_apply,
    SignedOperandRequest.encContextFields, length_encPair, encBits_apply,
    List.length_nil]
  ring

private theorem leafCost_poly (Cc dc : ℕ) (Co dO : Bool → ℕ) :
    PolyBounded (fun a : Metadata => (encMetadata a).length)
      (fun a => leafCost Cc dc Co dO ⟨[], a⟩) := by
  have hp := localSize_poly
  have bound : PolyBounded (fun a : Metadata => (encMetadata a).length)
      (fun a => Cc * (4 * localSize a + (3 * localSize a + 2) ^ dc + 3) +
        Co false * ((3 * localSize a) ^ dO false + 1) +
          Co true * ((3 * localSize a) ^ dO true + 1)) :=
    (((PolyBounded.const Cc).mul ((((PolyBounded.const 4).mul hp).add
      ((((PolyBounded.const 3).mul hp).add (.const 2)).pow dc)).add (.const 3))).add
        ((PolyBounded.const (Co false)).mul
          ((((PolyBounded.const 3).mul hp).pow (dO false)).add (.const 1)))).add
      ((PolyBounded.const (Co true)).mul
        ((((PolyBounded.const 3).mul hp).pow (dO true)).add (.const 1)))
  apply bound.mono
  intro a
  let n := (parameters a).count
  have hl : Nat.clog 2 n ≤ n.size := Nat.clog_le_of_le_pow (Nat.lt_size_self n).le
  have hs := Nat.size_le_self (Nat.clog 2 n)
  have hb : CarrySaveCountingRoot.sizeBudget n a.precision ≤ 2 * n.size + a.precision.size := by
    dsimp only [CarrySaveCountingRoot.sizeBudget]
    omega
  have hz : (3 ^ modulusExp a.scale).size + a.coefficient.size + n.size + a.precision.size +
      CarrySaveCountingRoot.sizeBudget n a.precision + 1 ≤ 3 * localSize a := by
    dsimp only [localSize]
    change _ ≤ 3 * ((3 ^ modulusExp a.scale).size + a.coefficient.size + n.size +
      a.precision.size + 1)
    omega
  have hc : (SignedOperandRequest.encContext (context ⟨[], a⟩)).length + n.size +
      a.precision.size ≤ 4 * localSize a + 2 := by
    simp only [context, SignedOperandRequest.encContext_apply,
      SignedOperandRequest.encContextFields, length_encPair, encBits_apply,
      List.length_nil, encNat_apply, Nat.size_eq_bits_len]
    dsimp only [localSize]
    change _ ≤ 4 * ((3 ^ modulusExp a.scale).size + a.coefficient.size + n.size +
      a.precision.size + 1) + 2
    omega
  have hb' : CarrySaveCountingRoot.sizeBudget n a.precision ≤ 3 * localSize a := by
    omega
  dsimp only [n] at hc hz hb'
  dsimp only [leafCost]
  simp only [List.length_nil, Nat.zero_add]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.mul_le_mul_left
      have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hb' 2) dc
      omega
    · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left hz _) 1)
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left hz _) 1)

private theorem clock_bound (ci di c e Cc dc A D : ℕ) (Co dO : Bool → ℕ) :
    ∃ C E, ∀ a : ReducedProductRequest.Input, a.metadata.bit < a.metadata.precision →
      A * (a.payload.length + ((encMetadata a.metadata).length + 1) ^ D + 1) + 8 +
        CarryLookaheadCountingFromLeaves.overhead ci di c e (parameters a.metadata) +
          leafCost Cc dc Co dO a + 10 ≤
            C * (a.payload.length + ((encMetadata a.metadata).length + 1) ^ E + 1) := by
  obtain ⟨B, F, hB⟩ := CarryLookaheadCountingFromLeaves.exists_overhead_le ci di c e
  let size := fun a : ReducedProductRequest.Input => (encMetadata a.metadata).length + 1
  have hm : PolyBounded size (fun a : ReducedProductRequest.Input =>
      (encMetadata a.metadata).length) := PolyBounded.self.mono (fun _ => by dsimp [size]; omega)
  have hl := localSize_poly.comp hm
  have hf := (leafCost_poly Cc dc Co dO).comp hm
  let extra := fun a : ReducedProductRequest.Input =>
    A * (size a ^ D + 1) + B * localSize a.metadata ^ F +
      leafCost Cc dc Co dO ⟨[], a.metadata⟩ + 18
  have hextra : PolyBounded size extra :=
    ((((PolyBounded.const A).mul ((PolyBounded.self.pow D).add (.const 1))).add
      ((PolyBounded.const B).mul (hl.pow F))).add hf).add (.const 18)
  obtain ⟨C, E, h⟩ := hextra.exists_le_linear_add_pow (fun a => a.payload.length)
    (A + 2 * Cc + Co false + Co true) (fun a => by dsimp [size]; omega)
  refine ⟨C, E, fun a ha => ?_⟩
  have hsmall := hB (parameters a.metadata) ha
  have hn : (parameters a.metadata).count.size + a.metadata.precision.size + 1 ≤
      localSize a.metadata := by dsimp [localSize]; omega
  have hover := hsmall.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_left hn F))
  have hh := h a
  rw [leafCost_payload] at ⊢
  dsimp only [extra, size] at hh
  nlinarith

/-- Compile a fixed operand-bit machine into a product-bit machine starting from one encoded
request on a work tape. All derived arithmetic and physical fields are constructed natively.
The child clock is added with coefficient one, uniformly over every valid bit request. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S] (src : Fin N)
    (child : MultiTapeATM N Bool S) :
    ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM K Bool Q) (C D : ℕ),
      ∀ (input payload : List Bool) (m p t : ℕ) (x y : Ring p (modulus m))
        (i : Fin (modulus m).length),
        (∀ req : SignedOperandRequest.Request, req.payload = payload →
          req.coefficient < 2 * 3 ^ modulusExp m → req.bit < p →
          let target := SharedWordFork.start src child input (SignedOperandRequest.encRequest req) 0
          child.HaltsWithin t target ∧ (child.AcceptsWithin t target ↔
            (if req.right then ((representative m p y).coeff req.coefficient).val
              else ((representative m p x).coeff req.coefficient).val).testBit req.bit =
                req.claim)) →
        ∀ (bit : Fin p) (claim : Bool),
          let a : ReducedProductRequest.Input := ⟨payload, ⟨m, p, i.val, bit.val, claim⟩⟩
          let start := SharedWordFork.start source atm input (ReducedProductRequest.encInput a) 0
          let time := C * (payload.length + ((encMetadata a.metadata).length + 1) ^ D + 1) + t
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim) := by
  obtain ⟨k, r, z, S₀, hS₀, product, c, e, Cc, dc, Co, dO, hp⟩ :=
    Native.exists_evaluator src child
  let := hS₀
  obtain ⟨scratch, S₁, hS₁, prepared, ci, di, hi⟩ :=
    CarryLookaheadCountingFromParameters.exists_prepend product
  let := hS₁
  obtain ⟨d, hcontext, hparameters⟩ := exists_setup_inO
  obtain ⟨K, source, Q, hQ, atm, A, hload⟩ :=
    TwoWordLoad.exists_load_from hcontext hparameters _ _
      (CarryLookaheadCountingPrepare.context_ne_request scratch k r z) prepared
  obtain ⟨C, D, hclock⟩ := clock_bound ci di c e Cc dc A d Co dO
  refine ⟨K, source, Q, hQ, atm, C, D, ?_⟩
  intro input payload m p t x y i hchild bit claim a start time
  let L := depth a.metadata
  let n := (parameters a.metadata).count
  let setup := leafCost Cc dc Co dO a
  let evaluationTime := CarryLookaheadCounting.clockOfRoot c e p
    (40 * L + 2 * L.size + 2 * p.size + (setup + t + 10) + 1)
  have hh := hp input payload m p t x y i hchild bit claim
  have hn : Nat.clog 2 n = L := Nat.clog_pow 2 L (by decide)
  have hlength (v : ℕ) : (encNat v).length = v.size := Nat.size_eq_bits_len v
  simp only [hlength] at hh
  change product.HaltsWithin evaluationTime _ ∧ (product.AcceptsWithin evaluationTime _ ↔
    ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim) at hh
  obtain ⟨hprepared, hmeaning⟩ := hi input (SignedOperandRequest.encContext (context a))
    (parameters a.metadata) evaluationTime hh.1
  let preparedTime := CarryLookaheadCountingFromParameters.clockOfEvaluator ci di
    (parameters a.metadata) evaluationTime
  obtain ⟨hloaded, hloadedMeaning⟩ := hload input a 0 (Nat.zero_le _) preparedTime (by
    rw [CarryLookaheadCountingPrepare.ready_eq_initial]
    exact hprepared)
  have heq : preparedTime =
      CarryLookaheadCountingFromLeaves.overhead ci di c e (parameters a.metadata) +
        setup + 10 + t := by
    simp only [preparedTime, evaluationTime, CarryLookaheadCountingFromLeaves.overhead,
      CarryLookaheadCountingFromParameters.clockOfEvaluator,
      CarryLookaheadCounting.clockOfRoot, CarrySaveCountingRoot.clockOfLeaf]
    change _ = ci * ((CountingInput.encInput (parameters a.metadata)).length + 1) ^ di +
      ((2 * Nat.clog 2 (p + 1) + 6) * (CarryLookaheadCounting.overhead c e p + 2) +
        CarryLookaheadCounting.overhead c e p +
          (40 * Nat.clog 2 n + 2 * (Nat.clog 2 n).size + 2 * p.size + 0 + 1) + 1) +
      setup + 10 + t
    rw [hn]
    omega
  have hbound : 0 + A * (a.payload.length + ((encMetadata a.metadata).length + 1) ^ d + 1) +
      8 + preparedTime ≤ time := by
    rw [heq]
    have hb := hclock a bit.isLt
    dsimp only [time, a, setup] at ⊢ hb
    omega
  have hm : atm.AcceptsWithin
      (0 + A * (a.payload.length + ((encMetadata a.metadata).length + 1) ^ d + 1) +
        8 + preparedTime) start ↔
      ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim := by
    refine hloadedMeaning.trans ?_
    rw [CarryLookaheadCountingPrepare.ready_eq_initial]
    exact hmeaning.trans hh.2
  exact ⟨hloaded.mono hbound, ⟨fun h => hm.mp (h.of_halted_stepCoins hloaded),
    fun h => (hm.mpr h).mono hbound⟩⟩

/-- An ordinary-input product compiler. The sole external input is the framed request followed
by the original source word, which remains the operand machine's read-only input. Loading it
adds a linear source-length cost and leaves the recursive time coefficient equal to one. -/
theorem exists_from_input {N : ℕ} {S : Type} [Finite S] (src : Fin N)
    (child : MultiTapeATM N Bool S) :
    ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (C D : ℕ),
      ∀ (input payload : List Bool) (m p t : ℕ) (x y : Ring p (modulus m))
        (i : Fin (modulus m).length),
        (∀ req : SignedOperandRequest.Request, req.payload = payload →
          req.coefficient < 2 * 3 ^ modulusExp m → req.bit < p →
          let target := SharedWordFork.start src child input (SignedOperandRequest.encRequest req) 0
          child.HaltsWithin t target ∧ (child.AcceptsWithin t target ↔
            (if req.right then ((representative m p y).coeff req.coefficient).val
              else ((representative m p x).coeff req.coefficient).val).testBit req.bit =
                req.claim)) →
        ∀ (bit : Fin p) (claim : Bool),
          let a : ReducedProductRequest.Input := ⟨payload, ⟨m, p, i.val, bit.val, claim⟩⟩
          let word := encPair ReducedProductRequest.encInput encBits (a, input)
          let start := atm.toPTM.toNTM.initCfg word
          let time := C * (input.length + payload.length +
            ((encMetadata a.metadata).length + 1) ^ D + 1) + t
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim) := by
  obtain ⟨u, source, S₀, hS₀, product, A, D, h⟩ := exists_evaluator src child
  let := hS₀
  obtain ⟨K, Q, hQ, atm, B, hb⟩ :=
    SourceWordInput.exists_prepend ReducedProductRequest.encInput source product
  refine ⟨K, Q, hQ, atm, A + 3 * B, D + 1, ?_⟩
  intro input payload m p t x y i hchild bit claim a word start time
  obtain ⟨hh, ha⟩ := h input payload m p t x y i hchild bit claim
  obtain ⟨hh', ha'⟩ := hb a input
    (A * (payload.length + ((encMetadata a.metadata).length + 1) ^ D + 1) + t) hh
  have hlen : (ReducedProductRequest.encInput a).length =
      2 * payload.length + (encMetadata a.metadata).length + 1 := by
    simp only [encInput_apply, encInputFields, length_encPair, encBits_apply]
    change 2 * payload.length + 1 + (encMetadata a.metadata).length = _
    omega
  let n := (encMetadata a.metadata).length + 1
  have hp : n ^ D ≤ n ^ (D + 1) := Nat.pow_le_pow_right (by dsimp [n]; omega) (by omega)
  have hn : n ≤ n ^ (D + 1) := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [n]; omega) (by omega)
  have hn' : (encMetadata a.metadata).length + 1 ≤ n ^ (D + 1) := hn
  have ht : B * (input.length + (ReducedProductRequest.encInput a).length + 1) +
      (A * (payload.length + n ^ D + 1) + t) ≤ time := by
    rw [hlen]
    dsimp only [time]
    change _ ≤ (A + 3 * B) * (input.length + payload.length + n ^ (D + 1) + 1) + t
    have h₁ := Nat.mul_le_mul_left A (show payload.length + n ^ D + 1 ≤
      input.length + payload.length + n ^ (D + 1) + 1 by omega)
    have h₂ := Nat.mul_le_mul_left B (show input.length +
      (2 * payload.length + (encMetadata a.metadata).length + 1) + 1 ≤
        3 * (input.length + payload.length + n ^ (D + 1) + 1) by omega)
    rw [Nat.add_mul]
    nlinarith
  exact ⟨hh'.mono ht, ⟨fun h => ha.mp (ha'.mp (h.of_halted_stepCoins hh')),
    fun h => (ha'.mpr (ha.mpr h)).mono ht⟩⟩

end Turing.MultiTapeATM.ReducedProduct.Input
