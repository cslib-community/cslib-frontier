/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingLeaves
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveWordSum

/-!
# A native stopping sum from one raw request

One fixed finite alternating machine constructs the complete assignment-sum traversal and
uses the native stopping-product compiler at its leaves. The input request contains only the
short product context, binary assignment depth, precision, bit and claim. Native preparation
and traversal charge the assignment depth linearly; the polynomial applies only to short
metadata. Each branch pays one product clock and hence one supplied terminal evaluation.
-/

noncomputable section

public section

namespace Turing.MultiTapeATM.StoppingSum

open MultiTapeTM Cslib Cslib.BitString Cslib.Circuits.Boolean
open CarryLookahead.Query Cslib.Circuits.Frontier.FastContraction
open StoppingQuery.ProductRouting StoppingLeafRequest

private theorem preparation_le (Cs Ds Cl Dl contextLength L w : ℕ) (bit : Fin w)
    (claim : Bool) :
    Cs * (contextLength + L +
        ((CountingInput.encInput ⟨L, ⟨w, bit.val, claim⟩⟩).length + 1) ^ Ds + 1) +
      Cl * (CarrySaveCountingRoot.sizeBudget (2 ^ L) w + (encNat (2 ^ L)).length +
        (encNat w).length + (contextLength + 1) ^ Dl + 1) ≤
      (Cs * (7 ^ Ds + 2) + 3 * Cl) *
        (L + (contextLength + L.size + w.size + 1) ^ max 1 (max Ds Dl) + 1) := by
  let D := max 1 (max Ds Dl)
  let short := contextLength + L.size + w.size + 1
  let bound := L + short ^ D + 1
  have hpos : 0 < short := by dsimp [short]; omega
  have hDs : Ds ≤ D := (Nat.le_max_left Ds Dl).trans (Nat.le_max_right 1 _)
  have hDl : Dl ≤ D := (Nat.le_max_right Ds Dl).trans (Nat.le_max_right 1 _)
  have hlinear : short ≤ short ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (Nat.le_max_left 1 (max Ds Dl))
  have hcontext : contextLength ≤ short ^ D :=
    (show contextLength ≤ short by dsimp [short]; omega).trans hlinear
  have hp := CountingInput.length_encInput_le ⟨L, ⟨w, bit.val, claim⟩⟩ bit.isLt
  change (CountingInput.encInput ⟨L, ⟨w, bit.val, claim⟩⟩).length ≤
    2 * L.size + 4 * w.size + 4 at hp
  have hparameters : (CountingInput.encInput ⟨L, ⟨w, bit.val, claim⟩⟩).length + 1 ≤
      7 * short := by
    dsimp only [short]
    omega
  have hpow : ((CountingInput.encInput ⟨L, ⟨w, bit.val, claim⟩⟩).length + 1) ^ Ds ≤
      7 ^ Ds * short ^ D := by
    calc
      _ ≤ (7 * short) ^ Ds := Nat.pow_le_pow_left hparameters Ds
      _ = 7 ^ Ds * short ^ Ds := Nat.mul_pow ..
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hDs)
  have hsum : contextLength + L +
      ((CountingInput.encInput ⟨L, ⟨w, bit.val, claim⟩⟩).length + 1) ^ Ds + 1 ≤
        (7 ^ Ds + 2) * bound := by
    have hbase : contextLength + L + 1 ≤ bound := by dsimp [bound]; omega
    have hpower : short ^ D ≤ bound := by dsimp [bound]; omega
    have hscaled := Nat.mul_le_mul_left (7 ^ Ds) hpower
    rw [Nat.add_mul]
    omega
  have hcontextPow : (contextLength + 1) ^ Dl ≤ short ^ D :=
    (Nat.pow_le_pow_left (by dsimp [short]; omega) Dl).trans
      (Nat.pow_le_pow_right hpos hDl)
  have hshort : L.size + 2 * w.size ≤ 2 * short ^ D :=
    (show L.size + 2 * w.size ≤ 2 * short by dsimp [short]; omega).trans
      (Nat.mul_le_mul_left 2 hlinear)
  have hleaf : CarrySaveCountingRoot.sizeBudget (2 ^ L) w + (encNat (2 ^ L)).length +
      (encNat w).length + (contextLength + 1) ^ Dl + 1 ≤ 3 * bound := by
    simp only [CarrySaveCountingRoot.sizeBudget, Nat.clog_pow 2 L one_lt_two,
      encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]
    dsimp only [bound]
    omega
  change _ ≤ (Cs * (7 ^ Ds + 2) + 3 * Cl) * bound
  calc
    _ ≤ Cs * ((7 ^ Ds + 2) * bound) + Cl * (3 * bound) :=
      Nat.add_le_add (Nat.mul_le_mul_left Cs hsum) (Nat.mul_le_mul_left Cl hleaf)
    _ = _ := by ring

/-- Compile the full assignment sum into one finite native machine before any runtime
parameters are supplied. The remaining premise is exactly the native terminal contract on
bounded physical assignment paths and valid product terminals. The terminal clock is added
once per branch, inside the single product clock. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S]
    (assignment query : Fin N) (hne : assignment ≠ query) (terminal : MultiTapeATM N Bool S) :
    ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM K Bool Q) (C D P E : ℕ),
      ∀ (input : List Bool) (L : ℕ) (parameters : StoppingQuery.Product.Parameters)
        (entry : ℕ → ℕ → GaloisRingArith.Ring parameters.precision (modulus parameters.scale))
        (terminalTime : ℕ),
        (∀ (path : List Bool),
          path.length ≤ CarrySaveCountingRoot.sizeBudget (2 ^ L) parameters.precision → ∀ p,
          Valid parameters (2 ^ Nat.clog 2 parameters.vertices)
            (Nat.clog 2 parameters.vertices) p → player p = none →
          let start := (TwoWordInput.ready assignment query input path (encPosition p)).withState
            (some terminal.toPTM.initial)
          terminal.HaltsWithin terminalTime start ∧
            (terminal.AcceptsWithin terminalTime start ↔
              StoppingQuery.value parameters.scale parameters.precision 0 parameters.vertices
                (fun _ v => entry (binaryValue path) v) (address p) = p.claim)) →
        ∀ (coefficient : Fin (modulus parameters.scale).length)
          (bit : Fin parameters.precision) (claim : Bool),
          let ctx : Context := ⟨parameters, coefficient.val⟩
          let request : CarrySaveWordSum.Request :=
            ⟨encContext ctx, L, ⟨parameters.precision, bit.val, claim⟩⟩
          let start := SharedWordFork.start source atm input (CarrySaveWordSum.encRequest request) 0
          let time := C * (L +
            ((encContext ctx).length + L.size + parameters.precision.size + 1) ^ D + 1) +
              StoppingProduct.clock P E parameters terminalTime
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ((representative parameters.scale parameters.precision
              (∑ assignment ∈ Finset.range (2 ^ L),
                ∏ vertex ∈ Finset.range parameters.vertices, entry assignment vertex)).coeff
                  coefficient.val).val.testBit bit.val = claim) := by
  obtain ⟨a, QL, hQL, leaf, Cl, Dl, P, E, hleaf⟩ :=
    StoppingLeaves.exists_leaves assignment query hne terminal
  let := hQL
  obtain ⟨K, source, Q, hQ, atm, Cs, Ds, hsum⟩ := CarrySaveWordSum.exists_evaluator leaf
  let D := max 1 (max Ds Dl)
  let C := Cs * (7 ^ Ds + 2) + 3 * Cl
  refine ⟨K, source, Q, hQ, atm, C, D, P, E, ?_⟩
  intro input L parameters entry terminalTime hterminal coefficient bit claim ctx request start time
  let B := CarrySaveCountingRoot.sizeBudget (2 ^ L) parameters.precision
  let leafTime := Cl * (B + (encNat (2 ^ L)).length + (encNat parameters.precision).length +
    ((encContext ctx).length + 1) ^ Dl + 1) +
      StoppingProduct.clock P E parameters terminalTime
  have hl := hleaf input ctx (encNat (2 ^ L)) (encNat parameters.precision) B terminalTime entry
    coefficient.isLt hterminal
  have hs := hsum input (encContext ctx) L parameters.precision leafTime
    (StoppingQuery.WordSum.leaves parameters.scale parameters.precision parameters.vertices
      entry coefficient.val) hl.1 hl.2 bit claim
  have hb := Nat.add_le_add_right
    (preparation_le Cs Ds Cl Dl (encContext ctx).length L parameters.precision bit claim)
    (StoppingProduct.clock P E parameters terminalTime)
  have hclock : Cs * ((encContext ctx).length + L +
      ((CountingInput.encInput ⟨L, request.query⟩).length + 1) ^ Ds + 1) + leafTime ≤ time := by
    simpa only [time, leafTime, B, C, D, request, Nat.add_assoc] using hb
  rw [StoppingQuery.WordSum.bit_sum] at hs
  exact ⟨hs.1.mono hclock,
    ⟨fun h => hs.2.mp (h.of_halted_stepCoins hs.1), fun h => (hs.2.mpr h).mono hclock⟩⟩

end Turing.MultiTapeATM.StoppingSum
