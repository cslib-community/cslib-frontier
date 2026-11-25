/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Primality
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Testing generators of prime fields at the first counting function level

`generatorTest (p, g)` accepts exactly a prime modulus `p` and a positive canonical representative
`g < p` of a primitive root. It is total on every pair of binary naturals. Primality is checked
by universally testing possible divisors, and generator status by universally testing the
smaller positive exponents. One bitstring of width `Nat.size p` supplies either candidate.
Thus the evaluator is polynomial-time, though its domain can be exponential, and one application
of short-index universal quantification places the test in F_1. No primality or discrete-log
oracle is assumed. Modular exponentiation uses the existing certified square-and-multiply API.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

private abbrev generatorChecks (p g d : ℕ) : Prop :=
  0 < g ∧ g < p ∧ (d = 0 ∨ p - 1 ≤ d ∨ powMod p g d ≠ 1)

private def generatorIndexTest : (ℕ × ℕ) × List Bool → Bool
  | ((p, g), w) => divisorIndexTest (p, w) &&
      decide (generatorChecks p g (BitString.binaryValue w))

open Classical in
/-- Test prime-field primitive roots on binary modulus/base pairs. Every malformed pair,
including modulus zero or one and noncanonical representatives, is rejected. -/
noncomputable def generatorTest (x : ℕ × ℕ) : Bool :=
  decide (∀ w : Fin (Nat.size x.1) → Bool, generatorIndexTest (x, List.ofFn w) = true)

private theorem computableInPolyTime_generatorIndexTest :
    ComputableInPolyTime generatorIndexTest
      (encPair (encPair encNat encNat) encBits) encBool := by
  have hp : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List Bool) × ℕ => x.1.1.1)
      (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
  have hg : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List Bool) × ℕ => x.1.1.2)
      (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
  have hd : ComputableInPolyTime
      (fun x : ((ℕ × ℕ) × List Bool) × ℕ => BitString.binaryValue x.1.2)
      (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
  have hpost : ComputableInPolyTime
      (fun pair : ((ℕ × ℕ) × List Bool) × ℕ =>
        let ((p, g), word) := pair.1
        let d := BitString.binaryValue word
        decide (0 < g ∧ g < p ∧ (d = 0 ∨ p - 1 ≤ d ∨ pair.2 ≠ 1)))
      (encPair (encPair (encPair encNat encNat) encBits) encNat) encBool :=
    .decide_and (.binary_lt' (.const 0) hg) (.decide_and (.binary_lt' hg hp)
      (.decide_or (hd.decide_eq' (.const 0))
        (.decide_or (.binary_le' (.binary_sub' hp (.const 1)) hd)
          (.decide_ne (.snd _ _) (.const 1)))))
  exact ComputableInPolyTime.bool_and.comp
    ((divisorIndexTest_polyTime.comp (by fun_prop)).prod
      (hpost.comp (ComputableInPolyTime.id'.prod
        (computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)))))

/-- A single universal short-index check puts the complete generator test in F_1.
All arithmetic and prime-divisor tests are performed by its one polynomial-time evaluator. -/
theorem generatorTest_mem_CountingFunction :
    generatorTest ∈ CountingFunction 1 (encPair encNat encNat) encBool :=
  CountingFunction.forall_bits (Decoder.pair Decoder.nat Decoder.nat)
    (CountingFunction.of_polyTime computableInPolyTime_generatorIndexTest)
    (ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.fst encNat encNat))

private theorem generatorTest_iff_checks (p g : ℕ) :
    generatorTest (p, g) = true ↔
      p.Prime ∧ 0 < g ∧ g < p ∧
        (∀ d, 0 < d → d < p - 1 → powMod p g d ≠ 1) := by
  classical
  change decide (∀ w : Fin (Nat.size p) → Bool,
    (divisorIndexTest (p, List.ofFn w) &&
      decide (generatorChecks p g (BitString.binaryValue (List.ofFn w)))) = true) = true ↔ _
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  refine ⟨fun h => ?_, fun ⟨hp, hg, hgp, hexp⟩ w => ?_⟩
  · have hcheck (d : ℕ) (hd : d < 2 ^ Nat.size p) : generatorChecks p g d := by
      obtain ⟨w, hw⟩ := BitString.exists_binaryValue_eq hd
      simpa only [hw] using (h w).2
    obtain ⟨hg, hgp, _⟩ := hcheck 0 (by positivity)
    exact ⟨(prime_iff_divisorIndices p).mpr fun w => (h w).1, hg, hgp, fun d hd hdp =>
      ((hcheck d ((by omega : d < p).trans (Nat.lt_size_self p))).2.2.resolve_left
        (by omega)).resolve_left (by omega)⟩
  · exact ⟨(prime_iff_divisorIndices p).mp hp w, hg, hgp,
      or_iff_not_imp_left.mpr fun hd => or_iff_not_imp_left.mpr fun hdp =>
        hexp _ (by omega) (by omega)⟩

private theorem powMod_eq_one_iff {p : ℕ} (hp : p.Prime) (g e : ℕ) :
    powMod p g e = 1 ↔ (g : ZMod p) ^ e = 1 := by
  rw [powMod_of_ne_zero hp.ne_zero]
  simpa only [Nat.cast_pow, Nat.cast_one, Nat.mod_eq_of_lt hp.one_lt] using
    (ZMod.natCast_eq_natCast_iff' (g ^ e) 1 p).symm

/-- The total binary test recognizes precisely canonical primitive roots of prime fields.
In particular the two-element field accepts its generator one, while all malformed moduli
are rejected. This characterization has no computational assumptions. -/
theorem generatorTest_eq_true_iff (p g : ℕ) :
    generatorTest (p, g) = true ↔
      p.Prime ∧ 0 < g ∧ g < p ∧ IsPrimitiveRoot (g : ZMod p) (p - 1) := by
  rw [generatorTest_iff_checks]
  refine ⟨fun ⟨hp, hg, hgp, hexp⟩ => ?_, fun ⟨hp, hg, hgp, hroot⟩ =>
    ⟨hp, hg, hgp, fun e he hep heq =>
      hroot.pow_ne_one_of_pos_of_lt (by omega) hep ((powMod_eq_one_iff hp g e).mp heq)⟩⟩
  let : Fact p.Prime := ⟨hp⟩
  have hg0 : (g : ZMod p) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff g p).not.mpr (Nat.not_dvd_of_pos_of_lt hg hgp)
  exact ⟨hp, hg, hgp, (IsPrimitiveRoot.iff (by omega : 0 < p - 1)).mpr
    ⟨ZMod.pow_card_sub_one_eq_one hg0, fun e he hep heq =>
      hexp e he hep ((powMod_eq_one_iff hp g e).mpr heq)⟩⟩

/-- On canonical representatives of a prime field, the total test is exactly membership in
the finite set of multiplicative generators. -/
theorem generatorTest_eq_true_iff_mem {p : ℕ} [Fact p.Prime] {g : ℕ} (hg : g < p) :
    generatorTest (p, g) = true ↔ (g : ZMod p) ∈ primitiveRoots (p - 1) (ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  rw [generatorTest_eq_true_iff, mem_primitiveRoots (by omega : 0 < p - 1)]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hp, Nat.pos_of_ne_zero fun hz =>
    h.ne_zero (by omega) (by simp only [hz, Nat.cast_zero]), hg, h⟩⟩

/-- Composite and malformed moduli reject every proposed generator. -/
theorem generatorTest_ne_true_of_not_prime {p g : ℕ} (hp : ¬p.Prime) :
    generatorTest (p, g) ≠ true :=
  fun h => hp ((generatorTest_eq_true_iff p g).mp h).1

end Cslib.Complexity
