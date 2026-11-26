/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.GenericRAM.Native.IndexFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-!
# Composing native certificates in factored time and polynomial space

Checks sequential composition, selected-branch conditionals with an unguarded `yes` factor,
retained-input option elimination, and polynomially bounded `IndexFold` streaming.
-/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Turing.MultiTapeTM Cslib.GenericRAM ComputableInPolyTime NativeCertificate.FactorTimePolySpace

namespace CslibFrontierTests.FactorTimePolySpace

private noncomputable def weightedRev (K : List Bool → ℕ) (hK : ∀ w, 1 ≤ K w) :
    NativeCertificate List.reverse encBits encBits :=
  let c := NativeCertificate.ofPolyTime bitsReverse
  ⟨fun w => K w * c.time w, c.space,
    c.computes.mono_le (fun w => Nat.le_mul_of_pos_left _ (hK w)) fun _ => le_rfl⟩

private theorem weightedRev_factor (K : List Bool → ℕ) (hK : ∀ w, 1 ≤ K w) :
    (weightedRev K hK).FactorTimePolySpace K :=
  let hp := NativeCertificate.ofPolyTime_isPolynomial bitsReverse
  .of_polyBounded hp.1 hp.2 fun _ => le_rfl

private theorem twoStage_factor :
    ((weightedRev (fun w => 2 ^ (2 * w.length)) fun _ => Nat.two_pow_pos _).comp
      (weightedRev (fun w => 2 ^ w.length) fun _ => Nat.two_pow_pos _)).FactorTimePolySpace
      (fun w => 2 ^ w.length + 2 ^ (2 * w.length)) :=
  ((weightedRev_factor _ _).comp (weightedRev_factor _ _)).mono fun w => by
    simp only [List.length_reverse, le_rfl]

example : ∃ e : ℕ, ComputableInO
    (fun w : List Bool => (Option.some true).elim w.reverse
      fun b => (IndexFold.run (List.reverse ∘ Prod.snd) 2 (w, b).1).2)
    encBits encBits (fun w => 2 ^ w.length * (w.length + 1) ^ e)
    (fun w => (w.length + 1) ^ e) := by
  have hRun (w : List Bool) (j : ℕ) :
      (IndexFold.run (List.reverse ∘ Prod.snd) j w).2.length = w.length := by
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [IndexFold.run_succ, IndexFold.step, Function.comp_apply, List.length_reverse, ih]
  have hpos {n : ℕ} : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  exact (option (fun _ => hpos)
    ((ofPolyTime (const (encOut := encOption encBool) (Option.some true))).mono fun _ => hpos)
    ((branch (ofPolyTime (const false))
      (weightedRev_factor (fun w => 2 ^ (2 ^ w.length)) fun _ => hpos)
      (fun _ h => Bool.noConfusion h) (ofPolyTime bitsReverse)).mono fun _ => hpos)
    (IndexFold.certificate_factorTimePolySpace_of_polyBounded
      (NativeCertificate.const_isPolynomial 2)
      (NativeCertificate.ofPolyTime_isPolynomial (fst encBits encBool))
      ((weightedRev_factor (fun w => 2 ^ w.length) fun _ => hpos).comp_polyPre
        (snd encNat encBits) fun _ => hpos)
      (.const 2) (K := fun p : List Bool × Bool => 2 ^ p.1.length) (B := fun p => p.1.length)
      (fun _ => hpos)
      (PolyBounded.self.mono fun p => by simp only [length_encPair, encBits_apply]; omega)
      (fun _ _ _ => by simp only [hRun, le_rfl])
      (fun _ _ _ => by simp only [encBits_apply, hRun, le_rfl])).snd
    fun _ _ _ => le_rfl).computableInO

example : (List.reverse ∘ List.reverse) [true, false, false] = [true, false, false] := by decide
example : (IndexFold.run (List.reverse ∘ Prod.snd) 3 [true, false]).2 = [false, true] := by decide
example : ∃ e : ℕ, ComputableInO (List.reverse ∘ List.reverse) encBits encBits
    (fun w => (2 ^ w.length + 2 ^ (2 * w.length)) * (w.length + 1) ^ e)
    (fun w => (w.length + 1) ^ e) := twoStage_factor.computableInO
example : ComputableInPolySpace (List.reverse ∘ List.reverse) encBits encBits :=
  twoStage_factor.computableInPolySpace

end CslibFrontierTests.FactorTimePolySpace
