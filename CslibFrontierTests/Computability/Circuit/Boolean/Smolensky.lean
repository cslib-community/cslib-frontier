/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.Smolensky
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeParity
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Data.ZMod.Defs

/-!
# Tests for Razborov–Smolensky lower bounds and multiplicative characters

Checked concrete evaluations and instantiations of `BitString.phaseChar`,
`BitString.card_agree_phaseChar_le`, Arora–Barak Lemma 13.6 (`BitString.exists_agree_of_parity`
with `BitString.lowDegree_eq_signSpan`), `Smolensky.two_mul_two_pow_le_size_of_computes_modGate`,
`Smolensky.modGate_notMem_AC0Mod`, and `Smolensky.compl_modGate_notMem_AC0Mod`.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.Smolensky

open Finset Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.Smolensky

/-! ### Multiplicative characters and coordinatewise degree preservation -/

example : phaseChar (2 : ZMod 3) ({0, 1} : Finset (Fin 2)) ![true, true] = 1 := by
  decide

example : phaseChar (2 : ZMod 3) ({0, 1} : Finset (Fin 2)) ![true, false] = 2 := by
  decide

example : #{x : BitString 2 | (1 : ZMod 3) = (2 : ZMod 3) ^ weight x} ≤
    #{S : Finset (Fin 2) | #S ≤ 2 / 2 + 0} :=
  card_agree_phaseChar_le (ω := (2 : ZMod 3)) (by decide) (by decide) (one_mem_lowDegree 0)

/-! ### Arora–Barak Lemma 13.6 -/

instance : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩

/-- Arora–Barak Lemma 13.6 in the source's form, over `GF(3)` in the `±1` monomials
`∏ i ∈ S, (-1) ^ xᵢ`: if a sum `g` of monomials of at most `√n` coordinates agrees with the product
of all `n` coordinates on `G`, every function on `G` agrees there with a sum of monomials of at most
`n / 2 + √n` coordinates. -/
theorem lemma_13_6 {n : ℕ} {g : BitString n → ZMod 3}
    (hg : g ∈ Submodule.span (ZMod 3) (chi (ZMod 3) '' {S : Finset (Fin n) | #S ≤ Nat.sqrt n}))
    (G : Finset (BitString n)) (hG : ∀ x ∈ G, g x = chi (ZMod 3) univ x)
    (f : BitString n → ZMod 3) :
    ∃ p ∈ Submodule.span (ZMod 3) (chi (ZMod 3) '' {S : Finset (Fin n) | #S ≤ n / 2 + Nat.sqrt n}),
      ∀ x ∈ G, p x = f x := by
  have hg' : g ∈ lowDegree (ZMod 3) (Fin n) (Nat.sqrt n) := by
    rw [lowDegree_eq_signSpan]
    exact hg
  obtain ⟨p, hp, h⟩ := exists_agree_of_parity hg' G hG f
  rw [lowDegree_eq_signSpan, Fintype.card_fin] at hp
  exact ⟨p, hp, h⟩

-- The hypotheses hold for one coordinate, with `g` the character itself and `G` the whole cube.
example (f : BitString 1 → ZMod 3) :
    ∃ p ∈ Submodule.span (ZMod 3) (chi (ZMod 3) '' {S : Finset (Fin 1) | #S ≤ 1 / 2 + Nat.sqrt 1}),
      ∀ x ∈ univ, p x = f x :=
  lemma_13_6 (Submodule.subset_span ⟨univ, by simp, rfl⟩) univ (fun _ _ => rfl) f

example :
    (fun x : BitString 2 =>
        monomial (ZMod 3) ({0, 1} : Finset (Fin 3)) ![x 0, x 1, true]) ∈
      lowDegree (ZMod 3) (Fin 2) 2 := by
  refine comp_mem_lowDegree (φ := fun x : BitString 2 => ![x 0, x 1, true]) (fun i => ?_)
    (monomial_mem_lowDegree (by decide))
  fin_cases i
  · exact bitVal_mem_lowDegree 0
  · exact bitVal_mem_lowDegree 1
  · convert one_mem_lowDegree (R := ZMod 3) (ι := Fin 2) 1
    simp [bitVal]

/-! ### Word conventions and finite circuit lower bounds -/

example : [true, false, true] ∈ Language.ofSlices (modGate 3) :=
  (mem_ofSlices_modGate_iff 3 [true, false, true]).2 (by decide)

example : [true, true, true] ∈ (Language.ofSlices (modGate 3))ᶜ :=
  (mem_compl_ofSlices_modGate_iff 3 [true, true, true]).2 (by decide)

example : ¬ (Circuit.oneGate (σ := Unbounded.extSignature) (.gate 3601) id).Computes
    (Unbounded.extInterpretation (modGate 2)) (single (modGate 3 3601)) := by
  intro hC
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbound := two_mul_two_pow_le_size_of_computes_modGate (p := 3) (q := 2) (by decide) hC
    (ℓ := 5) (by decide) (by
      have hd : (Circuit.oneGate (σ := Unbounded.extSignature) (.gate 3601) id).depth = 1 :=
        Circuit.depth_oneGate _ _
      rw [hd]
      decide)
  rw [Circuit.size_oneGate] at hbound
  omega

/-! ### Arbitrary prime pairs `MOD_p ∉ AC⁰[q]` -/

example : Language.ofSlices (modGate 3) ∉ AC0Mod 2 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  modGate_notMem_AC0Mod (by decide)

example : (Language.ofSlices (modGate 3))ᶜ ∉ AC0Mod 2 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  compl_modGate_notMem_AC0Mod (by decide)

example : Language.ofSlices (modGate 2) ∉ AC0Mod 3 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  modGate_notMem_AC0Mod (by decide)

example : Language.ofSlices (modGate 5) ∉ AC0Mod 3 :=
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  modGate_notMem_AC0Mod (by decide)

example : ∃ L : Language Bool, L ∈ ACC0 ∧ L ∉ AC0Mod 2 ∧ Lᶜ ∈ ACC0 ∧ Lᶜ ∉ AC0Mod 2 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ⟨Language.ofSlices (modGate 3), modGate_mem_ACC0 3, modGate_notMem_AC0Mod (by decide),
    ACC0.compl (modGate_mem_ACC0 3), compl_modGate_notMem_AC0Mod (by decide)⟩

end CslibFrontierTests.Computability.Circuit.Boolean.Smolensky
