/-
Copyright (c) 2026 Carlos Toledo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlos Toledo
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
public import CslibFrontier.Computability.WordRAM.OfTuring.Space
import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Subexponential `k`-SAT on the word RAM

`Cslib.Complexity.CountingNativeEndpoint.decidableInSubexpTime_KSAT` decides `k`-SAT on multi-tape
machines in time `2 ^ (δ * n)` times a polynomial, for every `δ > 0`. Its consequence `not_ETH`
passes through `Cslib.Complexity.DecidableInTimeO`, which forgets the work space of the decider.
Here the decider is rebuilt from the native model counter
`Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter`, whose `ComputableInO` contract
keeps the polynomial work space, composed with the polynomial-time width check and the test
`0 < count`. Because the work space is polynomial,
`Cslib.WordRAM.uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace` carries the decider to
one fixed word-RAM program at logarithmic word size, although its running time is not polynomially
bounded, so `Cslib.WordRAM.DTIME_subset_RAMTIME_additive` does not apply.

The word RAM reads the bits of `encCNF φ`, one bit per word, as in `Cslib.WordRAM.RAMTIME`. For
`k = 3`, `Cslib.WordRAM.uniformDecidableInTimeLogWord_KSAT` says that the exponential time
hypothesis `Cslib.Complexity.ETH`, read on the word RAM over `Basis.additive` with words of
`O(log L)` bits, fails as well.

## Main results

* `Cslib.Complexity.CountingNativeEndpoint.exists_decidableInTimeAndSpace_KSAT`: one multi-tape
  machine decides `k`-SAT within time `2 ^ (A * interpolationScale n)` times a polynomial and
  within polynomial work space.
* `Cslib.WordRAM.uniformDecidableInTimeLogWord_KSAT`: for every `δ > 0`, one fixed program over
  `Basis.additive` decides `k`-SAT within `c * (⌈2 ^ (δ * n)⌉ * (L + 1) ^ e) + c` instructions, at
  every word size above a logarithmic threshold in `L`.
-/

public section

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- **`k`-SAT with its work space.** One binary multi-tape machine decides `KSAT k` on
`encCNF φ` within time `c * (⌈2 ^ (A * interpolationScale n)⌉ * (L + 1) ^ E)` and work space
`c * (L + 1) ^ E`, where `n = φ.numVars` and `L = |encCNF φ|`. -/
theorem exists_decidableInTimeAndSpace_KSAT (k : ℕ) :
    ∃ (t s : CNF ℕ → ℕ) (A E c : ℕ), DecidableInTimeAndSpace (KSAT k) encCNF t s ∧
      (∀ φ, t φ ≤ c * (⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
        ((encCNF φ).length + 1) ^ E)) ∧
      (∀ φ, s φ ≤ c * ((encCNF φ).length + 1) ^ E) := by
  obtain ⟨count, A, e, b, hspec, hcount⟩ := exists_modelCounter k
  obtain ⟨c₀, -, hlen⟩ := id hcount
  obtain ⟨dw, _, hw⟩ := (computableInPolyTime_all_length_le k).exists_degree
  obtain ⟨dp, _, hp⟩ := ComputableInPolyTime.binary_pos.exists_degree
  obtain ⟨c, htm, -⟩ := hw.inO.ite (hp.inO.comp hcount) (ComputableInO.const false)
  set E := dw + e + b + b * dp + 1
  set F := 4 + (2 * c₀ + 1) ^ dp
  have hbound (φ : CNF ℕ) {M B : ℕ} (hM : ((encCNF φ).length + 1) ^ E ≤ M) (hB : B ≤ M) :
      c * (((encCNF φ).length + 1) ^ dw +
        (if (φ.all fun c => decide (c.length ≤ k)) = true then
          B + ((encNat (count φ)).length + 1) ^ dp
        else (encCNF φ).length) + 1) ≤ c * F * M := by
    set Y := (encCNF φ).length + 1
    have hY : 1 ≤ Y := Nat.le_add_left 1 _
    have hYb : 1 ≤ Y ^ b := Nat.one_le_pow _ _ hY
    have hdw : Y ^ dw ≤ M := (Nat.pow_le_pow_right hY (by omega)).trans hM
    have h1 : Y ≤ M := (Nat.le_self_pow (by omega) _).trans hM
    have hl : (encNat (count φ)).length + 1 ≤ (2 * c₀ + 1) * Y ^ b :=
      calc (encNat (count φ)).length + 1
          ≤ c₀ * (Y ^ b + 1) + 1 := Nat.add_le_add_right (hlen φ) 1
        _ ≤ c₀ * (Y ^ b + Y ^ b) + Y ^ b := by gcongr
        _ = (2 * c₀ + 1) * Y ^ b := by ring
    have hp : ((encNat (count φ)).length + 1) ^ dp ≤ (2 * c₀ + 1) ^ dp * M :=
      calc ((encNat (count φ)).length + 1) ^ dp
          ≤ ((2 * c₀ + 1) * Y ^ b) ^ dp := Nat.pow_le_pow_left hl dp
        _ = (2 * c₀ + 1) ^ dp * Y ^ (b * dp) := by rw [mul_pow, ← pow_mul]
        _ ≤ (2 * c₀ + 1) ^ dp * Y ^ E :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))
        _ ≤ (2 * c₀ + 1) ^ dp * M := Nat.mul_le_mul_left _ hM
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c ?_
    simp only [F, Nat.add_mul]
    split <;> omega
  refine ⟨_, _, A, E, c * F, decidableInTimeAndSpace_iff.mpr ⟨_, htm, fun φ => ?_⟩,
    fun φ => ?_, fun φ => ?_⟩
  · -- correctness
    simp only [KSAT, Set.mem_ofPred_eq, Function.comp_apply]
    by_cases hwid : (φ.all fun c => decide (c.length ≤ k)) = true
    · have hwid' : ∀ c ∈ φ, c.length ≤ k := by simpa using hwid
      simp only [hwid, ↓reduceIte]
      rw [hspec φ hwid', decide_eq_true_iff, CNF.modelCount_pos_iff]
      exact ⟨fun h => h.2, fun h => ⟨hwid', h⟩⟩
    · simp only [hwid, Bool.false_eq_true, ↓reduceIte, iff_false, not_and]
      intro h
      exact absurd (by simpa using h) hwid
  · -- time
    exact hbound φ (Nat.le_mul_of_pos_left _ (Nat.ceil_pos.mpr (by positivity)))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.le_add_left 1 _) (show e ≤ E by omega)))
  · -- space
    exact hbound φ le_rfl (Nat.pow_le_pow_right (Nat.le_add_left 1 _) (show b ≤ E by omega))

end Cslib.Complexity.CountingNativeEndpoint

namespace Cslib.WordRAM

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-- **Subexponential `k`-SAT on the word RAM.** For every `δ > 0`, one fixed program over
`Basis.additive`, run on the bits of `encCNF φ`, decides `KSAT k` within
`c * (⌈2 ^ (δ * n)⌉ * (L + 1) ^ e) + c` instructions, where `n = φ.numVars` and
`L = |encCNF φ|`, at every word size `w ≥ logWidth k' L` for a constant `k' > 0`. -/
theorem uniformDecidableInTimeLogWord_KSAT (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c e : ℕ, UniformDecidableInTimeLogWord .additive (KSAT k)
      (fun _ φ => (encCNF φ).map Bool.toNat) (fun φ => (encCNF φ).length)
      (fun φ _ => c * (⌈(2 : ℝ) ^ (δ * φ.numVars)⌉₊ * ((encCNF φ).length + 1) ^ e) + c) := by
  obtain ⟨t, s, A, E, c, hd, ht, hs⟩ := CountingNativeEndpoint.exists_decidableInTimeAndSpace_KSAT k
  obtain ⟨C, k', hk', hU⟩ := uniformDecidableInTimeLogWord_of_decidableInTimeAndSpace hd hs
  obtain ⟨K, -, hK⟩ := SubexponentialSAT.exists_two_pow_mul_interpolationScale_le (A : ℝ) hδ
  refine ⟨C * c * ⌈K⌉₊ + C, E, k', hk', hU.mono (fun φ _ => ?_) (fun _ _ h => h) hU.inputAdmissible⟩
  set X := ⌈(2 : ℝ) ^ ((A : ℝ) * SubexponentialSAT.interpolationScale φ.numVars)⌉₊ with hXdef
  set Z := ⌈(2 : ℝ) ^ (δ * φ.numVars)⌉₊
  set Y := (encCNF φ).length + 1
  have hXZ : X ≤ ⌈K⌉₊ * Z := Nat.ceil_le.mpr <| by
    push_cast
    exact (hK φ.numVars).trans <|
      mul_le_mul (Nat.le_ceil K) (Nat.le_ceil _) (by positivity) (by positivity)
  have h1 : C * t φ ≤ (C * c * ⌈K⌉₊ + C) * (Z * Y ^ E) :=
    calc C * t φ ≤ C * (c * (X * Y ^ E)) := Nat.mul_le_mul_left _ (ht φ)
      _ ≤ C * (c * (⌈K⌉₊ * Z * Y ^ E)) := by gcongr
      _ = C * c * ⌈K⌉₊ * (Z * Y ^ E) := by ring
      _ ≤ (C * c * ⌈K⌉₊ + C) * (Z * Y ^ E) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  change C * t φ + C ≤ (C * c * ⌈K⌉₊ + C) * (Z * Y ^ E) + (C * c * ⌈K⌉₊ + C)
  omega

end Cslib.WordRAM
