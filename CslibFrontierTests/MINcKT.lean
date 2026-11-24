/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Kolmogorov.MKtP
import CslibFrontier.Computability.Kolmogorov.MINcKT

/-!
# Tests for `MKtP`, `condUniversalTM`, and `MINcKT`

Representative `module` client and concrete non-vacuity checks for
`CslibFrontier.Computability.Kolmogorov.MKtP`,
`CslibFrontier.Computability.Kolmogorov.Conditional`, and
`CslibFrontier.Computability.Kolmogorov.MINcKT` across ordinary `import`s.
-/

namespace Cslib.Kolmogorov.Tests

open Cslib.Complexity Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod
open _root_.Turing.MultiTapeTM

/-! ### `MKtPInstance`, `encMKtP`, `MKtP.boundedSearch`, and `GapMKtP` checks -/

-- `encMKtP` preserves the exact encoded words of `encPair encBits encUnary` definitionally.
example (x : List Bool) (k : ℕ) :
    encMKtP ⟨x, k⟩ = encPair encBits encUnary (x, k) :=
  rfl

-- Generated `enc_structure` certificates and `@[fun_prop]` composition for `MKtPInstance` and
-- `MKtP.boundedSearch` across an ordinary `module` import.
example :
    ComputableInPolyTime
      (fun q : MKtPInstance × ℕ => MKtP.boundedSearch ⟨q.1.word, q.1.threshold⟩ q.2)
      (encPair encMKtP encUnary) encBool := by
  fun_prop

-- Concrete yes-instances of `MKtP` and `MKtP.boundedSearch` from `levinKt_le_length_add`.
example (x : List Bool) :
    let k := x.length + copyOverhead + Nat.clog 2 (x.length + 1)
    (⟨x, k⟩ : MKtPInstance) ∈ MKtP ∧ MKtP.boundedSearch ⟨x, k⟩ (2 ^ (k + 1)) = true := by
  intro k
  have hmem : (⟨x, k⟩ : MKtPInstance) ∈ MKtP := MKtP.mk_mem_iff.mpr (levinKt_le_length_add x)
  exact ⟨hmem, (MKtP.boundedSearch_eq_true_iff_of_two_pow_le le_rfl).mpr hmem⟩

-- Concrete no-instances of `MKtP` and `MKtP.boundedSearch` from `exists_length_eq_le_ecomplexity`
-- and `plain_le_levinKt`.
example (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : List Bool, x.length = n ∧ (⟨x, n - 1⟩ : MKtPInstance) ∉ MKtP ∧
      MKtP.boundedSearch ⟨x, n - 1⟩ (2 ^ n) = false := by
  obtain ⟨x, hx, hplain⟩ := universalTM.exists_length_eq_le_ecomplexity n
  have hnot : (⟨x, n - 1⟩ : MKtPInstance) ∉ MKtP := by
    rw [MKtP.mk_mem_iff]
    intro hle
    have h1 : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := (hplain.trans (plain_le_levinKt x)).trans hle
    have h2 : n ≤ n - 1 := ENat.natCast_le_natCast.mp h1
    omega
  have hpow : 2 ^ ((n - 1) + 1) ≤ 2 ^ n := by
    rw [Nat.sub_add_cancel hn]
  refine ⟨x, hx, hnot, ?_⟩
  rw [Bool.eq_false_iff]
  exact mt (MKtP.boundedSearch_eq_true_iff_of_two_pow_le hpow).mp hnot

-- Concrete strict-gap `GapMKtP` promise problem (`copyOverhead < copyOverhead + n / 2` for `2 ≤ n`)
-- admitting both a yes-instance (`[]`) and a no-instance of length `2 * copyOverhead + 2`.
example :
    let s₁ : ℕ → ℕ := fun _ => copyOverhead
    let s₂ : ℕ → ℕ := fun n => copyOverhead + n / 2
    let hs : ∀ n, s₁ n ≤ s₂ n := fun _ => Nat.le_add_right _ _
    (∀ n, 2 ≤ n → s₁ n < s₂ n) ∧
      [] ∈ (GapMKtP s₁ s₂ hs).yes ∧
      ∃ x : List Bool, x.length = 2 * copyOverhead + 2 ∧ x ∈ (GapMKtP s₁ s₂ hs).no := by
  intro s₁ s₂ hs
  refine ⟨fun n hn => by dsimp only [s₁, s₂]; omega, ?_, ?_⟩
  · rw [GapMKtP.yes_eq, mem_MKtPAt_iff]
    simpa [s₁] using levinKt_le_length_add []
  · set n := 2 * copyOverhead + 2
    obtain ⟨x, hx, hplain⟩ := universalTM.exists_length_eq_le_ecomplexity n
    refine ⟨x, hx, ?_⟩
    rw [GapMKtP.no_eq, GapMKtP.mem_noSet_iff]
    have hlt : ((s₂ x.length : ℕ) : ℕ∞) < (n : ℕ∞) := by
      rw [ENat.natCast_lt_natCast, hx]
      dsimp only [s₂, n]
      omega
    exact hlt.trans_le (hplain.trans (plain_le_levinKt x))

-- `LiuPass2021Crypto, Fact 3.1`: at least one string of length `n` has an optimal `Kt`-witness
-- running in at most `2 ^ (copyOverhead + Nat.clog 2 (n + 1) + 1)` steps when `1 ≤ n`.
example (n : ℕ) (hn : 1 ≤ n) :
    0 < {x : List Bool | x.length = n ∧
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧
          p.length + Nat.clog 2 s ≤ levinKtNat x ∧
            s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + 1)}.ncard := by
  have h := two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow hn
  have hpow : 2 ^ (n - 1) < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ### `condUniversalTM` and `MINcKT` non-vacuity checks -/

-- At 0 steps, no instance belongs to `MINcKT`, and `MINcKT.check` returns `false`.
example (x y : List Bool) (s : ℕ) : (⟨x, y, 0, s⟩ : MINcKT.Instance) ∉ MINcKT := by
  simp [MINcKT.mk_mem_iff]

example (x y p : List Bool) (s : ℕ) :
    MINcKT.check (⟨x, y, 0, s⟩, p) = false := by
  simp [MINcKT.check]

-- Concrete yes-instances of `MINcKT` from self-conditioning (`exists_condTimeBoundedAt_self_le`).
example : ∃ (q : Polynomial ℕ) (c : ℕ), ∀ y : List Bool,
    (⟨y, y, q.eval (y.length + 1), c⟩ : MINcKT.Instance) ∈ MINcKT := by
  obtain ⟨q, c, _, _, hbound, _⟩ := exists_condTimeBoundedAt_self_le
  exact ⟨q, c, fun y => MINcKT.mk_mem_iff.mpr (hbound y le_rfl)⟩

-- Concrete no-instances of `MINcKT` from conditional incompressibility
-- (`exists_length_eq_forall_le_condTimeBoundedAt`).
example (y : List Bool) (n t : ℕ) (hn : 1 ≤ n) :
    ∃ x : List Bool, x.length = n ∧ (⟨x, y, t, n - 1⟩ : MINcKT.Instance) ∉ MINcKT := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_condTimeBoundedAt y n
  refine ⟨x, hx, ?_⟩
  rw [MINcKT.mk_mem_iff]
  intro hle
  have h1 : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := (hall t).trans hle
  have h2 : n ≤ n - 1 := ENat.natCast_le_natCast.mp h1
  omega

end Cslib.Kolmogorov.Tests
