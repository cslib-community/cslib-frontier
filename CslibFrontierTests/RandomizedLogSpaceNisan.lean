/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.Nisan
import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON

/-! Nisan's generator against randomized logarithmic space: the closure hypotheses are met by the
reachable views under any space bound, the generator with no hash seeds is exact, and the `BPL`
majority step applies to a concrete language. -/

set_option linter.privateModule false

namespace CslibFrontierTests.RandomizedLogSpaceNisan

open Cslib.Complexity Turing

variable {k : ℕ} {State : Type} (M : MultiTapePTM k Bool State)

-- The hypotheses of the fooling bound are met under any space bound, by the reachable views,
-- whose number bounds the error.
example [Finite State] {input : List Bool} {s : ℕ} (hs : M.toNTM.RunsInSpace input s)
    (n r : ℕ) : ∃ V : Finset (FiniteCfg k Bool State),
      V.card ≤ 2 ^ (2 * MultiTapeNTM.coreLengthBound k State input.length s + 1) ∧
      |(M.acceptNisanSeeds input n r : ℝ) / 2 ^ (n + r * (3 * n - 1)) -
          (M.acceptCoins input (2 ^ r * n) : ℝ) / 2 ^ (2 ^ r * n)| ≤
        (2 ^ r - 1) * V.card / (2 * √(2 ^ n)) := by
  obtain ⟨V, hreach, hV, hcard⟩ := M.exists_finset_reachable hs
  exact ⟨V, hcard, M.abs_acceptNisanSeeds_div_sub_le hV ((hreach _).mpr .refl) n r⟩

-- Boundary `r = 0`: with no hash seeds the generator outputs its seed block, the error bound is
-- `0`, and the fraction of accepted seeds is exactly the fraction of accepted coin strings.
example {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, M.viewCoinStep finite bit ∈ V)
    (hinit : M.toNTM.initView input ∈ V) (n : ℕ) :
    (M.acceptNisanSeeds input n 0 : ℝ) / 2 ^ n = (M.acceptCoins input n : ℝ) / 2 ^ n := by
  have h := M.abs_acceptNisanSeeds_div_sub_le hV hinit n 0
  simp only [pow_zero, one_mul, zero_mul, add_zero, sub_self, zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

-- The program reads exactly the coins the machine reads: it accepts a coin string exactly when
-- the machine's replay of it accepts.
example {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, M.viewCoinStep finite bit ∈ V)
    (hinit : M.toNTM.initView input ∈ V) {t : ℕ} :
    (Finset.univ.filter fun w : Fin t → Bool => (M.coinProgram hV hinit t).eval w = true).card =
      M.acceptCoins input t := by
  classical
  unfold MultiTapePTM.acceptCoins
  exact congrArg Finset.card
    (Finset.filter_congr fun w _ => MultiTapePTM.eval_coinProgram_iff hV hinit w)

-- The `BPL` majority step applies to undirected connectivity, which is in `L ⊆ BPL`; the
-- parameters are explicit in the input length.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c d : ℕ),
    (∀ G, M.toNTM.RunsInSpace (encUSTCON G) (c * (Nat.log2 (encUSTCON G).length + 1))) ∧
    ∀ G r n, r = d * (Nat.log2 (encUSTCON G).length + 2) + 1 → n = 2 * (2 * r + 3) →
      n + r * (3 * n - 1) ≤ 39 * (2 * d + 1) ^ 2 * (Nat.log2 (encUSTCON G).length + 1) ^ 2 ∧
      (G ∈ USTCON → 2 ^ (n + r * (3 * n - 1)) < 2 * M.acceptNisanSeeds (encUSTCON G) n r) ∧
      (G ∉ USTCON → 2 * M.acceptNisanSeeds (encUSTCON G) n r < 2 ^ (n + r * (3 * n - 1))) :=
  exists_acceptNisanSeeds_of_mem_BPL (L_subset_BPL USTCON_mem_L)

-- Boundary of the seed-length bound: at `d = 0` (so `r = 1` and `n = 10`) the seed has
-- `10 + 1 * 29 = 39` bits, so the bound `39 (2 d + 1) ^ 2 (log₂ m + 1) ^ 2` is attained when
-- `log₂ m = 0`; the constant `39` cannot be lowered.
example : (10 : ℕ) + 1 * (3 * 10 - 1) = 39 * (2 * 0 + 1) ^ 2 * (0 + 1) ^ 2 := by decide

end CslibFrontierTests.RandomizedLogSpaceNisan
