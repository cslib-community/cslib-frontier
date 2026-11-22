/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.AffineDisperser
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.PolyTime

/-!
# Explicit `4N - o(N)` circuit lower bounds in `P` and stratified Farkas optimality

This module packages three families of consequences of `four_mul_le_cost_add` and
`four_mul_le_size_add`:

* **Unconditional `4N - O(N ^ (4 / 5))` lower bound in `P`**: instantiating `four_mul_le_cost_add`
  at `Li.primeDisperser` (`CslibFrontier.Computability.Complexity.AffineDisperser.Li.PolyTime`,
  Milestone 1 toward `#4323`) yields an unconditional language in `P` requiring at least
  `4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates (`binaryB2Cost`, with constants and
  negations free), and hence at least `4 * N - 19332 * N ^ (4 / 5)` total gates, for all
  sufficiently large `N` (`exists_mem_P_eventually_four_mul_sub_le_cost_primeDisperser`,
  `exists_mem_P_eventually_four_mul_sub_le_size_primeDisperser`). Achieving `4n - O(log n)`
  (`Theorem 1.1` per `#4322`) remains open pending an `O(log n)`-dimension disperser (`#4323`).
* **Explicit `4N - O(N / log N)` lower bound via `explicitDisperser`**: instantiating at
  `explicitDisperser` improves the constant from `60 * N / (Nat.log 2 N + 1) + 10` to
  `54 * N / (Nat.log 2 N + 1) + 9` under both `binaryB2Cost` and `size`
  (`exists_mem_P_eventually_four_mul_sub_le_cost`, `exists_mem_P_eventually_four_mul_sub_le_size`).
* **Weight and stratified Farkas optimality**:
  - For uniform `0/α` weights `(α, β, c)` under the tightened 3-deletion Case 5a-opposite
    constraint `c ≤ 2 * β + 3` (replacing `#4322`'s `c ≤ 2 * β + 2`), `c - α ≤ 4`
    (`weight_sub_le_four`) and `c - α = 4` forces `3 ≤ β`, `5 ≤ α`, `9 ≤ c`, and `α = β + 2`
    (`weight_lower_bounds_of_sub_eq_four`).
  - **Original bigraded Farkas `4n` optimality** (`stratified_weight_sub_le_four`,
    `stratified_weight_lower_bounds_of_sub_eq_four`, not from `[MishraSanthanam2027]`): even if a
    potential assigns an independent equation weight `ce`, arbitrary bigraded unpaired weights
    `w dg de`, and arbitrary bigraded pair weights `bp dg₁ de₁ dg₂ de₂`, the concrete
    `moveAffine` + `PairInSystem` (`unitDelete`) + `Case 5b` (`PC`) cycle forces
    `c - w_init ≤ 4`, and attaining `c - w_init = 4` alongside Case 5a-opposite still forces
    `ce = 1`, `3 ≤ bp 1 0 1 0`, `5 ≤ w_init`, and `9 ≤ c`.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.weight_sub_le_four`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.weight_lower_bounds_of_sub_eq_four`: optimality of
  `(α, β, c) = (5, 3, 9)` for uniform `0/α` weights.
* `Cslib.Circuits.Boolean.AffineDisperser4n.stratified_weight_sub_le_four`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.stratified_weight_lower_bounds_of_sub_eq_four`:
  original bigraded Farkas optimality of `4n - 9d`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_four_mul_sub_le_cost`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_four_mul_sub_le_size`:
  explicit `4N - O(N / log N)` lower bounds via `explicitDisperser`.
* `exists_mem_P_eventually_four_mul_sub_le_cost_primeDisperser`,
  `exists_mem_P_eventually_four_mul_sub_le_size_primeDisperser`:
  explicit `4N - O(N ^ (4 / 5))` lower bounds in `P` via `Li.primeDisperser`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; `#4322`
  records `4n - 10d` with `(6, 4, 10)`, whereas `(5, 3, 9)`, `binaryB2Cost`, the
  `Li.primeDisperser` instantiation, and the bigraded Farkas optimality theorems are original to
  this formalization)
* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Filter Cslib.Circuits Cslib.Circuits.Boolean.SemiCircuit Cslib.Complexity
open Cslib.AffineDisperser

/-! ### Optimality of `(α, β, c) = (5, 3, 9)` and bigraded Farkas `4n` barrier -/

/-- Upper bound on the coefficient of `n` (recorded in `#4322`, label `Remark 4.3` unverified
against [MishraSanthanam2027]): under `α ≤ β + 2` and `c ≤ 2 * α - β + 2`, the leading coefficient
`c - α` cannot exceed `4`. -/
theorem weight_sub_le_four {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * α - β + 2) :
    c - α ≤ 4 := by
  linarith

/-- Optimality of `α = 5, β = 3, c = 9` under the tightened 3-deletion Case 5a-opposite constraint
`c ≤ 2 * β + 3` (original refinement of `#4322`'s `c ≤ 2 * β + 2`): any rational weight triple
`(α, β, c)` satisfying the gate-elimination constraints and achieving `c - α = 4` satisfies
`3 ≤ β`, `5 ≤ α`, `9 ≤ c`, and `α = β + 2`. -/
theorem weight_lower_bounds_of_sub_eq_four {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * β + 3)
    (h₃ : c ≤ 2 * α - β + 2) (h₄ : c - α = 4) :
    3 ≤ β ∧ 5 ≤ α ∧ 9 ≤ c ∧ α = β + 2 :=
  ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Original bigraded Farkas `4n` barrier**: for any potential assigning unit gate cost, equation
cost `ce`, bigraded unpaired parameter weights `w dg de` (`dg` gate-children, `de`
equation-children), bigraded zero-locus pair weights `bp dg₁ de₁ dg₂ de₂`, slope `c`, and initial
per-input weight bound `w_init` covering fan-out-`2` inputs (`w 2 0 ≤ w_init`), if the potential is
nonincreasing across:
1. `moveAffine` on an XOR gate reading a paired parameter and an auxiliary variable (`ce ≤ 1`),
2. `PairInSystem` + `unitDelete` swapping that paired parameter with an auxiliary variable of
   gate-degree `2` (`w 2 0 ≤ bp 1 0 1 0 + 1 + ce`), and
3. `Case 5b` pair creation on two `(2, 0)` unpaired parameters
   (`c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2`),
then `c - w_init ≤ 4`. -/
theorem stratified_weight_sub_le_four {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ}
    {ce c w_init : ℚ}
    (h_init : w 2 0 ≤ w_init)
    (h_move : ce ≤ 1)
    (h_pis : w 2 0 ≤ bp 1 0 1 0 + 1 + ce)
    (h_pc : c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2) :
    c - w_init ≤ 4 := by
  linarith

/-- **Original bigraded Pareto-optimality of `(ce, β, w_init, c) = (1, 3, 5, 9)`**: in any
bigraded `(dg, de)` potential satisfying the hypotheses of `stratified_weight_sub_le_four` together
with the 3-deletion Case 5a-opposite bound `c ≤ 2 * bp 1 0 1 0 + 3` and attaining `c - w_init = 4`,
every step of the equational Farkas cycle holds with equality and `ce = 1`, `3 ≤ bp 1 0 1 0`,
`5 ≤ w 2 0`, `5 ≤ w_init`, and `9 ≤ c`. -/
theorem stratified_weight_lower_bounds_of_sub_eq_four {w : ℕ → ℕ → ℚ}
    {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {ce c w_init : ℚ}
    (h_init : w 2 0 ≤ w_init)
    (h_move : ce ≤ 1)
    (h_pis : w 2 0 ≤ bp 1 0 1 0 + 1 + ce)
    (h_pc : c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2)
    (h_aop : c ≤ 2 * bp 1 0 1 0 + 3)
    (h_opt : c - w_init = 4) :
    ce = 1 ∧ 3 ≤ bp 1 0 1 0 ∧ 5 ≤ w 2 0 ∧ 5 ≤ w_init ∧ 9 ≤ c ∧ w 2 0 = bp 1 0 1 0 + 2 :=
  ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Original `(D1)`-rerouting bound on fan-out-`1` weights**: if `(D1)` deletion of a fan-out-`2`
degenerate gate rerouting into a `(1, 0)` parameter is also nonincreasing (`w 2 0 ≤ w 1 0 + 1`),
then even the fan-out-`1` weight satisfies `w_init - 1 ≤ w 1 0` whenever `c - w_init = 4` under
`stratified_weight_lower_bounds_of_sub_eq_four`, forcing `4 ≤ w 1 0`. -/
theorem stratified_fanout_one_lower_bound {w : ℕ → ℕ → ℚ}
    {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {ce c w_init : ℚ}
    (h_init : w 2 0 ≤ w_init)
    (h_reroute : w 2 0 ≤ w 1 0 + 1)
    (h_move : ce ≤ 1)
    (h_pis : w 2 0 ≤ bp 1 0 1 0 + 1 + ce)
    (h_pc : c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2)
    (h_aop : c ≤ 2 * bp 1 0 1 0 + 3)
    (h_opt : c - w_init = 4) :
    4 ≤ w 1 0 := by
  have := stratified_weight_lower_bounds_of_sub_eq_four h_init h_move h_pis h_pc h_aop h_opt
  linarith

/-! ### Explicit `4N - O(N / log N)` lower bounds for `explicitDisperser` -/

/-- The `4n - 9d` binary-gate lower bound (`four_mul_le_cost_add`) instantiated at
`explicitDisperser N`. -/
theorem four_mul_le_cost_add_explicitThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser N))) :
    4 * N ≤ C.program.cost binaryB2Cost + 9 * (explicitThreshold N + 1) :=
  four_mul_le_cost_add (isAffineDisperser_explicitDisperser N) C hC

/-- The `4n - 9d` size lower bound (`four_mul_le_size_add`) instantiated at
`explicitDisperser N`. -/
theorem four_mul_le_size_add_explicitThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser N))) :
    4 * N ≤ C.size + 9 * (explicitThreshold N + 1) :=
  four_mul_le_size_add (isAffineDisperser_explicitDisperser N) C hC

/-- Asymptotic natural-number binary-gate lower bound for `explicitDisperser N`:
eventually `4 * N ≤ C.program.cost binaryB2Cost + 54 * N / (Nat.log 2 N + 1) + 9`. -/
theorem eventually_four_mul_le_cost_add_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * N ≤ C.program.cost binaryB2Cost + 54 * N / (Nat.log 2 N + 1) + 9 := by
  filter_upwards [eventually_explicitThreshold_le] with N hth C hC
  have hlb := four_mul_le_cost_add_explicitThreshold C hC
  have hdiv : explicitThreshold N ≤ 6 * N / (Nat.log 2 N + 1) :=
    Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2 (by linarith)
  have hmul : 9 * (6 * N / (Nat.log 2 N + 1)) ≤ 54 * N / (Nat.log 2 N + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos _)]
    have := Nat.div_mul_le_self (6 * N) (Nat.log 2 N + 1)
    calc
      9 * (6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)
        = 9 * ((6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)) := by ring
      _ ≤ 9 * (6 * N) := Nat.mul_le_mul_left 9 this
      _ = 54 * N := by ring
  omega

/-- Asymptotic natural-number size lower bound for `explicitDisperser N`:
eventually `4 * N ≤ C.size + 54 * N / (Nat.log 2 N + 1) + 9`. -/
theorem eventually_four_mul_le_size_add_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * N ≤ C.size + 54 * N / (Nat.log 2 N + 1) + 9 := by
  filter_upwards [eventually_four_mul_le_cost_add_explicitDisperser] with N hN C hC
  have := hN C hC
  have := cost_binaryB2Cost_le_size C
  omega

/-- Asymptotic real binary-gate lower bound for `explicitDisperser N`:
eventually `4 * N - 54 * N / (Nat.log 2 N + 1) - 9 ≤ C.program.cost binaryB2Cost`. -/
theorem eventually_four_mul_sub_le_cost_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤
        (C.program.cost binaryB2Cost : ℝ) := by
  filter_upwards [eventually_four_mul_le_cost_add_explicitDisperser] with N hN C hC
  have hlb : (4 * N : ℝ) ≤
      (C.program.cost binaryB2Cost : ℝ) + ((54 * N / (Nat.log 2 N + 1) : ℕ) : ℝ) + 9 := by
    exact_mod_cast hN C hC
  have hdiv : ((54 * N / (Nat.log 2 N + 1) : ℕ) : ℝ) ≤
      54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_mul] using
      (Nat.cast_div_le (α := ℝ) (m := 54 * N) (n := Nat.log 2 N + 1))
  linarith

/-- Asymptotic real size lower bound for `explicitDisperser N`:
eventually `4 * N - 54 * N / (Nat.log 2 N + 1) - 9 ≤ C.size`. -/
theorem eventually_four_mul_sub_le_size_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤ (C.size : ℝ) := by
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_explicitDisperser] with N hN C hC
  have hle : (C.program.cost binaryB2Cost : ℝ) ≤ (C.size : ℝ) := by
    exact_mod_cast cost_binaryB2Cost_le_size C
  linarith [hN C hC]

/-- There exists an explicit language in `P` (`explicitDisperserLanguage`) whose `N`-bit slices
require at least `4 * N - 54 * N / (Nat.log 2 N + 1) - 9` genuinely binary `B₂` gates. -/
theorem exists_mem_P_eventually_four_mul_sub_le_cost :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤
          (C.program.cost binaryB2Cost : ℝ) := by
  refine ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, ?_⟩
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_explicitDisperser] with N hN C hC
  rw [slice_explicitDisperserLanguage] at hC
  exact hN C hC

/-- There exists an explicit language in `P` (`explicitDisperserLanguage`) whose `N`-bit slices
require Boolean circuits of size at least `4 * N - 54 * N / (Nat.log 2 N + 1) - 9`. -/
theorem exists_mem_P_eventually_four_mul_sub_le_size :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤ (C.size : ℝ) := by
  refine ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, ?_⟩
  filter_upwards [eventually_four_mul_sub_le_size_of_computes_explicitDisperser] with N hN C hC
  rw [slice_explicitDisperserLanguage] at hC
  exact hN C hC

/-! ### Unconditional `4N - O(N ^ (4 / 5))` lower bounds in `P` via `Li.primeDisperser` -/

/-- Concrete `4n - 9d` binary-gate lower bound for `Li.primeDisperser N`. -/
theorem four_mul_le_cost_add_primeThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (Li.primeDisperser N))) :
    4 * N ≤ C.program.cost binaryB2Cost + 9 * (Li.primeThreshold N + 1) :=
  four_mul_le_cost_add (Li.isAffineDisperser_primeDisperser N) C hC

/-- Concrete `4n - 9d` size lower bound for `Li.primeDisperser N`. -/
theorem four_mul_le_size_add_primeThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (Li.primeDisperser N))) :
    4 * N ≤ C.size + 9 * (Li.primeThreshold N + 1) :=
  four_mul_le_size_add (Li.isAffineDisperser_primeDisperser N) C hC

/-- Every `fullSignature 2 Bool` circuit computing `Li.primeDisperser N` requires at least
`4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates (`binaryB2Cost`) for all sufficiently
large `N`. -/
theorem eventually_four_mul_sub_le_cost_of_computes_primeDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (Li.primeDisperser N)) →
      4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.program.cost binaryB2Cost : ℝ) := by
  filter_upwards [Li.eventually_primeThreshold_real_le] with N hleR C hC
  have hnatR : (4 : ℝ) * (N : ℝ) ≤
      (C.program.cost binaryB2Cost : ℝ) + 9 * ((Li.primeThreshold N + 1 : ℕ) : ℝ) := by
    exact_mod_cast four_mul_le_cost_add_primeThreshold C hC
  linarith

/-- Every `fullSignature 2 Bool` circuit computing `Li.primeDisperser N` has total size at least
`4 * N - 19332 * N ^ (4 / 5)` for all sufficiently large `N`. -/
theorem eventually_four_mul_sub_le_size_of_computes_primeDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (Li.primeDisperser N)) →
      4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) := by
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_primeDisperser] with N hN C hC
  have hle : (C.program.cost binaryB2Cost : ℝ) ≤ (C.size : ℝ) := by
    exact_mod_cast cost_binaryB2Cost_le_size C
  linarith [hN C hC]

/-- Unconditional explicit language in `P` (`Li.primeDisperserLanguage`) whose `N`-bit slices
eventually require at least `4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates
(`binaryB2Cost`, with constants and unary negations free). -/
theorem exists_mem_P_eventually_four_mul_sub_le_cost_primeDisperser :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.program.cost binaryB2Cost : ℝ) :=
  ⟨Li.primeDisperserLanguage, Li.primeDisperserLanguage_mem_P, by
    simpa only [Li.slice_primeDisperserLanguage] using
      eventually_four_mul_sub_le_cost_of_computes_primeDisperser⟩

/-- Unconditional explicit language in `P` (`Li.primeDisperserLanguage`) whose `N`-bit slices
eventually require Boolean circuits of total size at least `4 * N - 19332 * N ^ (4 / 5)`. -/
theorem exists_mem_P_eventually_four_mul_sub_le_size_primeDisperser :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) :=
  ⟨Li.primeDisperserLanguage, Li.primeDisperserLanguage_mem_P, by
    simpa only [Li.slice_primeDisperserLanguage] using
      eventually_four_mul_sub_le_size_of_computes_primeDisperser⟩

end Cslib.Circuits.Boolean.AffineDisperser4n
