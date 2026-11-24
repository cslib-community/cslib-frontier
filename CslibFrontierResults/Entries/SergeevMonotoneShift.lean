/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Monotone.Shift

/-!
# Collected results: monotone circuit complexity of cyclic shift and permutation operators
-/

register_result "sergeev-monotone-shift-upper-bound" where
  title := "Monotone cyclic shift has gate complexity at most L(A) + O(q n log n), \
    and O(q n log n) on one-hot and dual-rail antichains"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2020MonotoneShift,
      theorem := "Theorem 1 (and A₀, A₁ corollaries)",
      locator := "Upper complexity bounds, pp. 3–4 (arXiv:1905.10747v2)" }
  ]
  theorems := [
    Cslib.Circuits.Monotone.computesMonotoneShift_monotoneShiftCircuit,
    Cslib.Circuits.Monotone.cost_monotoneShiftCircuit_le,
    Cslib.Circuits.Monotone.computesMonotoneShift_oneHotShiftCircuit,
    Cslib.Circuits.Monotone.cost_oneHotShiftCircuit_le,
    Cslib.Circuits.Monotone.computesMonotoneShift_dualRailShiftCircuit,
    Cslib.Circuits.Monotone.cost_dualRailShiftCircuit
  ]
  scope := "Over Cslib.Circuits.Monotone.signature weighted by Monotone.binaryCost (charging 1 \
    per binary AND/OR gate and 0 for constants, matching Sergeev's basis {∨, ∧} on nonempty \
    domains and handling q = 0 by zero-output wiring). For any injective antichain code \
    α : Fin n → Fin m → Bool and any monotone circuit cA computing the antichain monomials \
    fun Y r => decide (α r ≤ Y), monotoneShiftCircuit q cA computes S_{q, α} with binaryCost ≤ \
    cA.program.cost binaryCost + 4 * q * n * Nat.clog 2 n (Sergeev notes the boolean sums Y^{i,β} \
    can even be shared in O(n), which is absorbed into O(q n log n) for q ≥ 1). Instantiated on \
    the weight-1 one-hot antichain A₁ (oneHotShiftAntichain n, L(A₁) = 0) with cost ≤ \
    4 * q * n * Nat.clog 2 n, and on dualRailShiftCode n b for any Nat.clog 2 n ≤ b (covering \
    both minimal width b = Nat.clog 2 n in dualRailShiftAntichain n and Sergeev's p. 2 width \
    b = Nat.log 2 n + 1) with exact cost 3 * q * n * Nat.clog 2 n by wiring the dual-rail shift \
    bits directly into the barrel shifter. Theorem 2 (AKS sorting-network permutation upper \
    bounds) is not included."

register_result "sergeev-monotone-shift-lower-bound" where
  title := "Every monotone circuit for the cyclic shift or permutation operator requires \
    q n log₂ n - O(q n) binary gates regardless of the antichain encoding"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2020MonotoneShift,
      theorem := "Theorem 3 and unnumbered Corollary",
      locator := "Lower complexity bounds, pp. 4–6 (arXiv:1905.10747v2)" },
    { paper := Chashkin2006, theorem := unverified, locator := unverified },
    { paper := LamagnaSavage1974, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Monotone.mul_sum_clog_le_cost_of_computesMonotoneShift,
    Cslib.Circuits.Monotone.mul_log_sub_le_cost_of_computesMonotoneShift,
    Cslib.Circuits.Monotone.mul_sum_clog_le_cost_of_computesMonotonePerm,
    Cslib.Circuits.Monotone.mul_log_sub_le_cost_of_computesMonotonePerm
  ]
  scope := "Unconditional over all n, q, m : ℕ, all control codes α : Fin n → Fin m → Bool \
    (resp. β : Equiv.Perm (Fin n) → Fin m → Bool), and all circuits c over \
    Cslib.Circuits.Monotone.signature satisfying ComputesMonotoneShift c α (resp. \
    ComputesMonotonePerm c β): proves the exact finite bound \
    q * ∑_{t=1}^n Nat.clog 2 t ≤ c.program.cost Monotone.binaryCost and the explicit \
    asymptotic-form bound q * n * Nat.log 2 n - q * n ≤ c.program.cost Monotone.binaryCost \
    (constant 1 in the linear term). No separate antichain hypothesis is needed in the lower \
    bound statement because q = 0 and n ≤ 1 give 0 on the left-hand side while for q ≥ 1, \
    ComputesMonotoneShift.injective_and_isAntichain proves α must injectively index an antichain. \
    Chashkin2006 and LamagnaSavage1974 are cited as secondary historical attributions through \
    Sergeev pp. 1, 4–5 and were not inspected directly."
