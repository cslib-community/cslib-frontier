/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Monotone.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.Interval.Finset.Nat
import CslibFrontier.Computability.Circuit.Parallel
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simps
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Tactic.Ring

/-!
# Monotone circuit complexity of cyclic shift and permutation operators

Following Sergeev [Sergeev2020MonotoneShift], an `(n q + m, n q)`-input operator on `n` Boolean
vectors `X = (x_0, …, x_{n-1})` of length `q` (packed via `finProdFinEquiv : Fin n × Fin q ≃
Fin (n * q)`) and an `m`-bit control vector `Y : Fin m → Bool` (appended via `Fin.append X Y`)
implements:

* the **monotone cyclic shift operator** `S_{q, A}` (`ComputesMonotoneShift c α`) when for every
  `X` and `k : Fin n`, evaluating `c` at `(X, α k)` yields the right cyclic shift
  `cyclicShiftVec X k` placing input block `x_i` at output block `(i + k) mod n`;
* the **monotone permutation operator** `P_{q, Π}` (`ComputesMonotonePerm c β`) when for every
  `X` and `π : Equiv.Perm (Fin n)`, evaluating `c` at `(X, β π)` yields `permuteVec X π`, whose
  output block `j` is `x_{π(j)}`.

Whenever `0 < q`, monotonicity of `Monotone.interpretation` forces any code `α` (or `β`) computed
by a monotone circuit to have pairwise incomparable codewords (`ComputesMonotoneShift.not_le`,
`ComputesMonotonePerm.not_le`), hence an injective indexing of an antichain in `Fin m → Bool`
(`ComputesMonotoneShift.injective_and_isAntichain`,
`ComputesMonotonePerm.injective_and_isAntichain`).

On the upper-bound side (**Theorem 1**, [Sergeev2020MonotoneShift], pp. 3–4), from any monotone
circuit `cA` computing the antichain monomials `fun Y r => decide (α r ≤ Y)` (which evaluate at
`α k` to the one-hot indicator `decide (r = k)`), `monotoneShiftCircuit q cA` ORs the indicator
wires into `2 ⌈log₂ n⌉` bit-value tests and feeds an explicit `⌈log₂ n⌉`-stage monotone barrel
shifter built from 3-gate monotone multiplexers `(y₁ ∧ a) ∨ (y₀ ∧ b)`, achieving
`binaryCost ≤ cA.program.cost binaryCost + 4 * q * n * Nat.clog 2 n`. On the weight-`1` one-hot
antichain `oneHotShiftAntichain` (`L(A₁) = 0`), `oneHotShiftCircuit` uses at most
`4 * q * n * Nat.clog 2 n` gates; on the dual-rail binary code `dualRailShiftCode n b` (`b ≥
Nat.clog 2 n`, covering both minimal width `dualRailShiftAntichain n` and Sergeev's
`b = Nat.log 2 n + 1`), `dualRailShiftCircuit` reads the bit rails directly with zero indicator
gates and exact cost `3 * q * n * Nat.clog 2 n`. Sergeev's Theorem 2 (sorting-network upper
bounds for `P_{q, Π}` via AKS) is not included in this module.

On the lower-bound side (**Theorem 3** and **Corollary**, [Sergeev2020MonotoneShift], pp. 4–6,
adapting Chashkin [Chashkin2006] and Lamagna–Savage [LamagnaSavage1974]), monotone projection
isolation (`eq_proj_or_eq_proj_of_or`, `eq_proj_or_eq_proj_of_and`) traces for each shift `k` and
input coordinate `(i, b)` a chain of `{∧, ∨}` gates computing `X(i, b)` from `(i, b)` to output
`((i + k) mod n, b)`. For fixed `k` these gate sets are pairwise disjoint across all `n q`
coordinates, while for fixed output `(j, b)` at most `2^d` inputs reach the output wire within `d`
gates, forcing the path lengths to sum to at least `∑_{t=1}^n ⌈log₂ t⌉ ≥ n ⌊log₂ n⌋ - n`. Thus
every monotone circuit computing `S_{q, α}` — and, by restriction along `cyclicShiftPerm`, every
monotone circuit computing `P_{q, β}` — has `binaryCost` at least
`q * ∑_{t=1}^n Nat.clog 2 t ≥ q * n * Nat.log 2 n - q * n`, independently of the choice of
antichain `α` or `β` and control width `m`.

## Main definitions

* `Cslib.Circuits.Monotone.permuteVec`, `Cslib.Circuits.Monotone.cyclicShiftPerm`,
  `Cslib.Circuits.Monotone.cyclicShiftVec`: block permutation and right cyclic shift on `n`
  vectors of width `q`.
* `Cslib.Circuits.Monotone.ComputesMonotoneShift`,
  `Cslib.Circuits.Monotone.ComputesMonotonePerm`: monotone circuit computation of `S_{q, A}` and
  `P_{q, Π}`.
* `Cslib.Circuits.Monotone.oneHotShiftAntichain`, `Cslib.Circuits.Monotone.dualRailShiftCode`,
  `Cslib.Circuits.Monotone.dualRailShiftAntichain`: the weight-`1` (`A₁`) and dual-rail binary
  (`A₀`) shift antichains.
* `Cslib.Circuits.Monotone.monotoneShiftCircuit`, `Cslib.Circuits.Monotone.oneHotShiftCircuit`,
  `Cslib.Circuits.Monotone.dualRailShiftCircuit`: explicit monotone barrel-shifter circuits for
  general antichains, `A₁`, and `A₀`.

## Main results

* `Cslib.Circuits.Monotone.ComputesMonotoneShift.injective_and_isAntichain`,
  `Cslib.Circuits.Monotone.ComputesMonotonePerm.injective_and_isAntichain`: when `0 < q`, any
  monotone-computable shift or permutation code injectively indexes an antichain.
* `Cslib.Circuits.Monotone.computesMonotoneShift_monotoneShiftCircuit`,
  `Cslib.Circuits.Monotone.cost_monotoneShiftCircuit_le`: Theorem 1 (`L(S_{q, A}) ≤ L(A) +
  4 q n ⌈log₂ n⌉`).
* `Cslib.Circuits.Monotone.computesMonotoneShift_oneHotShiftCircuit`,
  `Cslib.Circuits.Monotone.cost_oneHotShiftCircuit_le`,
  `Cslib.Circuits.Monotone.computesMonotoneShift_dualRailShiftCircuit`,
  `Cslib.Circuits.Monotone.cost_dualRailShiftCircuit`: `O(q n log n)` instantiations on `A₁` and
  `A₀`.
* `Cslib.Circuits.Monotone.eq_proj_or_eq_proj_of_or`,
  `Cslib.Circuits.Monotone.eq_proj_or_eq_proj_of_and`: monotone projection isolation at OR and AND
  gates.
* `Cslib.Circuits.Monotone.mul_sum_clog_le_cost_of_computesMonotoneShift`,
  `Cslib.Circuits.Monotone.mul_log_sub_le_cost_of_computesMonotoneShift`: Theorem 3 (`L(S_{q, A}) ≥
  q ∑_{t=1}^n ⌈log₂ t⌉ ≥ q n ⌊log₂ n⌋ - q n` for every antichain `A`).
* `Cslib.Circuits.Monotone.mul_sum_clog_le_cost_of_computesMonotonePerm`,
  `Cslib.Circuits.Monotone.mul_log_sub_le_cost_of_computesMonotonePerm`: Corollary (`L(P_{q, Π}) ≥
  q ∑_{t=1}^n ⌈log₂ t⌉ ≥ q n ⌊log₂ n⌋ - q n` for every permutation antichain `Π`).

## References

* [I. S. Sergeev, *On the Monotone Complexity of the Shift Operator*][Sergeev2020MonotoneShift]
* [A. V. Chashkin, *On the Complexity of a Cyclic Shift of a Set of Real Numbers*][Chashkin2006]
* [E. A. Lamagna and J. E. Savage, *Combinational Complexity of Some Monotone
  Functions*][LamagnaSavage1974]
-/

public section

namespace Cslib.Circuits.Monotone

open Finset

/-! ### Block permutations, cyclic shifts, and monotone operator specifications -/

/-- Permute the `n` length-`q` blocks of `X` according to `π`: output block `j` receives input
block `π j` (`π(X) = (x_{π(0)}, …, x_{π(n-1)})`, [Sergeev2020MonotoneShift], p. 3). -/
@[expose] def permuteVec {n q : ℕ} (X : Fin (n * q) → Bool) (π : Equiv.Perm (Fin n)) :
    Fin (n * q) → Bool :=
  fun idx =>
    let (j, b) := finProdFinEquiv.symm idx
    X (finProdFinEquiv (π j, b))

/-- At coordinate `(j, b)`, `permuteVec X π` reads coordinate `(π j, b)` of `X`. -/
@[simp] theorem permuteVec_finProdFinEquiv {n q : ℕ} (X : Fin (n * q) → Bool)
    (π : Equiv.Perm (Fin n)) (j : Fin n) (b : Fin q) :
    permuteVec X π (finProdFinEquiv (j, b)) = X (finProdFinEquiv (π j, b)) := by
  simp [permuteVec]

/-- The permutation of `Fin n` corresponding to a cyclic right shift by `k` positions: output
position `j` reads input position `(j - k) mod n`, while input position `i` moves to output
position `(i + k) mod n`. -/
@[expose] def cyclicShiftPerm {n : ℕ} (k : Fin n) : Equiv.Perm (Fin n) :=
  letI : NeZero n := ⟨k.pos.ne'⟩
  { toFun := fun j => j - k
    invFun := fun i => i + k
    left_inv := fun j => sub_add_cancel j k
    right_inv := fun i => add_sub_cancel_right i k }

/-- Cyclic right shift `X ≫ k` of `n` length-`q` Boolean vectors by `k` positions
([Sergeev2020MonotoneShift], p. 2): output block `(i + k) mod n` equals input block `i`. -/
@[expose] def cyclicShiftVec {n q : ℕ} (X : Fin (n * q) → Bool) (k : Fin n) :
    Fin (n * q) → Bool :=
  permuteVec X (cyclicShiftPerm k)

/-- Output block `(i + k) mod n` of `cyclicShiftVec X k` carries input block `i`. -/
@[simp] theorem cyclicShiftVec_symm_finProdFinEquiv {n q : ℕ} (X : Fin (n * q) → Bool)
    (k i : Fin n) (b : Fin q) :
    cyclicShiftVec X k (finProdFinEquiv ((cyclicShiftPerm k).symm i, b)) =
      X (finProdFinEquiv (i, b)) := by
  simp [cyclicShiftVec]

/-- Distinct shift amounts `k₁ ≠ k₂` induce distinct permutations of `Fin n`. -/
theorem cyclicShiftPerm_injective {n : ℕ} : Function.Injective (cyclicShiftPerm (n := n)) := by
  intro k₁ k₂ h
  let : NeZero n := ⟨k₁.pos.ne'⟩
  have h0 : (cyclicShiftPerm k₁).symm 0 = (cyclicShiftPerm k₂).symm 0 :=
    congrArg (fun e => e.symm 0) h
  change (0 : Fin n) + k₁ = (0 : Fin n) + k₂ at h0
  simpa using h0

/-- A monotone circuit `c` computes the monotone cyclic shift operator `S_{q, A}` for control
code `α : Fin n → Fin m → Bool` when `c` evaluates `(X, α k)` to `cyclicShiftVec X k` for all
data vectors `X` and shift indices `k` ([Sergeev2020MonotoneShift], p. 2). -/
@[expose] def ComputesMonotoneShift {n q m : ℕ}
    (c : Circuit signature (n * q + m) (n * q)) (α : Fin n → Fin m → Bool) : Prop :=
  ∀ (X : Fin (n * q) → Bool) (k : Fin n),
    c.eval interpretation (Fin.append X (α k)) = cyclicShiftVec X k

/-- A monotone circuit `c` computes the monotone permutation operator `P_{q, Π}` for control code
`β : Equiv.Perm (Fin n) → Fin m → Bool` when `c` evaluates `(X, β π)` to `permuteVec X π` for all
data vectors `X` and permutations `π` ([Sergeev2020MonotoneShift], p. 3). -/
@[expose] def ComputesMonotonePerm {n q m : ℕ}
    (c : Circuit signature (n * q + m) (n * q))
    (β : Equiv.Perm (Fin n) → Fin m → Bool) : Prop :=
  ∀ (X : Fin (n * q) → Bool) (π : Equiv.Perm (Fin n)),
    c.eval interpretation (Fin.append X (β π)) = permuteVec X π

/-- Restricting a monotone permutation circuit along `cyclicShiftPerm` yields a monotone cyclic
shift circuit for `fun k => β (cyclicShiftPerm k)` ([Sergeev2020MonotoneShift], p. 3). -/
theorem ComputesMonotonePerm.computesMonotoneShift {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {β : Equiv.Perm (Fin n) → Fin m → Bool}
    (hc : ComputesMonotonePerm c β) :
    ComputesMonotoneShift c (fun k => β (cyclicShiftPerm k)) :=
  fun X k => hc X (cyclicShiftPerm k)

/-! ### Monotonicity of circuit evaluation and antichain necessity -/

private theorem trace_mono {N G : ℕ} (p : Program signature N G)
    {x y : Fin N → Bool} (hxy : x ≤ y) (w : Wire N G) :
    p.trace interpretation x w ≤ p.trace interpretation y w :=
  p.trace_rel (· ≤ ·) hxy (fun _ _ _ h => interpretation_mono _ h) w

private theorem eval_mono {N M : ℕ} (c : Circuit signature N M) :
    Monotone (c.eval interpretation) :=
  fun _ _ hxy o => trace_mono c.program hxy (c.outputs o)

private theorem not_true_le_false : ¬ (true ≤ false) := by decide

private theorem not_le_of_eval_permuteVec {ι : Type*} {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {γ : ι → Fin m → Bool}
    {φ : ι → Equiv.Perm (Fin n)}
    (hc : ∀ X r, c.eval interpretation (Fin.append X (γ r)) = permuteVec X (φ r))
    (hq : 0 < q) {r₁ r₂ : ι} (hne : φ r₁ ≠ φ r₂) : ¬ γ r₁ ≤ γ r₂ := by
  intro hle
  obtain ⟨j, hj⟩ : ∃ j, φ r₁ j ≠ φ r₂ j := by
    by_contra! h
    exact hne (Equiv.ext h)
  let u₁ : Fin (n * q) := finProdFinEquiv (φ r₁ j, ⟨0, hq⟩)
  let X : Fin (n * q) → Bool := fun u => decide (u = u₁)
  have happ : Fin.append X (γ r₁) ≤ Fin.append X (γ r₂) :=
    Fin.addCases (fun _ => by simp) (fun t => by simpa using hle t)
  have hmono := eval_mono c happ (finProdFinEquiv (j, ⟨0, hq⟩))
  rw [hc X r₁, hc X r₂] at hmono
  simp only [permuteVec_finProdFinEquiv, X, u₁, decide_true] at hmono
  exact hj (Prod.mk.inj (finProdFinEquiv.injective
    (of_decide_eq_true (Bool.eq_true_of_true_le hmono)).symm)).1

private theorem injective_and_isAntichain_of_not_le {ι : Type*} {m : ℕ} {γ : ι → Fin m → Bool}
    (hnot : ∀ {r₁ r₂ : ι}, r₁ ≠ r₂ → ¬ γ r₁ ≤ γ r₂) :
    Function.Injective γ ∧ IsAntichain (· ≤ ·) (Set.range γ) := by
  refine ⟨fun r₁ r₂ heq => by_contra fun hne => hnot hne (le_of_eq heq), ?_⟩
  rintro _ ⟨r₁, rfl⟩ _ ⟨r₂, rfl⟩ hne
  exact hnot (fun h => hne (congrArg γ h))

/-- When `0 < q`, any monotone circuit computing `P_{q, Π}` forces distinct permutations to have
incomparable control codewords (`¬ β π₁ ≤ β π₂`). -/
theorem ComputesMonotonePerm.not_le {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {β : Equiv.Perm (Fin n) → Fin m → Bool}
    (hc : ComputesMonotonePerm c β) (hq : 0 < q)
    {π₁ π₂ : Equiv.Perm (Fin n)} (hne : π₁ ≠ π₂) : ¬ β π₁ ≤ β π₂ :=
  not_le_of_eval_permuteVec hc hq hne

/-- When `0 < q`, any code `β` computed by a monotone permutation circuit is injective and its
range is an antichain under the pointwise order on `Fin m → Bool`. -/
theorem ComputesMonotonePerm.injective_and_isAntichain {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {β : Equiv.Perm (Fin n) → Fin m → Bool}
    (hc : ComputesMonotonePerm c β) (hq : 0 < q) :
    Function.Injective β ∧ IsAntichain (· ≤ ·) (Set.range β) :=
  injective_and_isAntichain_of_not_le (hc.not_le hq)

/-- When `0 < q`, any monotone circuit computing `S_{q, α}` forces distinct shift amounts to have
incomparable control codewords (`¬ α k₁ ≤ α k₂`). -/
theorem ComputesMonotoneShift.not_le {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {α : Fin n → Fin m → Bool}
    (hc : ComputesMonotoneShift c α) (hq : 0 < q)
    {k₁ k₂ : Fin n} (hne : k₁ ≠ k₂) : ¬ α k₁ ≤ α k₂ :=
  not_le_of_eval_permuteVec hc hq (cyclicShiftPerm_injective.ne hne)

/-- When `0 < q`, any shift code `α` computed by a monotone shift circuit is injective and its
range is an antichain under the pointwise order on `Fin m → Bool`. -/
theorem ComputesMonotoneShift.injective_and_isAntichain {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {α : Fin n → Fin m → Bool}
    (hc : ComputesMonotoneShift c α) (hq : 0 < q) :
    Function.Injective α ∧ IsAntichain (· ≤ ·) (Set.range α) :=
  injective_and_isAntichain_of_not_le (hc.not_le hq)

/-! ### Standard shift antichains: one-hot (`A₁`) and dual-rail binary (`A₀`) -/

/-- The weight-`1` one-hot shift antichain `A₁ ⊂ B^n` ([Sergeev2020MonotoneShift], p. 2), sending
`k : Fin n` to the indicator vector `fun i => decide (i = k)`. -/
@[expose] def oneHotShiftAntichain (n : ℕ) : Fin n → Fin n → Bool :=
  fun k i => decide (i = k)

private theorem eq_of_oneHotShiftAntichain_le {n : ℕ} {k₁ k₂ : Fin n}
    (h : oneHotShiftAntichain n k₁ ≤ oneHotShiftAntichain n k₂) : k₁ = k₂ := by
  have hk := h k₁
  simp only [oneHotShiftAntichain, decide_true] at hk
  exact of_decide_eq_true (Bool.eq_true_of_true_le hk)

/-- `oneHotShiftAntichain n` is injective. -/
theorem injective_oneHotShiftAntichain (n : ℕ) :
    Function.Injective (oneHotShiftAntichain n) :=
  fun _ _ heq => eq_of_oneHotShiftAntichain_le (le_of_eq heq)

/-- The range of `oneHotShiftAntichain n` is an antichain in `Fin n → Bool`. -/
theorem isAntichain_range_oneHotShiftAntichain (n : ℕ) :
    IsAntichain (· ≤ ·) (Set.range (oneHotShiftAntichain n)) :=
  (injective_and_isAntichain_of_not_le (γ := oneHotShiftAntichain n)
    fun hne hle => hne (eq_of_oneHotShiftAntichain_le hle)).2

/-- Dual-rail binary shift code of bit-width `b` ([Sergeev2020MonotoneShift], p. 2, `A₀`),
doubling the `b`-bit binary representation `[k]_2` in the first `b` coordinates with its bitwise
negation `\overline{[k]_2}` in the last `b` coordinates. -/
@[expose] def dualRailShiftCode (n b : ℕ) : Fin n → Fin (2 * b) → Bool :=
  fun k t =>
    if t.val < b then k.val.testBit t.val else !k.val.testBit (t.val - b)

/-- Minimal-width (`2 * Nat.clog 2 n`) dual-rail binary shift antichain; Sergeev's `p. 2` width
`2 * (⌊log₂ n⌋ + 1)` is `dualRailShiftCode n (Nat.log 2 n + 1)`. -/
abbrev dualRailShiftAntichain (n : ℕ) : Fin n → Fin (2 * Nat.clog 2 n) → Bool :=
  dualRailShiftCode n (Nat.clog 2 n)

private theorem eq_of_dualRailShiftCode_le {n b : ℕ} (hb : n ≤ 2 ^ b) {k₁ k₂ : Fin n}
    (h : dualRailShiftCode n b k₁ ≤ dualRailShiftCode n b k₂) : k₁ = k₂ := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · have hpos := h ⟨i, by omega⟩
    have hneg := h ⟨b + i, by omega⟩
    simp only [dualRailShiftCode, hi, ↓reduceIte, show ¬ (b + i < b) by omega,
      Nat.add_sub_cancel_left] at hpos hneg
    cases hb₁ : k₁.val.testBit i <;> cases hb₂ : k₂.val.testBit i
    · rfl
    · rw [hb₁, hb₂] at hneg; exact False.elim (not_true_le_false hneg)
    · rw [hb₁, hb₂] at hpos; exact False.elim (not_true_le_false hpos)
    · rfl
  · have hlt₁ : k₁.val < 2 ^ i :=
      k₁.isLt.trans_le (hb.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    have hlt₂ : k₂.val < 2 ^ i :=
      k₂.isLt.trans_le (hb.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [Nat.testBit_lt_two_pow hlt₁, Nat.testBit_lt_two_pow hlt₂]

/-- Whenever `n ≤ 2 ^ b` (in particular for `b = Nat.clog 2 n` and `b = Nat.log 2 n + 1`),
`dualRailShiftCode n b` is injective. -/
theorem injective_dualRailShiftCode {n b : ℕ} (hb : n ≤ 2 ^ b) :
    Function.Injective (dualRailShiftCode n b) :=
  fun _ _ heq => eq_of_dualRailShiftCode_le hb (le_of_eq heq)

/-- Whenever `n ≤ 2 ^ b`, the range of `dualRailShiftCode n b` is an antichain in
`Fin (2 * b) → Bool`. -/
theorem isAntichain_range_dualRailShiftCode {n b : ℕ} (hb : n ≤ 2 ^ b) :
    IsAntichain (· ≤ ·) (Set.range (dualRailShiftCode n b)) :=
  (injective_and_isAntichain_of_not_le (γ := dualRailShiftCode n b)
    fun hne hle => hne (eq_of_dualRailShiftCode_le hb hle)).2

/-! ### Theorem 1: Monotone barrel-shifter upper bounds -/

/-- Natural-number cyclic right shift of `n` length-`q` blocks by `s` positions, used as the
intermediate stage invariant of the barrel shifter. -/
private def shiftByNat {n q : ℕ} (X : Fin (n * q) → Bool) (s : ℕ) : Fin (n * q) → Bool :=
  fun idx =>
    let (j, b) := finProdFinEquiv.symm idx
    letI : NeZero n := ⟨j.pos.ne'⟩
    X (finProdFinEquiv (j - Fin.ofNat n s, b))

private theorem shiftByNat_zero {n q : ℕ} (X : Fin (n * q) → Bool) :
    shiftByNat X 0 = X := by
  funext idx
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective idx
  let : NeZero n := ⟨j.pos.ne'⟩
  simp only [shiftByNat, Equiv.symm_apply_apply]
  have h0 : Fin.ofNat n 0 = (0 : Fin n) := rfl
  rw [h0, sub_zero]

private theorem shiftByNat_add {n q : ℕ} (X : Fin (n * q) → Bool) (s₁ s₂ : ℕ) :
    shiftByNat (shiftByNat X s₁) s₂ = shiftByNat X (s₁ + s₂) := by
  funext idx
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective idx
  let : NeZero n := ⟨j.pos.ne'⟩
  have hofNat : Fin.ofNat n (s₁ + s₂) = Fin.ofNat n s₁ + Fin.ofNat n s₂ := by
    ext
    simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
  simp only [shiftByNat, Equiv.symm_apply_apply]
  rw [hofNat, sub_sub, add_comm]

private theorem shiftByNat_coe {n q : ℕ} (X : Fin (n * q) → Bool) (k : Fin n) :
    shiftByNat X k.val = cyclicShiftVec X k := by
  funext idx
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective idx
  let : NeZero n := ⟨k.pos.ne'⟩
  have hk : Fin.ofNat n k.val = k := by
    ext
    exact Nat.mod_eq_of_lt k.isLt
  simp only [shiftByNat, Equiv.symm_apply_apply, cyclicShiftVec, permuteVec_finProdFinEquiv, hk]
  rfl

/-- Three-gate monotone multiplexer `(v 0 && v 1) || (v 2 && v 3)` implementing Sergeev's
`Y^{i,1} a ∨ Y^{i,0} b` ([Sergeev2020MonotoneShift], pp. 3–4). -/
private def monotoneMux : Circuit signature 4 1 :=
  (Circuit.oneGate (σ := signature) Op.or ![0, 1]).comp
    ((Circuit.oneGate (σ := signature) Op.and ![0, 1]).append
      (Circuit.oneGate (σ := signature) Op.and ![2, 3]))

private theorem eval_monotoneMux (v : Fin 4 → Bool) :
    monotoneMux.eval interpretation v 0 = ((v 0 && v 1) || (v 2 && v 3)) := by
  simp only [monotoneMux, Circuit.eval_comp, Circuit.eval_oneGate, interpretation_or,
    Circuit.eval_append, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : Fin.append ((Circuit.oneGate (σ := signature) Op.and ![0, 1]).eval interpretation v)
      ((Circuit.oneGate (σ := signature) Op.and ![2, 3]).eval interpretation v) (0 : Fin 2) =
      (v 0 && v 1) := Fin.append_left _ _ (0 : Fin 1)
  have h1 : Fin.append ((Circuit.oneGate (σ := signature) Op.and ![0, 1]).eval interpretation v)
      ((Circuit.oneGate (σ := signature) Op.and ![2, 3]).eval interpretation v) (1 : Fin 2) =
      (v 2 && v 3) := Fin.append_right _ _ (0 : Fin 1)
  rw [h0, h1]

private theorem cost_monotoneMux : monotoneMux.program.cost binaryCost = 3 := by
  simp only [circuit_simps, monotoneMux, binaryCost_or, binaryCost_and]

private def barrelMuxSelect (n q L i : ℕ) (hi : i < L) (u : Fin (n * q)) :
    Fin 4 → Fin (n * q + 2 * L) :=
  let (j, b) := finProdFinEquiv.symm u
  let jShift : Fin n := ⟨(j.val + n - (2 ^ i) % n) % n, Nat.mod_lt _ j.pos⟩
  let uShift : Fin (n * q) := finProdFinEquiv (jShift, b)
  ![Fin.natAdd (n * q) ⟨i, by omega⟩,
    Fin.castAdd (2 * L) uShift,
    Fin.natAdd (n * q) ⟨L + i, by omega⟩,
    Fin.castAdd (2 * L) u]

private def barrelStage (n q L i : ℕ) (hi : i < L) :
    Circuit signature (n * q + 2 * L) (n * q + 2 * L) :=
  (Circuit.pi fun u : Fin (n * q) =>
      monotoneMux.comp (Circuit.wiring signature (barrelMuxSelect n q L i hi u))).append
    (Circuit.wiring signature (Fin.natAdd (n * q)))

private theorem cost_barrelStage (n q L i : ℕ) (hi : i < L) :
    (barrelStage n q L i hi).program.cost binaryCost = 3 * q * n := by
  simp only [circuit_simps, barrelStage, cost_monotoneMux, Nat.zero_add, Nat.add_zero]
  ac_rfl

private theorem jShift_eq_sub_ofNat {n i : ℕ} (j : Fin n) :
    letI : NeZero n := ⟨j.pos.ne'⟩
    (⟨(j.val + n - (2 ^ i) % n) % n, Nat.mod_lt _ j.pos⟩ : Fin n) = j - Fin.ofNat n (2 ^ i) := by
  let : NeZero n := ⟨j.pos.ne'⟩
  ext
  simp only [Fin.sub_def, Fin.ofNat]
  have hlt : 2 ^ i % n < n := Nat.mod_lt _ j.pos
  congr 1
  omega

private theorem eval_barrelStage (n q L i : ℕ) (hi : i < L)
    (X : Fin (n * q) → Bool) (R : Fin (2 * L) → Bool) (bit : Bool)
    (hpos : R ⟨i, by omega⟩ = bit) (hneg : R ⟨L + i, by omega⟩ = !bit) :
    (barrelStage n q L i hi).eval interpretation (Fin.append X R) =
      Fin.append (shiftByNat X (if bit then 2 ^ i else 0)) R := by
  funext idx
  refine Fin.addCases (fun u => ?_) (fun t => ?_) idx
  · simp only [barrelStage, Circuit.eval_append, Fin.append_left, Circuit.eval_pi,
      Circuit.eval_comp, Circuit.eval_wiring, eval_monotoneMux]
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective u
    simp only [barrelMuxSelect, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Equiv.symm_apply_apply, Fin.append_right, Fin.append_left, hpos, hneg]
    rw [jShift_eq_sub_ofNat]
    cases bit
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.false_and, Bool.true_and,
        Bool.false_or]
      rw [shiftByNat_zero]
    · simp [shiftByNat]
  · simp [barrelStage]

private def barrelStages (n q L : ℕ) :
    (t : ℕ) → t ≤ L → Circuit signature (n * q + 2 * L) (n * q + 2 * L)
  | 0, _ => Circuit.id signature (n * q + 2 * L)
  | t + 1, ht =>
    (barrelStage n q L t (Nat.lt_of_succ_le ht)).comp
      (barrelStages n q L t (Nat.le_of_succ_le ht))

private theorem cost_barrelStages (n q L : ℕ) :
    ∀ (t : ℕ) (ht : t ≤ L),
      (barrelStages n q L t ht).program.cost binaryCost = 3 * q * n * t
  | 0, _ => by simp only [circuit_simps, barrelStages, Circuit.id, Nat.mul_zero]
  | t + 1, ht => by
    rw [barrelStages, Circuit.cost_program_comp, cost_barrelStages n q L t (Nat.le_of_succ_le ht),
      cost_barrelStage, Nat.mul_succ]

private theorem eval_barrelStages (n q L s : ℕ)
    (X : Fin (n * q) → Bool) (R : Fin (2 * L) → Bool)
    (hpos : ∀ i (hi : i < L), R ⟨i, by omega⟩ = s.testBit i)
    (hneg : ∀ i (hi : i < L), R ⟨L + i, by omega⟩ = !s.testBit i) :
    ∀ (t : ℕ) (ht : t ≤ L),
      (barrelStages n q L t ht).eval interpretation (Fin.append X R) =
        Fin.append (shiftByNat X (s % 2 ^ t)) R
  | 0, _ => by
    simp [barrelStages, Nat.mod_one, shiftByNat_zero]
  | t + 1, ht => by
    have hlt : t < L := Nat.lt_of_succ_le ht
    rw [barrelStages, Circuit.eval_comp, eval_barrelStages n q L s X R hpos hneg t hlt.le,
      eval_barrelStage n q L t hlt _ R (s.testBit t) (hpos t hlt) (hneg t hlt),
      shiftByNat_add]
    have hmod : s % 2 ^ (t + 1) = s % 2 ^ t + if s.testBit t then 2 ^ t else 0 := by
      rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ t) with h | h <;> simp [h]
    rw [hmod]

private def barrelShiftCircuit (n q L : ℕ) :
    Circuit signature (n * q + 2 * L) (n * q) :=
  (Circuit.wiring signature (Fin.castAdd (2 * L))).comp (barrelStages n q L L le_rfl)

private theorem cost_barrelShiftCircuit (n q L : ℕ) :
    (barrelShiftCircuit n q L).program.cost binaryCost = 3 * q * n * L := by
  rw [barrelShiftCircuit, Circuit.cost_program_comp, cost_barrelStages,
    Circuit.cost_program_wiring, Nat.add_zero]

private theorem eval_barrelShiftCircuit (n q : ℕ) (X : Fin (n * q) → Bool) (k : Fin n)
    (R : Fin (2 * Nat.clog 2 n) → Bool)
    (hpos : ∀ i (hi : i < Nat.clog 2 n), R ⟨i, by omega⟩ = k.val.testBit i)
    (hneg : ∀ i (hi : i < Nat.clog 2 n),
      R ⟨Nat.clog 2 n + i, by omega⟩ = !k.val.testBit i) :
    (barrelShiftCircuit n q (Nat.clog 2 n)).eval interpretation (Fin.append X R) =
      cyclicShiftVec X k := by
  rw [barrelShiftCircuit, Circuit.eval_comp,
    eval_barrelStages n q (Nat.clog 2 n) k.val X R hpos hneg (Nat.clog 2 n) le_rfl,
    Circuit.eval_wiring, Fin.append_comp_castAdd]
  have hk_lt : k.val < 2 ^ Nat.clog 2 n := k.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two n)
  rw [Nat.mod_eq_of_lt hk_lt, shiftByNat_coe]

private def orInputList (n : ℕ) : List (Fin n) → Circuit signature n 1
  | [] => Circuit.oneGate (σ := signature) (Op.const false) Fin.elim0
  | [r] => Circuit.wiring signature fun _ : Fin 1 => r
  | r :: r' :: rs =>
    (Circuit.oneGate (σ := signature) Op.or ![0, 1]).comp
      ((Circuit.wiring signature fun _ : Fin 1 => r).append (orInputList n (r' :: rs)))

private theorem eval_orInputList (n : ℕ) :
    ∀ (idxs : List (Fin n)) (z : Fin n → Bool),
      (orInputList n idxs).eval interpretation z 0 = idxs.any z
  | [], _ => by simp [orInputList]
  | [r], z => by simp [orInputList]
  | r :: r' :: rs, z => by
    simp only [orInputList, Circuit.eval_comp, Circuit.eval_oneGate, interpretation_or,
      Circuit.eval_append, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : Fin.append ((Circuit.wiring signature fun _ : Fin 1 => r).eval interpretation z)
        ((orInputList n (r' :: rs)).eval interpretation z) (0 : Fin 2) = z r :=
      Fin.append_left _ _ (0 : Fin 1)
    have h1 : Fin.append ((Circuit.wiring signature fun _ : Fin 1 => r).eval interpretation z)
        ((orInputList n (r' :: rs)).eval interpretation z) (1 : Fin 2) =
        (orInputList n (r' :: rs)).eval interpretation z 0 :=
      Fin.append_right _ _ (0 : Fin 1)
    rw [h0, h1, eval_orInputList n (r' :: rs) z]
    rfl

private theorem cost_orInputList_le (n : ℕ) :
    ∀ idxs : List (Fin n), (orInputList n idxs).program.cost binaryCost ≤ idxs.length
  | [] => by simp [circuit_simps, orInputList]
  | [r] => by simp [circuit_simps, orInputList]
  | r :: r' :: rs => by
    rw [orInputList, Circuit.cost_program_comp, Circuit.cost_program_append,
      Circuit.cost_program_wiring, Circuit.cost_program_oneGate, binaryCost_or, Nat.zero_add]
    have ih := cost_orInputList_le n (r' :: rs)
    simp only [List.length_cons] at ih ⊢
    omega

private def railBitsOfOneHot (n L : ℕ) : Circuit signature n (2 * L) :=
  Circuit.pi fun t : Fin (2 * L) =>
    if t.val < L then
      orInputList n ((List.finRange n).filter fun r => r.val.testBit t.val)
    else
      orInputList n ((List.finRange n).filter fun r => !r.val.testBit (t.val - L))

private theorem eval_railBitsOfOneHot_oneHot (n L : ℕ) (k : Fin n) (t : Fin (2 * L)) :
    (railBitsOfOneHot n L).eval interpretation (fun r => decide (r = k)) t =
      if t.val < L then k.val.testBit t.val else !k.val.testBit (t.val - L) := by
  have hany : ∀ P : Fin n → Bool,
      ((List.finRange n).filter P).any (fun r => decide (r = k)) = P k := by
    intro P
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨fun ⟨_, hP, heq⟩ => heq ▸ hP, fun hPk => ⟨k, hPk, rfl⟩⟩
  simp only [railBitsOfOneHot, Circuit.eval_pi]
  split_ifs with ht <;> rw [eval_orInputList, hany]

private theorem cost_railBitsOfOneHot_le (n L : ℕ) :
    (railBitsOfOneHot n L).program.cost binaryCost ≤ n * L := by
  rw [railBitsOfOneHot, Circuit.cost_program_pi]
  let e : Fin L ⊕ Fin L ≃ Fin (2 * L) :=
    (finSumFinEquiv.trans (finCongr (Nat.two_mul L).symm))
  rw [← e.sum_comp, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  calc ∑ i : Fin L,
        ((if (e (.inl i)).val < L then
            orInputList n ((List.finRange n).filter fun r => r.val.testBit (e (.inl i)).val)
          else
            orInputList n ((List.finRange n).filter fun r =>
              !r.val.testBit ((e (.inl i)).val - L))).program.cost binaryCost +
         (if (e (.inr i)).val < L then
            orInputList n ((List.finRange n).filter fun r => r.val.testBit (e (.inr i)).val)
          else
            orInputList n ((List.finRange n).filter fun r =>
              !r.val.testBit ((e (.inr i)).val - L))).program.cost binaryCost)
      ≤ ∑ _i : Fin L, n := by
        refine sum_le_sum fun i _ => ?_
        have hinl : (e (.inl i)).val = i.val := rfl
        have hinr : (e (.inr i)).val = L + i.val := rfl
        rw [hinl, ite_eq_left i.isLt, hinr, ite_eq_right (by omega : ¬ L + i.val < L),
          Nat.add_sub_cancel_left]
        calc (orInputList n ((List.finRange n).filter fun r => r.val.testBit i.val)).program.cost
              binaryCost +
            (orInputList n ((List.finRange n).filter fun r => !r.val.testBit i.val)).program.cost
              binaryCost
            ≤ ((List.finRange n).filter fun r => r.val.testBit i.val).length +
              ((List.finRange n).filter fun r => !r.val.testBit i.val).length :=
              Nat.add_le_add (cost_orInputList_le _ _) (cost_orInputList_le _ _)
          _ = (List.finRange n).length := (List.length_eq_length_filter_add _).symm
          _ = n := List.length_finRange
    _ = n * L := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- **Theorem 1 circuit construction** ([Sergeev2020MonotoneShift], pp. 3–4): from any monotone
circuit `cA : Circuit signature m n` computing the one-hot/monomial indicators of an `n`-element
shift antichain, build a monotone circuit for `S_{q, A}` by ORing the indicators into `2 ⌈log₂ n⌉`
rail bits and applying the `⌈log₂ n⌉`-stage monotone barrel shifter (and pure zero-output wiring
when `q = 0`). -/
def monotoneShiftCircuit {n m : ℕ} (q : ℕ) (cA : Circuit signature m n) :
    Circuit signature (n * q + m) (n * q) :=
  match q with
  | 0 => Circuit.wiring signature fun idx => idx.elim0
  | q' + 1 =>
    (barrelShiftCircuit n (q' + 1) (Nat.clog 2 n)).comp
      ((Circuit.id signature (n * (q' + 1))).parallel
        ((railBitsOfOneHot n (Nat.clog 2 n)).comp cA))

private theorem computesMonotoneShift_monotoneShiftCircuit_of_oneHot {n q m : ℕ}
    {α : Fin n → Fin m → Bool} {cA : Circuit signature m n}
    (hcA : ∀ k : Fin n, cA.eval interpretation (α k) = fun r => decide (r = k)) :
    ComputesMonotoneShift (monotoneShiftCircuit q cA) α := by
  cases q with
  | zero =>
    intro X k
    funext idx
    exact idx.elim0
  | succ q' =>
    intro X k
    set L := Nat.clog 2 n
    simp only [monotoneShiftCircuit, Circuit.eval_comp, Circuit.eval_parallel,
      Fin.append_comp_castAdd, Fin.append_comp_natAdd, Circuit.eval_wiring, Function.comp_id,
      hcA k]
    set R := (railBitsOfOneHot n L).eval interpretation (fun r => decide (r = k))
    have hpos : ∀ i (hi : i < L), R ⟨i, by omega⟩ = k.val.testBit i := by
      intro i hi
      simpa [R, hi] using eval_railBitsOfOneHot_oneHot n L k ⟨i, by omega⟩
    have hneg : ∀ i (hi : i < L), R ⟨L + i, by omega⟩ = !k.val.testBit i := by
      intro i hi
      have hnot : ¬ (L + i < L) := by omega
      simpa [R, hnot] using eval_railBitsOfOneHot_oneHot n L k ⟨L + i, by omega⟩
    exact eval_barrelShiftCircuit n (q' + 1) X k R hpos hneg

/-- **Theorem 1 (correctness)** ([Sergeev2020MonotoneShift], pp. 3–4): if `α` injectively indexes
an antichain in `Fin m → Bool` and `cA` computes the antichain monomials
`fun Y r => decide (α r ≤ Y)` (`Y^{α_r} = ⋀_{α_{r,t} = 1} Y_t`), then `monotoneShiftCircuit q cA`
computes the monotone cyclic shift operator `S_{q, α}`. -/
theorem computesMonotoneShift_monotoneShiftCircuit {n q m : ℕ}
    {α : Fin n → Fin m → Bool} {cA : Circuit signature m n}
    (hinj : Function.Injective α) (hanti : IsAntichain (· ≤ ·) (Set.range α))
    (hcA : cA.Computes interpretation fun Y r => decide (α r ≤ Y)) :
    ComputesMonotoneShift (monotoneShiftCircuit q cA) α := by
  refine computesMonotoneShift_monotoneShiftCircuit_of_oneHot fun k => ?_
  rw [hcA (α k)]
  funext r
  by_cases hrk : r = k
  · subst hrk; simp
  · simp only [hrk, decide_false, decide_eq_false_iff_not]
    exact hanti ⟨r, rfl⟩ ⟨k, rfl⟩ (hinj.ne hrk)

/-- **Theorem 1 (cost bound)** ([Sergeev2020MonotoneShift], pp. 3–4): `monotoneShiftCircuit q cA`
has binary monotone gate cost at most `cA.program.cost binaryCost + 4 * q * n * Nat.clog 2 n`
(`L(S_{q, A}) ≤ L(A) + O(q n log n)`). -/
theorem cost_monotoneShiftCircuit_le {n m : ℕ} (q : ℕ) (cA : Circuit signature m n) :
    (monotoneShiftCircuit q cA).program.cost binaryCost ≤
      cA.program.cost binaryCost + 4 * q * n * Nat.clog 2 n := by
  cases q with
  | zero =>
    simp [monotoneShiftCircuit]
  | succ q' =>
    simp only [monotoneShiftCircuit]
    rw [Circuit.cost_program_comp, Circuit.cost_program_parallel, Circuit.cost_program_wiring,
      Nat.zero_add, Circuit.cost_program_comp, cost_barrelShiftCircuit]
    have hrail := cost_railBitsOfOneHot_le n (Nat.clog 2 n)
    have hmul : n * Nat.clog 2 n + 3 * (q' + 1) * n * Nat.clog 2 n ≤
        4 * (q' + 1) * n * Nat.clog 2 n := by
      calc n * Nat.clog 2 n + 3 * (q' + 1) * n * Nat.clog 2 n
          ≤ (q' + 1) * (n * Nat.clog 2 n) + 3 * (q' + 1) * n * Nat.clog 2 n :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos q')) _
        _ = 4 * (q' + 1) * n * Nat.clog 2 n := by ring
    omega

/-- Explicit monotone shift circuit for the weight-`1` one-hot antichain `A₁`
([Sergeev2020MonotoneShift], pp. 2–3), using `Circuit.id` (`L(A₁) = 0`) for the monomial stage. -/
def oneHotShiftCircuit (n q : ℕ) : Circuit signature (n * q + n) (n * q) :=
  monotoneShiftCircuit q (Circuit.id signature n)

/-- `oneHotShiftCircuit n q` computes `S_{q, A₁}` on `oneHotShiftAntichain n`. -/
theorem computesMonotoneShift_oneHotShiftCircuit (n q : ℕ) :
    ComputesMonotoneShift (oneHotShiftCircuit n q) (oneHotShiftAntichain n) := by
  refine computesMonotoneShift_monotoneShiftCircuit (injective_oneHotShiftAntichain n)
    (isAntichain_range_oneHotShiftAntichain n) fun Y => funext fun r => ?_
  change Y r = decide (oneHotShiftAntichain n r ≤ Y)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  refine ⟨fun hYr i => ?_, fun hle => ?_⟩
  · by_cases hir : i = r <;> simp [oneHotShiftAntichain, hir, hYr]
  · exact Bool.eq_true_of_true_le (by simpa [oneHotShiftAntichain] using hle r)

/-- `oneHotShiftCircuit n q` uses at most `4 * q * n * Nat.clog 2 n` binary monotone gates
([Sergeev2020MonotoneShift], p. 3). -/
theorem cost_oneHotShiftCircuit_le (n q : ℕ) :
    (oneHotShiftCircuit n q).program.cost binaryCost ≤ 4 * q * n * Nat.clog 2 n := by
  simpa [oneHotShiftCircuit, Circuit.id, Circuit.cost_program_wiring] using
    cost_monotoneShiftCircuit_le q (Circuit.id signature n)

/-- Explicit monotone shift circuit for `dualRailShiftCode n b` whenever `Nat.clog 2 n ≤ b`
([Sergeev2020MonotoneShift], pp. 2–4), wiring the first `Nat.clog 2 n` positive and negated shift
bits directly into the barrel shifter with zero indicator gates. -/
def dualRailShiftCircuit (n q b : ℕ) (hb : Nat.clog 2 n ≤ b) :
    Circuit signature (n * q + 2 * b) (n * q) :=
  let L := Nat.clog 2 n
  let selectRail : Fin (2 * L) → Fin (2 * b) := fun t =>
    if h : t.val < L then ⟨t.val, by omega⟩ else ⟨b + (t.val - L), by omega⟩
  (barrelShiftCircuit n q L).comp
    ((Circuit.id signature (n * q)).parallel (Circuit.wiring signature selectRail))

/-- `dualRailShiftCircuit n q b hb` computes `S_{q, A₀}` on `dualRailShiftCode n b`. -/
theorem computesMonotoneShift_dualRailShiftCircuit (n q b : ℕ) (hb : Nat.clog 2 n ≤ b) :
    ComputesMonotoneShift (dualRailShiftCircuit n q b hb) (dualRailShiftCode n b) := by
  intro X k
  set L := Nat.clog 2 n
  simp only [dualRailShiftCircuit, Circuit.eval_comp, Circuit.eval_parallel,
    Fin.append_comp_castAdd, Fin.append_comp_natAdd, Circuit.eval_wiring, Function.comp_id]
  set R : Fin (2 * L) → Bool :=
    dualRailShiftCode n b k ∘ fun t : Fin (2 * L) =>
      if h : t.val < L then ⟨t.val, by omega⟩ else ⟨b + (t.val - L), by omega⟩
  have hpos : ∀ i (hi : i < L), R ⟨i, by omega⟩ = k.val.testBit i := by
    intro i hi
    simp [R, dualRailShiftCode, hi, hi.trans_le hb]
  have hneg : ∀ i (hi : i < L), R ⟨L + i, by omega⟩ = !k.val.testBit i := by
    intro i hi
    simp [R, dualRailShiftCode, show ¬ L + i < L by omega, show ¬ b + i < b by omega]
  exact eval_barrelShiftCircuit n q X k R hpos hneg

/-- `dualRailShiftCircuit n q b hb` uses **exact** binary monotone gate cost
`3 * q * n * Nat.clog 2 n`. -/
theorem cost_dualRailShiftCircuit (n q b : ℕ) (hb : Nat.clog 2 n ≤ b) :
    (dualRailShiftCircuit n q b hb).program.cost binaryCost = 3 * q * n * Nat.clog 2 n := by
  simp only [dualRailShiftCircuit]
  rw [Circuit.cost_program_comp, Circuit.cost_program_parallel, Circuit.cost_program_wiring,
    Circuit.cost_program_wiring, cost_barrelShiftCircuit]
  ring

/-! ### Theorem 3 and Permutation Corollary: Antichain-independent lower bounds -/

/-- **Monotone projection isolation at an OR gate** ([Sergeev2020MonotoneShift], proof of
Theorem 3, Step (a), p. 5): if `f, g : (Fin N → Bool) → Bool` are monotone and `(f x || g x) =
x i` for all `x`, then either `f` or `g` equals the coordinate projection `fun x => x i`. -/
theorem eq_proj_or_eq_proj_of_or {N : ℕ} {f g : (Fin N → Bool) → Bool} {i : Fin N}
    (hf : Monotone f) (hg : Monotone g) (hor : ∀ x, (f x || g x) = x i) :
    (∀ x, f x = x i) ∨ (∀ x, g x = x i) := by
  let ei : Fin N → Bool := fun r => decide (r = i)
  have one_side : ∀ {h : (Fin N → Bool) → Bool}, Monotone h →
      (∀ x, x i = false → h x = false) → h ei = true → ∀ x, h x = x i := by
    intro h hh hfalse htrue x
    cases hxi : x i
    · exact hfalse x hxi
    · have hle : ei ≤ x := fun r => by
        by_cases hri : r = i
        · subst hri; simp [ei, hxi]
        · simp [ei, hri]
      exact Bool.eq_true_of_true_le (htrue ▸ hh hle)
  have hei : (f ei || g ei) = true := by simpa [ei] using hor ei
  rcases Bool.or_eq_true_iff.mp hei with hfi | hgi
  · exact Or.inl (one_side hf (fun x hxi => (Bool.or_eq_false_iff.mp (hxi ▸ hor x)).1) hfi)
  · exact Or.inr (one_side hg (fun x hxi => (Bool.or_eq_false_iff.mp (hxi ▸ hor x)).2) hgi)

/-- **Monotone projection isolation at an AND gate** ([Sergeev2020MonotoneShift], proof of
Theorem 3, Step (a), p. 5): if `f, g : (Fin N → Bool) → Bool` are monotone and `(f x && g x) =
x i` for all `x`, then either `f` or `g` equals the coordinate projection `fun x => x i`. -/
theorem eq_proj_or_eq_proj_of_and {N : ℕ} {f g : (Fin N → Bool) → Bool} {i : Fin N}
    (hf : Monotone f) (hg : Monotone g) (hand : ∀ x, (f x && g x) = x i) :
    (∀ x, f x = x i) ∨ (∀ x, g x = x i) := by
  let ci : Fin N → Bool := fun r => decide (r ≠ i)
  have one_side : ∀ {h : (Fin N → Bool) → Bool}, Monotone h →
      (∀ x, x i = true → h x = true) → h ci = false → ∀ x, h x = x i := by
    intro h hh htrue hfalse x
    cases hxi : x i
    · have hle : x ≤ ci := fun r => by
        by_cases hri : r = i
        · subst hri; simp [ci, hxi]
        · simp [ci, hri]
      exact Bool.eq_false_of_le_false (hfalse ▸ hh hle)
    · exact htrue x hxi
  have hci : (f ci && g ci) = false := by simpa [ci] using hand ci
  rcases Bool.and_eq_false_iff.mp hci with hfi | hgi
  · exact Or.inl (one_side hf (fun x hxi => (Bool.and_eq_true_iff.mp ((hand x).trans hxi)).1) hfi)
  · exact Or.inr (one_side hg (fun x hxi => (Bool.and_eq_true_iff.mp ((hand x).trans hxi)).2) hgi)

/-- Input wires reachable backward from wire `w` in `p` via a directed path of at most `d` gates. -/
private def inputsWithin {N G : ℕ} (p : Program signature N G) :
    ℕ → Wire N G → Finset (Fin N)
  | 0, .input idx => {idx}
  | 0, .gate _ => ∅
  | _ + 1, .input idx => {idx}
  | d + 1, .gate g =>
    Finset.univ.biUnion fun a : Fin (signature.Arity (p.lines g).op) =>
      inputsWithin p d ((p.lines g).wires a)

private theorem inputsWithin_mono {N G : ℕ} (p : Program signature N G) :
    ∀ {d₁ d₂ : ℕ}, d₁ ≤ d₂ → ∀ w : Wire N G, inputsWithin p d₁ w ⊆ inputsWithin p d₂ w := by
  have hstep : ∀ (d : ℕ) (w : Wire N G), inputsWithin p d w ⊆ inputsWithin p (d + 1) w := by
    intro d
    induction d with
    | zero =>
      intro w
      cases w with
      | input idx => exact Subset.rfl
      | gate g => exact empty_subset _
    | succ d ih =>
      intro w
      cases w with
      | input idx => exact Subset.rfl
      | gate g =>
        intro x hx
        rw [inputsWithin, mem_biUnion] at hx ⊢
        obtain ⟨a, ha, hx⟩ := hx
        exact ⟨a, ha, ih _ hx⟩
  intro d₁ d₂ hd
  induction d₂, hd using Nat.le_induction with
  | base => intro _; exact Subset.rfl
  | succ d₂ _ ih => intro w; exact (ih w).trans (hstep d₂ w)

private theorem arity_le_two (op : Op) : signature.Arity op ≤ 2 := by
  cases op <;> simp

private theorem card_inputsWithin_le_two_pow {N G : ℕ} (p : Program signature N G) :
    ∀ (d : ℕ) (w : Wire N G), (inputsWithin p d w).card ≤ 2 ^ d
  | 0, .input _ => by simp [inputsWithin]
  | 0, .gate _ => by simp [inputsWithin]
  | d + 1, .input _ => by
    simp only [inputsWithin, card_singleton]
    exact Nat.one_le_two_pow
  | d + 1, .gate g => by
    rw [inputsWithin, pow_succ']
    calc (Finset.univ.biUnion fun a : Fin (signature.Arity (p.lines g).op) =>
          inputsWithin p d ((p.lines g).wires a)).card
        ≤ (Finset.univ : Finset (Fin (signature.Arity (p.lines g).op))).card * 2 ^ d :=
          Finset.card_biUnion_le_card_mul _ _ _ fun a _ =>
            card_inputsWithin_le_two_pow p d ((p.lines g).wires a)
      _ ≤ 2 * 2 ^ d := by
          rw [card_univ, Fintype.card_fin]
          exact Nat.mul_le_mul_right _ (arity_le_two (p.lines g).op)

private theorem exists_arg_eq_proj_of_interpretation_eq_proj {N : ℕ} (op : Op)
    (args : Fin (signature.Arity op) → (Fin N → Bool) → Bool) (u : Fin N)
    (hmono : ∀ a, Monotone (args a))
    (heval : ∀ X, interpretation op (fun a => args a X) = X u) :
    ∃ a : Fin (signature.Arity op), binaryCost op = 1 ∧ ∀ X, args a X = X u := by
  cases op with
  | const b =>
    exact False.elim (Bool.false_ne_true ((heval fun _ => false).symm.trans (heval fun _ => true)))
  | and =>
    rcases eq_proj_or_eq_proj_of_and (hmono 0) (hmono 1) heval with h0 | h1
    · exact ⟨0, rfl, h0⟩
    · exact ⟨1, rfl, h1⟩
  | or =>
    rcases eq_proj_or_eq_proj_of_or (hmono 0) (hmono 1) heval with h0 | h1
    · exact ⟨0, rfl, h0⟩
    · exact ⟨1, rfl, h1⟩

/-- Tracing backward along `p` from any wire `w` that computes `X u` under control `Y` selects a
set `S` of `{∧, ∨}` gates, all computing `X u` under `Y`, such that input `Fin.castAdd m u` reaches
`w` within `S.card` gate steps. -/
private theorem exists_projection_path {D m G : ℕ} (p : Program signature (D + m) G)
    (Y : Fin m → Bool) (u : Fin D) :
    ∀ w : Wire (D + m) G,
      (∀ X : Fin D → Bool, p.trace interpretation (Fin.append X Y) w = X u) →
      ∃ S : Finset (Fin G),
        Fin.castAdd m u ∈ inputsWithin p S.card w ∧
        (∀ g ∈ S,
          (∀ X : Fin D → Bool, p.trace interpretation (Fin.append X Y) (.gate g) = X u) ∧
          binaryCost (p.lines g).op = 1) ∧
        (∀ j, w = .gate j → ∀ g ∈ S, g ≤ j) ∧
        (∀ v, w = .input v → S = ∅) := by
  refine p.wire_induction (fun v hv => ?_) (fun g ih hg => ?_)
  · have hv_eq : v = Fin.castAdd m u := by
      revert hv
      refine Fin.addCases (fun u' hv => ?_) (fun t hv => ?_) v
      · by_contra hne
        have hu' : u' ≠ u := fun h => hne (congrArg (Fin.castAdd m) h)
        have hval := hv (fun r => decide (r = u))
        simp only [Program.trace, Wire.elim_input, Fin.append_left, decide_true] at hval
        exact hu' (of_decide_eq_true hval)
      · have h0 := hv (fun _ => false)
        have h1 := hv (fun _ => true)
        simp only [Program.trace, Wire.elim_input, Fin.append_right] at h0 h1
        exact False.elim (Bool.false_ne_true (h0.symm.trans h1))
    subst hv_eq
    refine ⟨∅, by simp [inputsWithin], by simp, ?_, fun _ _ => rfl⟩
    intro j hj
    cases hj
  · have hmono_arg : ∀ a, Monotone fun X : Fin D → Bool =>
        p.trace interpretation (Fin.append X Y) ((p.lines g).wires a) := by
      intro a X₁ X₂ hle
      refine trace_mono p (fun idx => ?_) _
      refine Fin.addCases (fun r => ?_) (fun _ => ?_) idx
      · simp only [Fin.append_left]; exact hle r
      · simp only [Fin.append_right]; exact le_rfl
    obtain ⟨a, hcost, ha⟩ := exists_arg_eq_proj_of_interpretation_eq_proj (p.lines g).op
      (fun a X => p.trace interpretation (Fin.append X Y) ((p.lines g).wires a)) u hmono_arg
      fun X => (p.trace_gate interpretation (Fin.append X Y) g).symm.trans (hg X)
    obtain ⟨S', hin', hS', hle', hemp'⟩ := ih a ha
    have hg_notMem : g ∉ S' := by
      cases hw : (p.lines g).wires a with
      | input v => rw [hemp' v hw]; exact notMem_empty g
      | gate j =>
        have hjlt : j < g := p.lt_of_lines_wires_eq_gate g a j hw
        intro hmem
        exact hjlt.not_ge (hle' j hw g hmem)
    refine ⟨insert g S', ?_, ?_, ?_, fun _ h => by cases h⟩
    · rw [card_insert_of_notMem hg_notMem, inputsWithin, mem_biUnion]
      exact ⟨a, mem_univ a, hin'⟩
    · intro g' hg'
      rcases mem_insert.mp hg' with rfl | hg'
      · exact ⟨hg, hcost⟩
      · exact hS' g' hg'
    · intro j hj g' hg'
      cases hj
      rcases mem_insert.mp hg' with rfl | hg'
      · exact le_rfl
      · cases hw : (p.lines g).wires a with
        | input v => rw [hemp' v hw] at hg'; exact absurd hg' (notMem_empty _)
        | gate j' =>
          exact (hle' j' hw g' hg').trans (p.lt_of_lines_wires_eq_gate g a j' hw).le

/-- Lamagna–Savage peeling bound on finite depth functions: if at most `2^d` elements of `s` have
`L x ≤ d` for every `d`, then `∑_{t=1}^{|s|} ⌈log₂ t⌉ ≤ ∑_{x ∈ s} L x`. -/
private theorem sum_clog_le_sum_of_card_filter_le_two_pow {α : Type*}
    (s : Finset α) (L : α → ℕ)
    (hcard : ∀ d : ℕ, (s.filter fun x => L x ≤ d).card ≤ 2 ^ d) :
    ∑ t ∈ Icc 1 s.card, Nat.clog 2 t ≤ ∑ x ∈ s, L x := by
  classical
  generalize hn : s.card = k
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have hs : s.Nonempty := card_pos.mp (by omega)
    obtain ⟨xm, hxm, hmax⟩ := exists_max_image s L hs
    have hfilt : s.filter (fun x => L x ≤ L xm) = s := filter_eq_self.mpr hmax
    have hclog : Nat.clog 2 (k + 1) ≤ L xm := by
      rw [Nat.clog_le_iff_le_pow Nat.one_lt_two, ← hn, ← hfilt]
      exact hcard (L xm)
    have hs' : (s.erase xm).card = k := by
      have := card_erase_of_mem hxm; omega
    have hih := ih (s.erase xm) (fun d => (card_le_card
      (filter_subset_filter _ (erase_subset xm s))).trans (hcard d)) hs'
    have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext t; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp), ← add_sum_erase _ _ hxm]
    exact Nat.add_le_add hclog hih

private theorem mul_log_sub_le_sum_clog (n : ℕ) :
    n * Nat.log 2 n - n ≤ ∑ t ∈ Icc 1 n, Nat.clog 2 t := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set L := Nat.log 2 n
  have hpowL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn
  have hpointwise : ∀ t ∈ Icc 1 n,
      (∑ j ∈ range L, if 2 ^ j < t then 1 else 0) ≤ Nat.clog 2 t := by
    intro t _
    rw [← sum_filter, ← card_eq_sum_ones]
    calc ((range L).filter (fun j => 2 ^ j < t)).card
        ≤ (range (Nat.clog 2 t)).card := card_le_card fun j hj => by
          rw [mem_filter] at hj
          rw [mem_range]
          by_contra hle
          exact hj.2.not_ge ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mp (Nat.not_lt.mp hle))
      _ = Nat.clog 2 t := card_range _
  have hswap : (∑ j ∈ range L, (n - 2 ^ j)) ≤ ∑ t ∈ Icc 1 n, Nat.clog 2 t := by
    calc ∑ j ∈ range L, (n - 2 ^ j)
        = ∑ j ∈ range L, ∑ t ∈ Icc 1 n, (if 2 ^ j < t then 1 else 0) := by
          refine sum_congr rfl fun j hj => ?_
          rw [mem_range] at hj
          have hjpow : 2 ^ j < n :=
            (Nat.pow_lt_pow_right Nat.one_lt_two hj).trans_le hpowL
          rw [← sum_filter, ← card_eq_sum_ones]
          have hfilt : (Icc 1 n).filter (fun t => 2 ^ j < t) = Icc (2 ^ j + 1) n := by
            ext t; simp only [mem_filter, mem_Icc]
            have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
            omega
          rw [hfilt, Nat.card_Icc]
          omega
      _ = ∑ t ∈ Icc 1 n, ∑ j ∈ range L, (if 2 ^ j < t then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ t ∈ Icc 1 n, Nat.clog 2 t := sum_le_sum hpointwise
  have hgeom : ∀ k ≤ L, n * k ≤ (∑ j ∈ range k, (n - 2 ^ j)) + 2 ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, sum_range_succ, pow_succ]
      have hk1 := ih (Nat.le_of_succ_le hk)
      have hk2 : 2 ^ k ≤ n :=
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_succ_le hk)).trans hpowL
      omega
  have := hgeom L le_rfl
  omega

/-- **Theorem 3 (exact finite sum form)** ([Sergeev2020MonotoneShift], pp. 4–6; after
[Chashkin2006] and [LamagnaSavage1974]): for *every* control code `α : Fin n → Fin m → Bool` and
*every* monotone circuit `c` computing `S_{q, α}`,
`q * (∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤ c.program.cost binaryCost`. -/
theorem mul_sum_clog_le_cost_of_computesMonotoneShift {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {α : Fin n → Fin m → Bool}
    (hc : ComputesMonotoneShift c α) :
    q * (∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤ c.program.cost binaryCost := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let : NeZero n := ⟨hn⟩
  let outIdx : Fin n → Fin (n * q) → Fin (n * q) := fun k u =>
    let (i, b) := finProdFinEquiv.symm u
    finProdFinEquiv ((cyclicShiftPerm k).symm i, b)
  have hout : ∀ (k : Fin n) (u : Fin (n * q)) (X : Fin (n * q) → Bool),
      c.program.trace interpretation (Fin.append X (α k)) (c.outputs (outIdx k u)) = X u := by
    intro k u X
    change c.eval interpretation (Fin.append X (α k)) (outIdx k u) = X u
    rw [hc X k]
    obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective u
    simp only [outIdx, Equiv.symm_apply_apply, cyclicShiftVec_symm_finProdFinEquiv]
  choose pathGates hpath using fun (k : Fin n) (u : Fin (n * q)) =>
    exists_projection_path c.program (α k) u (c.outputs (outIdx k u)) (hout k u)
  -- Step (b): for each shift `k`, the gate sets `pathGates k u` are pairwise disjoint binary gates.
  have hper_shift : ∀ k : Fin n,
      (∑ u : Fin (n * q), (pathGates k u).card) ≤ c.program.cost binaryCost := by
    intro k
    have hdisj :
        (↑(univ : Finset (Fin (n * q))) : Set (Fin (n * q))).PairwiseDisjoint (pathGates k) := by
      intro u₁ _ u₂ _ hne
      change Disjoint (pathGates k u₁) (pathGates k u₂)
      refine disjoint_left.2 fun g hg₁ hg₂ => ?_
      have := (((hpath k u₁).2.1 g hg₁).1 fun r => decide (r = u₁)).symm.trans
        (((hpath k u₂).2.1 g hg₂).1 fun r => decide (r = u₁))
      simp [hne.symm] at this
    rw [← card_biUnion hdisj, card_eq_sum_ones, c.program.cost_eq_sum]
    calc ∑ g ∈ univ.biUnion (pathGates k), 1
        = ∑ g ∈ univ.biUnion (pathGates k), binaryCost (c.program.lines g).op :=
          sum_congr rfl fun g hg => by
            obtain ⟨u, _, hgu⟩ := mem_biUnion.1 hg; exact ((hpath k u).2.1 g hgu).2.symm
      _ ≤ ∑ g : Fin c.size, binaryCost (c.program.lines g).op :=
          sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  -- Step (c): for each output `(j, b)`, the `n` shifts `k = j - i` have path-length sum ≥ ∑ clog.
  have hper_output : ∀ (j : Fin n) (b : Fin q),
      (∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤
        ∑ i : Fin n, (pathGates (cyclicShiftPerm i j) (finProdFinEquiv (i, b))).card := by
    intro j b
    let w := c.outputs (finProdFinEquiv (j, b))
    let L : Fin n → ℕ := fun i => (pathGates (cyclicShiftPerm i j) (finProdFinEquiv (i, b))).card
    have hcard : ∀ d : ℕ, ((univ : Finset (Fin n)).filter fun i => L i ≤ d).card ≤ 2 ^ d := by
      intro d
      let inWire : Fin n → Fin (n * q + m) :=
        fun i => Fin.castAdd m (finProdFinEquiv (i, b))
      have hinj : Function.Injective inWire := fun i₁ i₂ h =>
        (Prod.mk.inj (finProdFinEquiv.injective (Fin.castAdd_injective (n * q) m h))).1
      calc ((univ : Finset (Fin n)).filter fun i => L i ≤ d).card
          = (((univ : Finset (Fin n)).filter fun i => L i ≤ d).image inWire).card :=
            (card_image_of_injective _ hinj).symm
        _ ≤ (inputsWithin c.program d w).card := by
            refine card_le_card fun v hv => ?_
            obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
            have hji : (cyclicShiftPerm (cyclicShiftPerm i j)).symm i = j :=
              show i + (j - i) = j by rw [add_comm, sub_add_cancel]
            have hmem := (hpath (cyclicShiftPerm i j) (finProdFinEquiv (i, b))).1
            simp only [outIdx, Equiv.symm_apply_apply, hji] at hmem
            exact inputsWithin_mono c.program (mem_filter.1 hi).2 w hmem
        _ ≤ 2 ^ d := card_inputsWithin_le_two_pow c.program d w
    simpa [L] using sum_clog_le_sum_of_card_filter_le_two_pow (univ : Finset (Fin n)) L hcard
  -- Combine Steps (b) and (c) by reindexing `k = cyclicShiftPerm i j = j - i`.
  have htotal :
      n * (q * ∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤ n * c.program.cost binaryCost := by
    calc n * (q * ∑ t ∈ Icc 1 n, Nat.clog 2 t)
        = ∑ j : Fin n, ∑ b : Fin q, (∑ t ∈ Icc 1 n, Nat.clog 2 t) := by simp
      _ ≤ ∑ j : Fin n, ∑ b : Fin q,
            ∑ i : Fin n, (pathGates (cyclicShiftPerm i j) (finProdFinEquiv (i, b))).card :=
          sum_le_sum fun j _ => sum_le_sum fun b _ => hper_output j b
      _ = ∑ i : Fin n, ∑ b : Fin q,
            ∑ j : Fin n, (pathGates (cyclicShiftPerm i j) (finProdFinEquiv (i, b))).card :=
          (sum_congr rfl fun _ _ => Finset.sum_comm).trans
            (Finset.sum_comm.trans (sum_congr rfl fun _ _ => Finset.sum_comm))
      _ = ∑ i : Fin n, ∑ b : Fin q,
            ∑ k : Fin n, (pathGates k (finProdFinEquiv (i, b))).card :=
          sum_congr rfl fun i _ => sum_congr rfl fun b _ => Equiv.sum_comp (cyclicShiftPerm i)
            fun k => (pathGates k (finProdFinEquiv (i, b))).card
      _ = ∑ k : Fin n, ∑ u : Fin (n * q), (pathGates k u).card :=
          (sum_congr rfl fun _ _ => Finset.sum_comm).trans (Finset.sum_comm.trans
            (sum_congr rfl fun k _ => by rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]))
      _ ≤ ∑ _k : Fin n, c.program.cost binaryCost := sum_le_sum fun k _ => hper_shift k
      _ = n * c.program.cost binaryCost := by simp
  exact Nat.le_of_mul_le_mul_left htotal (Nat.pos_of_ne_zero hn)

/-- **Theorem 3 (`q n log₂ n - O(q n)` form)** ([Sergeev2020MonotoneShift], p. 4): for *every*
control code `α : Fin n → Fin m → Bool` and *every* monotone circuit `c` computing `S_{q, α}`,
`q * n * Nat.log 2 n - q * n ≤ c.program.cost binaryCost`. -/
theorem mul_log_sub_le_cost_of_computesMonotoneShift {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {α : Fin n → Fin m → Bool}
    (hc : ComputesMonotoneShift c α) :
    q * n * Nat.log 2 n - q * n ≤ c.program.cost binaryCost := by
  calc q * n * Nat.log 2 n - q * n
      = q * (n * Nat.log 2 n - n) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_assoc]
    _ ≤ q * (∑ t ∈ Icc 1 n, Nat.clog 2 t) :=
        Nat.mul_le_mul_left q (mul_log_sub_le_sum_clog n)
    _ ≤ c.program.cost binaryCost :=
        mul_sum_clog_le_cost_of_computesMonotoneShift hc

/-- **Permutation Corollary (exact finite sum form)** ([Sergeev2020MonotoneShift], p. 6): for
*every* permutation code `β : Equiv.Perm (Fin n) → Fin m → Bool` and *every* monotone circuit `c`
computing `P_{q, Π}`, `q * (∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤ c.program.cost binaryCost`. -/
theorem mul_sum_clog_le_cost_of_computesMonotonePerm {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {β : Equiv.Perm (Fin n) → Fin m → Bool}
    (hc : ComputesMonotonePerm c β) :
    q * (∑ t ∈ Icc 1 n, Nat.clog 2 t) ≤ c.program.cost binaryCost :=
  mul_sum_clog_le_cost_of_computesMonotoneShift hc.computesMonotoneShift

/-- **Permutation Corollary (`q n log₂ n - O(q n)` form)** ([Sergeev2020MonotoneShift], p. 6): for
*every* permutation code `β : Equiv.Perm (Fin n) → Fin m → Bool` and *every* monotone circuit `c`
computing `P_{q, Π}`, `q * n * Nat.log 2 n - q * n ≤ c.program.cost binaryCost`. -/
theorem mul_log_sub_le_cost_of_computesMonotonePerm {n q m : ℕ}
    {c : Circuit signature (n * q + m) (n * q)} {β : Equiv.Perm (Fin n) → Fin m → Bool}
    (hc : ComputesMonotonePerm c β) :
    q * n * Nat.log 2 n - q * n ≤ c.program.cost binaryCost :=
  mul_log_sub_le_cost_of_computesMonotoneShift hc.computesMonotoneShift

end Cslib.Circuits.Monotone
