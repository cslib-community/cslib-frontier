/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.QuadForm
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.Steiner
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.Uniform
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hyperedge gate-sweep circuit lower bounds

Instead of expanding each multi-consumer wire into a fixed binary junction chain before choosing a
layout, the post-layout Steiner compiler (`Compiler.steinerNetwork` in
`CslibFrontier/Computability/Circuit/Frontier/Compiler/GateSweep/Steiner.lean`) orders the
computation nodes `Compiler.Node c` first and then threads a linear Steiner chain through the sorted
support of each active signal. Every straddling signal crosses each prefix cut **at most once**, so
the multigraph cutwidth equals the hyperedge cutwidth `Compiler.signalWidth c π`.

Combining `Compiler.steinerNetwork` with discrete uniform bucket layouts and supporting-line
tangents (`CslibFrontier/Computability/Circuit/Frontier/Compiler/GateSweep/Uniform.lean`) and with
slice reductions on `Matrix.DisjointBlockRobust` polar matrices
(`CslibFrontier/Computability/Circuit/Frontier/Compiler/GateSweep/QuadForm.lean`) yields five
unconditional theorem families using zero Gaussian measure theory (the post-layout Steiner compiler
and all five gate-sweep lower-bound families below are original to this library):

1. **Bounded fan-in worst-case (`Ω(log r)`):** For every `r ≥ 2` and `k₀ : ℕ`, dense rectangle-free
   sets require `c.innerSize > (gateSweepCoefficient r k₀ - ε) n`, where
   `gateSweepCoefficient r k₀ = (k₀ + 2) / (r + 2 ^ k₀ - k₀ - 1)`. Choosing
   `k₀ = ⌊log₂ (r / ⌊log₂ r⌋)⌋` gives `(r - 1) * c.innerSize > (log₂ r - log₂ log₂ r - 1 - ε) n`
   (`eventually_log_sub_log_log_lt_mul_innerSize`), with concrete rational instances `28 / 9` at
   `r = 8`, `78 / 17 ≈ 4.5882` at `r = 40`, and `126 / 25 = 5.04` at `r = 64`.
2. **Bounded fan-in average-case:** Below `(gateSweepCoefficient r k₀ - ε) n` inner gates,
   `agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + exp (-γ n)` for all `r ≥ 2` and
   `k₀ : ℕ` (`exists_eventually_agreement_le_gateSweep`, `exists_eventually_agreement_le_log`).
3. **Low-reuse circuits at fan-in two:** Grouping unit-fanout gate trees eliminates unsevered
   fan-out-one gate wires from strict cuts, giving
   `(k₀ + 2 - ε) n < c.innerSize + (2 ^ k₀ - k₀) * Compiler.multiFanoutSize c` for all `k₀ ≥ 1`
   both in the worst case (`eventually_lt_innerSize_add_multiFanoutSize`, e.g. `s + 12 g_{≥2} > 6n`
   at `k₀ = 4`) and in the average case (`exists_eventually_agreement_le_multiFanoutSize`).
4. **Nondeterministic bounded fan-in:** Hiding `k` witness inputs in `Compiler.steinerNetwork`
   gives `(4 / (r + 1) - ε) n < c.innerSize` uniformly in `k : ℕ` for all `r ≥ 2`
   (`eventually_four_div_lt_innerSize_of_nondeterministicDecides`).
5. **Quadratic-form correlation**
   (`CslibFrontier/Computability/Circuit/Frontier/Compiler/GateSweep/QuadForm.lean`, re-exported
   here): Exponentially small correlation against `Cslib.Circuits.Frontier.symmHardForm` below
   `quadFormGateSweepCoefficient r k₀` and `(log₂ r - log₂ log₂ r - 2 - ε) n`.

## Main definitions

* `Cslib.Circuits.Frontier.gateSweepCoefficient r k₀`: `(k₀ + 2) / (r + 2 ^ k₀ - k₀ - 1)`.
* `Cslib.Circuits.Frontier.Compiler.hiddenSteinerNetwork`: `Compiler.steinerNetwork` with its last
  `k` witness inputs hidden.

## Main results

* `Cslib.Circuits.Frontier.eventually_gateSweep_lt_innerSize`,
  `Cslib.Circuits.Frontier.eventually_log_sub_log_log_lt_mul_innerSize`: Family 1 (worst-case).
* `Cslib.Circuits.Frontier.exists_eventually_agreement_le_gateSweep`,
  `Cslib.Circuits.Frontier.exists_eventually_agreement_le_log`: Family 2 (average-case).
* `Cslib.Circuits.Frontier.eventually_lt_innerSize_add_multiFanoutSize`,
  `Cslib.Circuits.Frontier.exists_eventually_agreement_le_multiFanoutSize`: Family 3 (low-reuse).
* `Cslib.Circuits.Frontier.eventually_four_div_lt_innerSize_of_nondeterministicDecides`: Family 4
  (nondeterministic).
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics
open scoped BigOperators

universe u v

/-! ### Gate-sweep coefficients and `Ω(log r)` specialization -/

/-- The hyperedge gate-sweep coefficient `(k₀ + 2) / (r + 2 ^ k₀ - k₀ - 1)` for fan-in `r`. -/
@[expose] noncomputable def gateSweepCoefficient (r k₀ : ℕ) : ℝ :=
  (k₀ + 2 : ℝ) / ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1)

theorem gateSweepCoefficient_pos {r : ℕ} (hr : 1 ≤ r) (k₀ : ℕ) :
    0 < gateSweepCoefficient r k₀ := by
  unfold gateSweepCoefficient
  have hd : (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact div_pos (by positivity) hd

/-- Explicit `Ω(log r)` choice of `k₀` for `gateSweepCoefficient`: for every `r ≥ 2`, some `k₀ : ℕ`
satisfies `log₂ r - log₂ log₂ r - 1 ≤ (r - 1) · gateSweepCoefficient r k₀`. -/
theorem exists_log_sub_log_log_le_mul_gateSweepCoefficient {r : ℕ} (hr : 2 ≤ r) :
    ∃ k₀ : ℕ,
      Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 ≤
        (r - 1 : ℝ) * gateSweepCoefficient r k₀ := by
  rcases lt_or_ge r 4 with hsmall | hr4
  · refine ⟨1, ?_⟩
    have hr_cases : r = 2 ∨ r = 3 := by omega
    rcases hr_cases with rfl | rfl
    · rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 : ℕ) by norm_num, Real.logb_two_pow, Nat.cast_one,
        Real.logb_one]
      unfold gateSweepCoefficient
      norm_num
    · have hlog3_ge : 1 ≤ Real.logb 2 (3 : ℝ) := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      have hlog3_le : Real.logb 2 (3 : ℝ) ≤ 2 := by
        calc Real.logb 2 (3 : ℝ)
            ≤ Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
          _ = 2 := by rw [Real.logb_two_pow]; norm_num
      have hll_nn : 0 ≤ Real.logb 2 (Real.logb 2 (3 : ℝ)) :=
        Real.logb_nonneg (by norm_num) hlog3_ge
      have hrhs : ((3 : ℕ) - 1 : ℝ) * gateSweepCoefficient 3 1 = 2 := by
        unfold gateSweepCoefficient
        norm_num
      push_cast at hrhs ⊢
      linarith
  · obtain ⟨k₀, _, hk₀_pow, hlog⟩ := exists_mul_two_pow_le_and_logb_sub_logb_le hr4
    refine ⟨k₀, ?_⟩
    have hk₀_alg : (k₀ : ℝ) ≤ (r - 1 : ℝ) * gateSweepCoefficient r k₀ := by
      unfold gateSweepCoefficient
      have hd_pos : (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
        have h1 := quadFormGateSweep_denom_ge r k₀
        have h2 : (4 : ℝ) ≤ r := by exact_mod_cast hr4
        linarith
      rw [mul_div_assoc', le_div_iff₀ hd_pos]
      have hk₀_pow_r : (k₀ : ℝ) * (2 : ℝ) ^ k₀ ≤ r := by exact_mod_cast hk₀_pow
      have hr4_r : (4 : ℝ) ≤ r := by exact_mod_cast hr4
      have hk₀_nn : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg k₀
      nlinarith [sq_nonneg (k₀ : ℝ)]
    linarith

/-! ### Tangent upper bounds on expected straddle counts -/

/-- Supporting-line bound on `∑_w (1 - 2^{1 - |support w|})` for any circuit of fan-in at most `r`
and any tangent parameter `k₀ : ℕ`. -/
private theorem sum_straddle_le_of_tangent {σ : Signature.{v}} {n m r : ℕ} (hr : 1 ≤ r)
    (k₀ : ℕ) (c : Circuit σ n m) (hfan : c.FanInAtMost r) [Fintype (Compiler.ActiveSignal c)] :
    (∑ w : Compiler.ActiveSignal c,
        (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n +
      (((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀) * c.innerSize +
      ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
      (m : ℝ) / (2 : ℝ) ^ k₀ := by
  classical
  have := Fintype.ofFinite {i : Fin n // Compiler.Reach c (.input i)}
  have := Fintype.ofFinite (Compiler.InnerGate c)
  have htan :
      (∑ w : Compiler.ActiveSignal c,
          (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
        ∑ w : Compiler.ActiveSignal c,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c w).ncard : ℝ) / (2 : ℝ) ^ k₀) :=
    Finset.sum_le_sum fun w _ =>
      Compiler.one_sub_two_pow_le_tangent k₀
        ((ncard_pos (toFinite _)).mpr (Compiler.support_nonempty w))
  have hcard_act :
      (Fintype.card (Compiler.ActiveSignal c) : ℝ) =
        ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) +
          Nat.card (Compiler.InnerGate c) := by
    have hnat : Fintype.card (Compiler.ActiveSignal c) =
        {i : Fin n | Compiler.Reach c (.input i)}.ncard + Nat.card (Compiler.InnerGate c) := by
      rw [Fintype.card_congr (Compiler.ActiveSignal.equiv c), Fintype.card_sum,
        ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact congrArg (· + Nat.card (Compiler.InnerGate c))
        (Nat.card_coe_set_eq {i : Fin n | Compiler.Reach c (.input i)})
    exact_mod_cast hnat
  have hcompl :
      ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) +
        {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard = n := by
    have hnc : {i : Fin n | ¬ Compiler.Reach c (.input i)} =
        {i : Fin n | Compiler.Reach c (.input i)}ᶜ := rfl
    rw [hnc, ← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsupp :
      (∑ w : Compiler.ActiveSignal c, ((Compiler.support c w).ncard : ℝ)) ≤
        (r + 1 : ℝ) * Nat.card (Compiler.InnerGate c) + m := by
    exact_mod_cast Compiler.sum_ncard_support_le_card_innerGate hfan
  have hG_le : (Nat.card (Compiler.InnerGate c) : ℝ) ≤ c.innerSize := by
    exact_mod_cast Compiler.card_innerGate_le (c := c)
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hDr_nn : (0 : ℝ) ≤ ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀ := by
    refine div_nonneg ?_ hpos2.le
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hd_nn : (0 : ℝ) ≤ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard := Nat.cast_nonneg _
  have hsum_rhs :
      (∑ w : Compiler.ActiveSignal c,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c w).ncard : ℝ) / (2 : ℝ) ^ k₀)) =
        (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * (Fintype.card (Compiler.ActiveSignal c) : ℝ) +
          (∑ w : Compiler.ActiveSignal c, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
      ← Finset.sum_div]
  have hsupp_div :
      (∑ w : Compiler.ActiveSignal c, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ ≤
        ((r + 1 : ℝ) * Nat.card (Compiler.InnerGate c) + m) / (2 : ℝ) ^ k₀ :=
    div_le_div_of_nonneg_right hsupp hpos2.le
  have halg :
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) *
          (({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) +
            Nat.card (Compiler.InnerGate c)) +
        ((r + 1 : ℝ) * Nat.card (Compiler.InnerGate c) + m) / (2 : ℝ) ^ k₀ =
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n -
        {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
        (((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀) * Nat.card (Compiler.InnerGate c) +
        (m : ℝ) / (2 : ℝ) ^ k₀ := by
    have hRin : ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) =
        n - {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard := by linarith
    rw [hRin]
    field_simp
    ring
  have hG_mul := mul_le_mul_of_nonneg_left hG_le hDr_nn
  rw [hsum_rhs, hcard_act] at htan
  linarith

/-- Supporting-line bound on non-unit active signals at fan-in two (`k₀ ≥ 1`). -/
private theorem sum_nonUnit_straddle_le_of_tangent {σ : Signature.{v}} {n m k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (c : Circuit σ n m) (hfan : c.FanInAtMost 2) [Fintype (Compiler.ActiveSignal c)]
    [DecidablePred (Compiler.IsUnitGateSignal c)] :
    (∑ w : Compiler.ActiveSignal c with ¬ Compiler.IsUnitGateSignal c w,
        (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n +
      ((c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c) / (2 : ℝ) ^ k₀ +
      ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
      (m : ℝ) / (2 : ℝ) ^ k₀ := by
  classical
  have := Fintype.ofFinite {i : Fin n // Compiler.Reach c (.input i)}
  have := Fintype.ofFinite (Compiler.InnerGate c)
  let S_nu := Finset.univ.filter fun w : Compiler.ActiveSignal c => ¬ Compiler.IsUnitGateSignal c w
  have htan :
      (∑ w ∈ S_nu, (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
        ∑ w ∈ S_nu,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c w).ncard : ℝ) / (2 : ℝ) ^ k₀) :=
    Finset.sum_le_sum fun w _ =>
      Compiler.one_sub_two_pow_le_tangent k₀
        ((ncard_pos (toFinite _)).mpr (Compiler.support_nonempty w))
  have hcard_nu :
      (S_nu.card : ℝ) =
        ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) + Compiler.multiFanoutSize c := by
    let emb_in : {i : Fin n // Compiler.Reach c (.input i)} ↪ Compiler.ActiveSignal c :=
      ⟨fun x => .input x.1 x.2, fun _ _ h => Subtype.ext (Compiler.ActiveSignal.input.inj h)⟩
    let emb_gt : Compiler.InnerGate c ↪ Compiler.ActiveSignal c :=
      ⟨Compiler.ActiveSignal.gate, fun _ _ h => Compiler.ActiveSignal.gate.inj h⟩
    let M_fin := Finset.univ.filter fun g : Compiler.InnerGate c => g ∈ Compiler.multiFanoutGates c
    have hdisj : Disjoint (Finset.univ.map emb_in) (M_fin.map emb_gt) := by
      refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
      obtain ⟨⟨i, _⟩, -, rfl⟩ := Finset.mem_map.mp hw₁
      obtain ⟨g, -, heq⟩ := Finset.mem_map.mp hw₂
      cases heq
    have hunion : S_nu = Finset.univ.map emb_in ∪ M_fin.map emb_gt := by
      ext w
      constructor
      · intro hw
        have hnu : ¬ Compiler.IsUnitGateSignal c w := (Finset.mem_filter.mp hw).2
        cases w with
        | input i hi =>
          exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩)
        | gate g =>
          refine Finset.mem_union_right _ (Finset.mem_map.mpr ⟨g, ?_, rfl⟩)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ g, ?_⟩
          have hp := Compiler.fanout_pos ((.gate g : Compiler.ActiveSignal c).toSignal)
          change ¬ Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal) = 1 at hnu
          change 2 ≤ Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal)
          omega
      · intro hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
        rcases Finset.mem_union.mp hw with hin | hgt
        · obtain ⟨⟨i, hi⟩, -, rfl⟩ := Finset.mem_map.mp hin
          exact id
        · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hgt
          have h2 : 2 ≤ Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal) :=
            (Finset.mem_filter.mp hg).2
          change ¬ Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal) = 1
          omega
    have hcard_in : Fintype.card {i : Fin n // Compiler.Reach c (.input i)} =
        {i : Fin n | Compiler.Reach c (.input i)}.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq {i : Fin n | Compiler.Reach c (.input i)}
    have hcard_M : M_fin.card = Compiler.multiFanoutSize c := by
      rw [Compiler.multiFanoutSize, ← ncard_coe_finset]
      congr 1
      ext g
      simp [M_fin]
    have hcard_nat : S_nu.card =
        {i : Fin n | Compiler.Reach c (.input i)}.ncard + Compiler.multiFanoutSize c := by
      rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_univ, hcard_in, hcard_M]
    exact_mod_cast hcard_nat
  have hcompl :
      ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) +
        {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard = n := by
    have hnc : {i : Fin n | ¬ Compiler.Reach c (.input i)} =
        {i : Fin n | Compiler.Reach c (.input i)}ᶜ := rfl
    rw [hnc, ← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsupp :
      (∑ w ∈ S_nu, ((Compiler.support c w).ncard : ℝ)) ≤
        (c.innerSize : ℝ) + 2 * Compiler.multiFanoutSize c + m := by
    have h1 := Compiler.sum_ncard_support_nonUnit_le hfan
    have hnat : ∑ w ∈ S_nu, (Compiler.support c w).ncard ≤
        c.innerSize + 2 * Compiler.multiFanoutSize c + m :=
      h1.trans (Nat.add_le_add_right
        (Nat.add_le_add_right (Compiler.card_innerGate_le (c := c)) _) m)
    exact_mod_cast hnat
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hd_nn : (0 : ℝ) ≤ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard := Nat.cast_nonneg _
  have hsum_rhs :
      (∑ w ∈ S_nu,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c w).ncard : ℝ) / (2 : ℝ) ^ k₀)) =
        (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * (S_nu.card : ℝ) +
          (∑ w ∈ S_nu, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm, ← Finset.sum_div]
  have hsupp_div :
      (∑ w ∈ S_nu, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ ≤
        ((c.innerSize : ℝ) + 2 * Compiler.multiFanoutSize c + m) / (2 : ℝ) ^ k₀ :=
    div_le_div_of_nonneg_right hsupp hpos2.le
  have halg :
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) *
          (({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) + Compiler.multiFanoutSize c) +
        ((c.innerSize : ℝ) + 2 * Compiler.multiFanoutSize c + m) / (2 : ℝ) ^ k₀ =
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n -
        {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
        ((c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c) / (2 : ℝ) ^ k₀ +
        (m : ℝ) / (2 : ℝ) ^ k₀ := by
    have hRin : ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) =
        n - {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard := by linarith
    rw [hRin]
    field_simp
    ring
  have _ := hk₀
  dsimp only [S_nu] at htan hsum_rhs hsupp_div
  rw [hsum_rhs, hcard_nu] at htan
  linarith

/-! ### Single-circuit Steiner demand and agreement lemmas -/

section SingleCircuit

/-- If a single-output circuit `c` decides `S`, so does `steinerNetwork c I (fun _ => Acc) π`. -/
theorem Compiler.accepted_steinerNetwork_of_decides {U : Type u} {σ : Signature.{v}} {n : ℕ}
    {c : Circuit σ n 1} {I : Interpretation σ U} {Acc : Set U} {S : Set (Fin n → U)}
    (hS : c.Decides I Acc S) {π : Layout (Compiler.Node c)} :
    (Compiler.steinerNetwork c I (fun _ => Acc) π).accepted = S := by
  rw [Compiler.accepted_steinerNetwork_single]
  ext x
  exact (hS x).symm

variable {U : Type u} [Finite U] [Nontrivial U] {σ : Signature.{v}} {n : ℕ}
  (I : Interpretation σ U) (Acc : Set U) (c : Circuit σ n 1)

/-- **Steiner frontier demand.** For a circuit `c` of fan-in at most `r ≥ 2` deciding a large
`K`-rectangle-free set `S ⊆ U^n`, every layout `π` of `Compiler.Node c` satisfies
`log_q |S| ≤ signalWidth c π + (3 r + 2) + 3 log_q K + log_q (|Node c| + 1)`, while unread inputs
satisfy `q ^ |unread| < K`. -/
theorem logb_ncard_le_signalWidth {r K : ℕ} {S : Set (Fin n → U)} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) (hdec : c.Decides I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) (π : Layout (Compiler.Node c)) :
    Real.logb (Nat.card U) S.ncard ≤
      Compiler.signalWidth c π + (3 * r + 2 : ℕ) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ∧
    Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K := by
  set N := Compiler.steinerNetwork c I (fun _ => Acc) π
  have hacc : N.accepted = S := Compiler.accepted_steinerNetwork_of_decides hdec
  have hw : N.width π ≤ Compiler.signalWidth c π := by
    rw [Compiler.steinerNetwork_toMultigraph, Compiler.width_steinerGraph_eq]
  have hd : N.MaxDegreeLE (2 * (r + 1)) := by
    rw [Compiler.steinerNetwork_toMultigraph]
    exact Compiler.maxDegreeLE_steinerGraph hfan
  have hm : ∀ u : Compiler.Node c, (N.readAt u).ncard ≤ r := fun u =>
    (Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega))
  have hdem := N.logb_ncard_accepted_le (hacc ▸ hfree) (hacc ▸ hbig) π hw hd hm
  rw [hacc] at hdem
  have hunread := hfree.pow_ncard_compl_lt (hacc ▸ N.dependsOn_read) hbig
  have hread_compl : N.readᶜ = {i : Fin n | ¬ Compiler.Reach c (.input i)} := by
    rw [Compiler.read_steinerNetwork]
    rfl
  rw [hread_compl] at hunread
  refine ⟨hdem.trans_eq ?_, hunread⟩
  push_cast
  ring

/-- **Agreement when many inputs are unreachable.** -/
theorem agreement_le_of_not_reach {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hu : K ≤ Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤
      1 / 2 + b + (Nat.card U * K ^ 2 : ℕ) / (Nat.card U : ℝ) ^ n := by
  have hread : (Compiler.network c I fun _ => Acc).readᶜ =
      {i : Fin n | ¬ Compiler.Reach c (.input i)} := by
    rw [Compiler.read_network]
    rfl
  exact agreement_le_of_unread I Acc c hS hb hK (hread.symm ▸ hu)

/-- **Agreement along a Steiner node layout.** -/
theorem agreement_le_of_signalWidth {S : Set (Fin n → U)} {K r : ℕ} {b : ℝ} (hr : 2 ≤ r)
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hfan : c.FanInAtMost r)
    (hu : Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K)
    (π : Layout (Compiler.Node c)) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b +
      (K ^ 3 * (Nat.card (Compiler.Node c) + 1) *
          Nat.card U ^ (Compiler.signalWidth c π + 3 * r + 2) : ℕ) /
        (Nat.card U : ℝ) ^ n := by
  set V := Nat.card (Compiler.Node c)
  set q := Nat.card U
  set w := Compiler.signalWidth c π
  have bound (A : Set U) :=
    (Compiler.steinerNetwork c I (fun _ => A) π).abs_signedCount_accepted_le π
      (fun _ _ _ => Compiler.satisfies_steinerNetwork_unique) hb hS
      (w := w) (d := 2 * (r + 1)) (m := r)
      (by rw [Compiler.steinerNetwork_toMultigraph, Compiler.width_steinerGraph_eq])
      (by
        rw [Compiler.steinerNetwork_toMultigraph]
        exact Compiler.maxDegreeLE_steinerGraph hfan)
      (fun u => (Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega)))
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [Compiler.accepted_steinerNetwork_single] at h₁
  have hacc_c : (Compiler.steinerNetwork c I (fun _ => Accᶜ) π).accepted =
      {x | c.eval I x 0 ∈ Acc}ᶜ := Compiler.accepted_steinerNetwork_single
  rw [hacc_c] at h₂
  have hread₁ : (Compiler.steinerNetwork c I (fun _ => Acc) π).readᶜ =
      {i : Fin n | ¬ Compiler.Reach c (.input i)} := by
    rw [Compiler.read_steinerNetwork]; rfl
  have hread₂ : (Compiler.steinerNetwork c I (fun _ => Accᶜ) π).readᶜ =
      {i : Fin n | ¬ Compiler.Reach c (.input i)} := by
    rw [Compiler.read_steinerNetwork]; rfl
  rw [hread₁] at h₁
  rw [hread₂] at h₂
  have hdeg_eq : w + 2 * (r + 1) + r = w + 3 * r + 2 := by omega
  rw [hdeg_eq] at h₁ h₂
  have h := agreement_le h₁ h₂
  have hres :
      (K - 1) ^ 2 * (V * q ^ (w + 3 * r + 2) +
          q ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) ≤
        K ^ 3 * (V + 1) * q ^ (w + 3 * r + 2) := by
    have hq1 : 1 ≤ q ^ (w + 3 * r + 2) := Nat.one_le_pow _ _ Nat.card_pos
    have hK_pos : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hu
    calc _ ≤ K ^ 2 * (V * K * q ^ (w + 3 * r + 2) + K * q ^ (w + 3 * r + 2)) := by
          gcongr
          · omega
          · exact Nat.le_mul_of_pos_right _ hK_pos
          · exact hu.le.trans (Nat.le_mul_of_pos_right _ hq1)
      _ = K ^ 3 * (V + 1) * q ^ (w + 3 * r + 2) := by ring
  have hresR :
      (((K - 1) ^ 2 * (V * q ^ (w + 3 * r + 2) +
          q ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) : ℕ) : ℝ) ≤
        ((K ^ 3 * (V + 1) * q ^ (w + 3 * r + 2) : ℕ) : ℝ) := by
    exact_mod_cast hres
  have hN_card : (Nat.card (Fin n → U) : ℝ) = (q : ℝ) ^ n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    push_cast
    rfl
  have hN_pos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : 0 < q := Nat.card_pos
    positivity
  rw [hN_card] at h
  refine h.trans ?_
  have hhalf : ∀ R : ℝ, (R + R) / (2 * (q : ℝ) ^ n) = R / (q : ℝ) ^ n := fun R => by
    field_simp
    ring
  rw [hhalf]
  linarith [div_le_div_of_nonneg_right hresR hN_pos.le]

end SingleCircuit

/-! ### Asymptotic helper bounds for logarithms and residuals -/

private theorem isLittleO_logb_of_log {K : ℕ → ℕ}
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) (q : ℝ) :
    (fun n => Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
  (hK.const_mul_left (1 / Real.log q)).congr_left fun n => by
    simp only [Real.logb]
    ring

private theorem exists_nat_pos_mul_ge {A δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, 1 ≤ M ∧ A ≤ δ * M := by
  refine ⟨⌈A / δ⌉₊ + 1, Nat.le_add_left 1 _, ?_⟩
  have h1 : A / δ ≤ (⌈A / δ⌉₊ + 1 : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  have h2 := (div_le_iff₀ hδ).mp h1
  linarith

private theorem mul_sqrt_le_of_sq_le {a M K V δ : ℝ} {N_sq n : ℕ}
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hK : 0 ≤ K) (hδ : 0 < δ) (hV : V ≤ K * n)
    (hN : (a * √(M * K)) ^ 2 ≤ (δ * δ) * N_sq) (hn : N_sq ≤ n) :
    a * √(M * V) ≤ δ * n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN_r : (N_sq : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : M * V ≤ (M * K) * n := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hV hM
  have h2 : a * √(M * V) ≤ (a * √(M * K)) * √n := by
    calc a * √(M * V) ≤ a * √((M * K) * n) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) ha
      _ = (a * √(M * K)) * √n := by
          rw [Real.sqrt_mul (mul_nonneg hM hK), mul_assoc]
  have hdiv : (a * √(M * K) / δ) ^ 2 ≤ n := by
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hδ)]
    calc (a * √(M * K)) ^ 2 ≤ (δ * δ) * N_sq := hN
      _ ≤ (δ * δ) * n := mul_le_mul_of_nonneg_left hN_r (by positivity)
      _ = n * δ ^ 2 := by ring
  have hle : a * √(M * K) ≤ δ * √n :=
    ((div_le_iff₀ hδ).mp (Real.le_sqrt_of_sq_le hdiv)).trans_eq (mul_comm _ _)
  calc a * √(M * V) ≤ (a * √(M * K)) * √n := h2
    _ ≤ (δ * √n) * √n := mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
    _ = δ * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]

private theorem logb_residual_nat {q K V m : ℕ} (hq : 1 < q) (hK : 0 < K) :
    Real.logb q ((K ^ 3 * (V + 1) * q ^ m : ℕ) : ℝ) =
      (m : ℝ) + 3 * Real.logb q K + Real.logb q ((V : ℝ) + 1) := by
  have hq_r : (1 : ℝ) < q := by exact_mod_cast hq
  have hq_pos : 0 < q := by omega
  push_cast
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq_r]
  push_cast
  ring

private theorem residual_nat_pos {q K V m : ℕ} (hq : 0 < q) (hK : 0 < K) :
    (0 : ℝ) < ((K ^ 3 * (V + 1) * q ^ m : ℕ) : ℝ) := by
  exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hK) (Nat.succ_pos V)) (Nat.pow_pos hq)

private theorem logb_residual_nat_deg {q K V w r : ℕ} (hq : 1 < q) (hK : 0 < K) :
    Real.logb q ((K ^ 3 * (V + 1) * q ^ (w + 3 * r + 2) : ℕ) : ℝ) =
      (w : ℝ) + ((3 * r + 2 : ℕ) : ℝ) + 3 * Real.logb q K + Real.logb q ((V : ℝ) + 1) := by
  rw [logb_residual_nat hq hK]
  push_cast
  ring

private theorem agreement_le_of_div_le {a half_b R qn μ' μ l2 n : ℝ}
    (hag : a ≤ half_b + R / qn) (hexp : R / qn ≤ Real.exp (-(μ' * l2 * n)))
    (hmono : Real.exp (-(μ' * l2 * n)) ≤ Real.exp (-(μ * l2 * n))) :
    a ≤ half_b + Real.exp (-((μ * l2) * n)) := by
  linarith

private theorem mul_le_of_norm_le {c x δ C : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 ≤ x)
    (hC : 0 < C) (hn : ‖x‖ ≤ δ / (C * c) * ‖(n : ℝ)‖) :
    c * x ≤ (δ / C) * n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, abs_of_nonneg hx, Real.norm_eq_abs, abs_of_nonneg hn0] at hn
  have hmul := mul_le_mul_of_nonneg_left hn hc.le
  have hcancel : c * (δ / (C * c) * n) = (δ / C) * n := by field_simp
  linarith

private theorem logb_node_err_le {q V L₀ δ C : ℝ} {n : ℕ}
    (hq2 : 2 ≤ q) (hV0 : 0 ≤ V) (hC : 0 < C) (hV : V ≤ L₀ * n + 1)
    (hnlogV : ‖Real.log (L₀ * n + 2)‖ ≤ δ / (C * (4 + 1 / Real.log 2)) * ‖(n : ℝ)‖) :
    Real.logb q (V + 1) ≤ (δ / C) * n := by
  have hln_nn : 0 ≤ Real.log (L₀ * n + 2) := Real.log_nonneg (by linarith)
  have hbound := mul_le_of_norm_le (by positivity : (0 : ℝ) < 4 + 1 / Real.log 2) hln_nn
    hC hnlogV
  calc Real.logb q (V + 1)
      ≤ (4 + 1 / Real.log 2) * Real.log (V + 1) := logb_le_mul_log hq2 (by linarith)
    _ ≤ (4 + 1 / Real.log 2) * Real.log (L₀ * n + 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
          (by positivity)
    _ ≤ (δ / C) * n := hbound

private theorem supply_eight_le {n δ a p W C_deg L_K L_V S_str gs U_un E1 E2 : ℝ}
    (hδn : 0 ≤ δ * n)
    (hπ : W ≤ S_str + E1 + E2)
    (hstr : S_str ≤ (1 - a) * n + gs + a * U_un + p)
    (hgs : gs ≤ a * n - δ * n)
    (hd : a * U_un ≤ a * L_K)
    (hE1 : E1 ≤ (δ / 8) * n)
    (hE2 : E2 ≤ (δ / 8) * n)
    (hK : (3 + a) * L_K ≤ (δ / 8) * n)
    (hV : L_V ≤ (δ / 8) * n)
    (hc : C_deg + p ≤ (δ / 8) * n) :
    W + C_deg + 3 * L_K + L_V ≤ (1 - δ / 4) * n := by
  calc W + C_deg + 3 * L_K + L_V
      ≤ (S_str + E1 + E2) + C_deg + 3 * L_K + L_V := by linarith
    _ ≤ (((1 - a) * n + gs + a * U_un + p) + E1 + E2) + C_deg + 3 * L_K + L_V := by linarith
    _ = n + (gs - a * n) + a * U_un + 3 * L_K + E1 + E2 + L_V + (C_deg + p) := by ring
    _ ≤ n + (-(δ * n)) + a * L_K + 3 * L_K + (δ / 8) * n + (δ / 8) * n +
          (δ / 8) * n + (δ / 8) * n := by linarith
    _ = n - 4 * ((δ / 8) * n) + (3 + a) * L_K := by ring
    _ ≤ n - 4 * ((δ / 8) * n) + (δ / 8) * n := by linarith
    _ = (1 - δ / 4) * n - (δ * n) / 8 := by ring
    _ ≤ (1 - δ / 4) * n := by linarith

private theorem supply_ten_le {n δ a p W C_deg L_K L_V S_str gs U_un E0 E1 E2 : ℝ}
    (hδn : 0 ≤ δ * n)
    (hπ : W ≤ S_str + E0 + E1 + E2)
    (hstr : S_str ≤ (1 - a) * n + gs + a * U_un + p)
    (hgs : gs ≤ a * n - δ * n)
    (hd : a * U_un ≤ a * L_K)
    (hE0 : E0 ≤ (δ / 10) * n)
    (hE1 : E1 ≤ (δ / 10) * n)
    (hE2 : E2 ≤ (δ / 10) * n)
    (hK : (3 + a) * L_K ≤ (δ / 10) * n)
    (hV : L_V ≤ (δ / 10) * n)
    (hc : C_deg + p ≤ (δ / 10) * n) :
    W + C_deg + 3 * L_K + L_V ≤ (1 - δ / 5) * n := by
  calc W + C_deg + 3 * L_K + L_V
      ≤ (S_str + E0 + E1 + E2) + C_deg + 3 * L_K + L_V := by linarith
    _ ≤ (((1 - a) * n + gs + a * U_un + p) + E0 + E1 + E2) + C_deg + 3 * L_K + L_V := by
          linarith
    _ = n + (gs - a * n) + a * U_un + 3 * L_K + E0 + E1 + E2 + L_V + (C_deg + p) := by ring
    _ ≤ n + (-(δ * n)) + a * L_K + 3 * L_K + (δ / 10) * n + (δ / 10) * n +
          (δ / 10) * n + (δ / 10) * n + (δ / 10) * n := by linarith
    _ = n - 5 * ((δ / 10) * n) + (3 + a) * L_K := by ring
    _ ≤ n - 5 * ((δ / 10) * n) + (δ / 10) * n := by linarith
    _ = (1 - δ / 5) * n - (δ * n) / 5 := by ring
    _ ≤ (1 - δ / 5) * n := by linarith

private theorem contra_of_logb_eight {n δ L_S B : ℝ} (hδn : 0 < δ * n)
    (hdef : n - L_S ≤ (δ / 8) * n) (hdem : L_S ≤ B) (hB : B ≤ (1 - δ / 4) * n) : False := by
  have h1 : n ≤ n - (δ * n) / 8 := by
    calc n = (n - L_S) + L_S := by ring
      _ ≤ (δ / 8) * n + (1 - δ / 4) * n := add_le_add hdef (hdem.trans hB)
      _ = n - (δ * n) / 8 := by ring
  linarith

private theorem contra_of_logb_ten {n δ L_S B : ℝ} (hδn : 0 < δ * n)
    (hdef : n - L_S ≤ (δ / 10) * n) (hdem : L_S ≤ B) (hB : B ≤ (1 - δ / 5) * n) : False := by
  have h1 : n ≤ n - (δ * n) / 10 := by
    calc n = (n - L_S) + L_S := by ring
      _ ≤ (δ / 10) * n + (1 - δ / 5) * n := add_le_add hdef (hdem.trans hB)
      _ = n - (δ * n) / 10 := by ring
  linarith

private theorem contra_of_nondet_eight {n δ L_S W C_deg L_K L_V S_str E1 E2 : ℝ}
    (hδn : 0 < δ * n)
    (hdef : n - L_S ≤ (δ / 8) * n)
    (hdem : L_S ≤ W + C_deg + 3 * L_K + L_V)
    (hπ : W ≤ S_str + E1 + E2)
    (hstr : S_str ≤ (1 - δ) * n + 1 / 4)
    (hE1 : E1 ≤ (δ / 8) * n)
    (hE2 : E2 ≤ (δ / 8) * n)
    (hK : 3 * L_K ≤ (δ / 8) * n)
    (hV : L_V ≤ (δ / 8) * n)
    (hc : C_deg + 1 / 4 ≤ (δ / 8) * n) : False := by
  have h1 : n ≤ n - (δ * n) / 4 := by
    calc n = (n - L_S) + L_S := by ring
      _ ≤ (δ / 8) * n + (W + C_deg + 3 * L_K + L_V) := add_le_add hdef hdem
      _ ≤ (δ / 8) * n + ((S_str + E1 + E2) + C_deg + 3 * L_K + L_V) := by linarith
      _ ≤ (δ / 8) * n + (((1 - δ) * n + 1 / 4 + E1 + E2) + C_deg + 3 * L_K + L_V) := by linarith
      _ = n - δ * n + E1 + E2 + 3 * L_K + L_V + (C_deg + 1 / 4) + (δ / 8) * n := by ring
      _ ≤ n - δ * n + (δ / 8) * n + (δ / 8) * n + (δ / 8) * n + (δ / 8) * n +
            (δ / 8) * n + (δ / 8) * n := by linarith
      _ = n - (δ * n) / 4 := by ring
  linarith

/-- Shared eventual Steiner layout-supply bound for fan-in at most `r`: under
`(c.innerSize : ℝ) ≤ (gateSweepCoefficient r k₀ - ε) * n` and fewer than `K_fn n` assignments to
unreachable inputs, some node layout `π` has total Steiner log-supply at most `(1 - δ / 4) * n`
where `δ = (r + 2 ^ k₀ - k₀ - 1) * ε / 2 ^ k₀`. -/
private theorem eventually_exists_layout_signalWidth_le_gateSweep {U : Type u}
    [Finite U] [Nontrivial U] {r : ℕ} (hr : 2 ≤ r) (k₀ : ℕ) {K_fn : ℕ → ℕ}
    (hK_pos : ∀ᶠ n in atTop, 1 ≤ K_fn n)
    (hlogK : (fun n => Real.logb (Nat.card U) (K_fn n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    let δ := ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) * ε / (2 : ℝ) ^ k₀
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ n 1),
      c.FanInAtMost r →
      (c.innerSize : ℝ) ≤ (gateSweepCoefficient r k₀ - ε) * n →
      Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K_fn n →
      ∃ π : Layout (Compiler.Node c),
        (Compiler.signalWidth c π : ℝ) + ((3 * r + 2 : ℕ) : ℝ) +
          3 * Real.logb (Nat.card U) (K_fn n) +
          Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ≤
            (1 - δ / 4) * n := by
  intro δ
  let q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card : 1 < q)
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_pos : 0 < D_r := by
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set L₀ := gateSweepCoefficient r k₀
  have hL₀_pos : 0 < L₀ := gateSweepCoefficient_pos (by omega) k₀
  have hDr_L₀ : (D_r / (2 : ℝ) ^ k₀) * L₀ = (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀ := by
    have hL_def : L₀ = (k₀ + 2 : ℝ) / D_r := rfl
    rw [hL_def]
    field_simp [hDr_pos.ne']
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨M, hM1, hM_lb⟩ := exists_nat_pos_mul_ge (A := 8 * (r + 1 : ℝ) * (L₀ + 1)) hδ
  obtain ⟨N_c, _, hNc_lb⟩ := exists_nat_pos_mul_ge (A := 8 * ((3 * r + 3 : ℕ) : ℝ)) hδ
  obtain ⟨N_sq, _, hNsq_lb⟩ := exists_nat_pos_mul_ge
    (A := ((r + 1 : ℝ) * √((M : ℝ) * (L₀ + 1))) ^ 2)
    (mul_pos (by positivity : 0 < δ / 8) (by positivity : 0 < δ / 8))
  have hlogV := isLittleO_log_affine (α := L₀) (β := 2) hL₀_pos.le (by norm_num)
  filter_upwards [hK_pos,
    hlogK.bound (show 0 < δ / (8 * (3 + (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀)) by positivity),
    hlogV.bound (show 0 < δ / (8 * (4 + 1 / Real.log 2)) by positivity),
    eventually_ge_atTop 1,
    eventually_ge_atTop N_c,
    eventually_ge_atTop N_sq] with
    n hKn1 hnK hnlogV hn1 hnC hn_sqrt σ c hfan hsize hunread
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_le c hfan hM1
  refine ⟨π, ?_⟩
  let V := Nat.card (Compiler.Node c)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs_L₀ : (c.innerSize : ℝ) ≤ L₀ * n := by
    have : 0 ≤ ε * n := by positivity
    linarith
  have hnode_le : (V : ℝ) ≤ L₀ * n + 1 := by
    have hnat : (V : ℝ) ≤ c.innerSize + 1 := by exact_mod_cast Compiler.card_node_le c
    linarith
  have hnode_mul : (V : ℝ) ≤ (L₀ + 1) * n := by linarith
  have hd_un_le : ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ) ≤
      Real.logb q (K_fn n) := by
    have hpow : (q : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard ≤ K_fn n := by
      exact_mod_cast hunread.le
    calc ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ)
        = Real.logb q ((q : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :=
          (Real.logb_self_pow (by linarith) hq.ne' _).symm
      _ ≤ Real.logb q (K_fn n) := Real.logb_le_logb_of_le hq (by positivity) hpow
  have hstr := sum_straddle_le_of_tangent (by omega : 1 ≤ r) k₀ c hfan
  have hs_term :
      (D_r / (2 : ℝ) ^ k₀) * c.innerSize ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n - δ * n := by
    have h1 := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ D_r / (2 : ℝ) ^ k₀)
    have hexp : (D_r / (2 : ℝ) ^ k₀) * ((L₀ - ε) * n) =
        ((D_r / (2 : ℝ) ^ k₀) * L₀) * n - δ * n := by
      dsimp only [δ, D_r]
      ring
    rwa [hexp, hDr_L₀] at h1
  have hM_term : ((r + 1) * V : ℝ) / M ≤ (δ / 8) * n := by
    have hM_pos : (0 : ℝ) < M := by positivity
    rw [div_le_iff₀ hM_pos]
    have h2 : ((r + 1) * V : ℝ) ≤ (r + 1 : ℝ) * ((L₀ + 1) * n) :=
      mul_le_mul_of_nonneg_left hnode_mul (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hM_lb hn0]
  have hsqrt_term : (r + 1 : ℝ) * √((M * V : ℝ)) ≤ (δ / 8) * n :=
    mul_sqrt_le_of_sq_le (by positivity) (Nat.cast_nonneg M) (by positivity) (by positivity)
      hnode_mul hNsq_lb hn_sqrt
  have hK_err : (3 + (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * Real.logb q (K_fn n) ≤ (δ / 8) * n :=
    mul_le_of_norm_le (by positivity) (Real.logb_nonneg hq (by exact_mod_cast hKn1))
      (by norm_num) hnK
  have hlogV_err : Real.logb q (V + 1) ≤ (δ / 8) * n :=
    logb_node_err_le hq2 (Nat.cast_nonneg _) (by norm_num) hnode_le hnlogV
  have hconst_err : ((3 * r + 2 : ℕ) : ℝ) + 1 / (2 : ℝ) ^ k₀ ≤ (δ / 8) * n := by
    have hp1 : 1 / (2 : ℝ) ^ k₀ ≤ 1 := div_le_one_of_le₀
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by positivity)
    have hNc_n : (N_c : ℝ) ≤ n := by exact_mod_cast hnC
    have hC2 : 8 * ((3 * r + 3 : ℕ) : ℝ) ≤ δ * n :=
      hNc_lb.trans (mul_le_mul_of_nonneg_left hNc_n hδ.le)
    have hcast : ((3 * r + 3 : ℕ) : ℝ) = ((3 * r + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    linarith
  have hd_term :
      ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * Real.logb q (K_fn n) :=
    mul_le_mul_of_nonneg_left hd_un_le (by positivity)
  rw [Nat.cast_one] at hstr
  exact supply_eight_le (mul_nonneg hδ.le hn0) hπ hstr hs_term hd_term hM_term hsqrt_term
    hK_err hlogV_err hconst_err

/-! ### Family 1: Bounded-fan-in worst-case lower bounds (`Ω(log r)`) -/

section Family1

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **Family 1 — Hyperedge gate-sweep lower bound for fan-in at most `r`.** For every `r ≥ 2`,
`k₀ : ℕ`, and `ε > 0`, circuits of fan-in at most `r` deciding dense rectangle-free sets `S_n` have
`c.innerSize > (gateSweepCoefficient r k₀ - ε) n` for all large `n`. -/
theorem eventually_gateSweep_lt_innerSize {r : ℕ} (hr : 2 ≤ r) (k₀ : ℕ)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (gateSweepCoefficient r k₀ - ε) * n < c.innerSize := by
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_pos : 0 < D_r := by
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set δ := D_r * ε / (2 : ℝ) ^ k₀
  have hδ : 0 < δ := by positivity
  have hK_pos : ∀ᶠ n in atTop, 1 ≤ K n := hSK.eventually_rectangleFree.mono fun _ h => h.pos
  have hlogK := isLittleO_logb_of_log hSK.isLittleO_log (Nat.card U)
  have hdef := isLittleO_sub_logb_ncard hSK.isLittleO_deficit
  filter_upwards [eventually_exists_layout_signalWidth_le_gateSweep.{u, v} hr k₀ hK_pos hlogK hε,
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    hdef.bound (show 0 < δ / 8 by positivity), eventually_ge_atTop 1] with
    n hsupply hfree hbig hndef hn1 σ I Acc c hfan hdec
  by_contra! hsize
  obtain ⟨_, hunread⟩ :=
    logb_ncard_le_signalWidth I Acc c hr hfan hdec hfree hbig (Finite.equivFin (Compiler.Node c))
  obtain ⟨π, hB⟩ := hsupply σ c hfan hsize hunread
  obtain ⟨hdem, _⟩ := logb_ncard_le_signalWidth I Acc c hr hfan hdec hfree hbig π
  have hdef_err : (n : ℝ) - Real.logb (Nat.card U) (S n).ncard ≤ (δ / 8) * n := by
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hndef
    exact (le_abs_self _).trans hndef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact contra_of_logb_eight (mul_pos hδ (by linarith)) hdef_err hdem hB

/-- Scaled `(r - 1) * c.innerSize` form of `eventually_gateSweep_lt_innerSize`. -/
theorem eventually_gateSweep_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r) (k₀ : ℕ)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ((r - 1 : ℝ) * gateSweepCoefficient r k₀ - ε) * n < (r - 1) * c.innerSize := by
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  filter_upwards [eventually_gateSweep_lt_innerSize.{u, v} hr k₀ hSK
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)] with n hn σ I Acc c hfan hdec
  have hlt := mul_lt_mul_of_pos_left (hn σ I Acc c hfan hdec) hr1_pos
  have hid : (r - 1 : ℝ) * ((gateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) * n) =
      ((r - 1 : ℝ) * gateSweepCoefficient r k₀ - ε) * n := by
    field_simp
  rwa [hid] at hlt

/-- **Explicit `Ω(log r)` bounded-fan-in lower bound.** For every `r ≥ 2` and `ε > 0`, circuits of
fan-in at most `r` deciding dense rectangle-free sets `S_n ⊆ U^n` satisfy
`(r - 1) * c.innerSize > (log₂ r - log₂ log₂ r - 1 - ε) n` for all large `n`. -/
theorem eventually_log_sub_log_log_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨k₀, hk₀⟩ := exists_log_sub_log_log_le_mul_gateSweepCoefficient hr
  filter_upwards [eventually_gateSweep_lt_mul_innerSize.{u, v} hr k₀ hSK hε] with
    n hn σ I Acc c hfan hdec
  have hle : (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - ε) * n ≤
      ((r - 1 : ℝ) * gateSweepCoefficient r k₀ - ε) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  exact hle.trans_lt (hn σ I Acc c hfan hdec)

/-- At fan-in `r = 8` (`k₀ = 2`), `7 * c.innerSize > (28 / 9 - ε) n` (`28 / 9 ≈ 3.1111`). -/
theorem eventually_twenty_eight_div_nine_lt_seven_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 8 → c.Decides I Acc (S n) →
        (28 / 9 - ε) * n < 7 * c.innerSize := by
  filter_upwards [eventually_gateSweep_lt_mul_innerSize.{u, v} (r := 8) (by decide) 2 hSK hε] with
    n hn σ I Acc c hfan hdec
  have h := hn σ I Acc c hfan hdec
  have hval : ((8 : ℕ) - 1 : ℝ) * gateSweepCoefficient 8 2 = 28 / 9 := by
    unfold gateSweepCoefficient
    norm_num
  rw [hval] at h
  have h7 : ((8 : ℕ) - 1 : ℝ) * c.innerSize = 7 * c.innerSize := by norm_num
  rwa [h7] at h

/-- At fan-in `r = 40` (`k₀ = 4`), `39 * c.innerSize > (78 / 17 - ε) n` (`78 / 17 ≈ 4.5882`,
surpassing `4.57597`). -/
theorem eventually_seventy_eight_div_seventeen_lt_thirty_nine_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 40 → c.Decides I Acc (S n) →
        (78 / 17 - ε) * n < 39 * c.innerSize := by
  filter_upwards [eventually_gateSweep_lt_mul_innerSize.{u, v} (r := 40) (by decide) 4 hSK hε] with
    n hn σ I Acc c hfan hdec
  have h := hn σ I Acc c hfan hdec
  have hval : ((40 : ℕ) - 1 : ℝ) * gateSweepCoefficient 40 4 = 78 / 17 := by
    unfold gateSweepCoefficient
    norm_num
  rw [hval] at h
  have h39 : ((40 : ℕ) - 1 : ℝ) * c.innerSize = 39 * c.innerSize := by norm_num
  rwa [h39] at h

/-- At fan-in `r = 64` (`k₀ = 4`), `63 * c.innerSize > (126 / 25 - ε) n` (`5.04 n`). -/
theorem eventually_one_hundred_twenty_six_div_twenty_five_lt_sixty_three_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 64 → c.Decides I Acc (S n) →
        (126 / 25 - ε) * n < 63 * c.innerSize := by
  filter_upwards [eventually_gateSweep_lt_mul_innerSize.{u, v} (r := 64) (by decide) 4 hSK hε] with
    n hn σ I Acc c hfan hdec
  have h := hn σ I Acc c hfan hdec
  have hval : ((64 : ℕ) - 1 : ℝ) * gateSweepCoefficient 64 4 = 126 / 25 := by
    unfold gateSweepCoefficient
    norm_num
  rw [hval] at h
  have h63 : ((64 : ℕ) - 1 : ℝ) * c.innerSize = 63 * c.innerSize := by norm_num
  rwa [h63] at h

end Family1

/-! ### Family 2: Bounded-fan-in average-case lower bounds -/

private theorem rectangleBias_nonneg_of_small {U : Type u} [Finite U] [Nontrivial U] {n K : ℕ}
    {S : Set (Fin n → U)} {b : ℝ} (hS : RectangleBias S K b) (hK : 2 ≤ K)
    (hsmall : 1 + 2 * Real.logb (Nat.card U) K ≤ (1 - 1 / 2) * n) :
    0 ≤ b := by
  refine hS.nonneg ?_
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  exact le_pow_half_of_logb Finite.one_lt_card (zero_lt_two.trans_le hK) hsmall

private theorem agreement_le_of_not_reach_exp {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} (I : Interpretation σ U) (Acc : Set U) {n K : ℕ} (c : Circuit σ n 1)
    {S : Set (Fin n → U)} {b μ : ℝ} (hS : RectangleBias S K b) (hb : 0 ≤ b) (hK2 : 2 ≤ K)
    (hsmall : 1 + 2 * Real.logb (Nat.card U) K ≤ (1 - 1 / 2) * n) (hμ : μ ≤ 1 / 2)
    (hu : K ≤ Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b + Real.exp (-((μ * Real.log 2) * n)) := by
  let q := Nat.card U
  have hq1 : 1 < q := Finite.one_lt_card
  have hq : (1 : ℝ) < q := by exact_mod_cast hq1
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq_pos : 0 < q := Nat.card_pos
  have hlog : Real.logb q ((q * K ^ 2 : ℕ) : ℝ) ≤ (1 - 1 / 2) * n := by
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_self_eq_one hq]
    exact hsmall
  have hexp_step := div_pow_le_exp hq2
    (by exact_mod_cast Nat.mul_pos hq_pos (Nat.pow_pos (zero_lt_two.trans_le hK2)))
    (by norm_num) hlog
  have hmono : Real.exp (-((1 / 2 : ℝ) * Real.log 2 * n)) ≤ Real.exp (-(μ * Real.log 2 * n)) :=
    Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (Real.log_nonneg one_le_two) (Nat.cast_nonneg (α := ℝ) n)])
  have hag := agreement_le_of_not_reach I Acc c hS hb (one_le_two.trans hK2) hu
  exact agreement_le_of_div_le hag hexp_step hmono

private theorem eventually_agreement_le_of_signalWidth_supply {U : Type u}
    [Finite U] [Nontrivial U] {r : ℕ} (hr : 2 ≤ r) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    {P : ∀ {n : ℕ} {σ : Signature.{v}}, Circuit σ n 1 → Prop}
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hsupply : ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ n 1),
      c.FanInAtMost r → P c →
      Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < max (K n) 2 →
      ∃ π : Layout (Compiler.Node c),
        (Compiler.signalWidth c π : ℝ) + ((3 * r + 2 : ℕ) : ℝ) +
          3 * Real.logb (Nat.card U) (max (K n) 2 : ℕ) +
          Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ≤ (1 - μ₀) * n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → P c →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + b n + Real.exp (-((min μ₀ (1 / 2) * Real.log 2) * n)) := by
  let q := Nat.card U
  have hq1 : 1 < q := Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  let K' : ℕ → ℕ := fun n => max (K n) 2
  have hlogK' := isLittleO_logb_max_two hK q
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 + 2 * Real.logb q (K' n) ≤ (1 - 1 / 2) * n := by
    filter_upwards [((isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop.add
      (hlogK'.const_mul_left 2)).bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [Real.norm_eq_abs, id, Nat.abs_cast] at hn
    linarith [le_abs_self (1 + 2 * Real.logb q (K' n))]
  filter_upwards [hbias, hsmall, hsupply] with n hbiasn hsmalln hsup σ I Acc c hfan hPc
  have hK2 : 2 ≤ K' n := le_max_right _ _
  have hS : RectangleBias (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  have hb : 0 ≤ b n := rectangleBias_nonneg_of_small hS hK2 hsmalln
  by_cases hu : K' n ≤ q ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard
  · exact agreement_le_of_not_reach_exp I Acc c hS hb hK2 hsmalln (min_le_right _ _) hu
  · push Not at hu
    have hmono : Real.exp (-(μ₀ * Real.log 2 * n)) ≤
        Real.exp (-(min μ₀ (1 / 2) * Real.log 2 * n)) :=
      Real.exp_le_exp.mpr (by
        have : min μ₀ (1 / 2) ≤ μ₀ := min_le_left _ _
        nlinarith [mul_nonneg (Real.log_nonneg one_le_two) (Nat.cast_nonneg (α := ℝ) n)])
    obtain ⟨π, hB⟩ := hsup σ c hfan hPc hu
    have hlog_res :
        Real.logb q ((K' n ^ 3 * (Nat.card (Compiler.Node c) + 1) *
            q ^ (Compiler.signalWidth c π + 3 * r + 2) : ℕ) : ℝ) ≤ (1 - μ₀) * n :=
      (logb_residual_nat_deg (r := r) hq1 (zero_lt_two.trans_le hK2)).trans_le hB
    have hexp_step := div_pow_le_exp hq2
      (residual_nat_pos Nat.card_pos (zero_lt_two.trans_le hK2)) hμ₀.le hlog_res
    have hag := agreement_le_of_signalWidth I Acc c hr hS hb hfan hu π
    exact agreement_le_of_div_le hag hexp_step hmono

section Family2

/-- **Family 2 — Hyperedge gate-sweep average-case bound.** For every `r ≥ 2`, `k₀ : ℕ`, and
`ε > 0`, there is `γ > 0` (uniform over the alphabet `U` and problem family) such that below
`(gateSweepCoefficient r k₀ - ε) n` inner gates, every circuit of fan-in at most `r` agrees with a
`RectangleBias` set on at most `1 / 2 + b n + exp (-γ n)` of inputs. -/
theorem exists_eventually_agreement_le_gateSweep {r : ℕ} (hr : 2 ≤ r) (k₀ : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost r →
          (c.innerSize : ℝ) ≤ (gateSweepCoefficient r k₀ - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_pos : 0 < D_r := by
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  set δ := D_r * ε / (2 : ℝ) ^ k₀
  have hδ : 0 < δ := by positivity
  have hμ : 0 < min (δ / 4) (1 / 2) := lt_min (by positivity) (by norm_num)
  refine ⟨min (δ / 4) (1 / 2) * Real.log 2, by positivity, fun U _ _ S K b hbias hK => ?_⟩
  exact eventually_agreement_le_of_signalWidth_supply.{u, v} hr (by positivity) hbias hK
    (eventually_exists_layout_signalWidth_le_gateSweep.{u, v} hr k₀
      (Eventually.of_forall fun _ => one_le_two.trans (le_max_right _ _))
      (isLittleO_logb_max_two hK (Nat.card U)) hε)

/-- **Explicit `Ω(log r)` average-case lower bound.** Below
`(log₂ r - log₂ log₂ r - 1 - ε) n` in `(r - 1) * c.innerSize`, agreement with any `RectangleBias`
family is at most `1 / 2 + b n + exp (-γ n)`. -/
theorem exists_eventually_agreement_le_log {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  obtain ⟨k₀, hk₀⟩ := exists_log_sub_log_log_le_mul_gateSweepCoefficient hr
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  obtain ⟨γ, hγ, H⟩ := exists_eventually_agreement_le_gateSweep.{u, v} hr k₀
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)
  refine ⟨γ, hγ, fun U _ _ S K b hbias hK => ?_⟩
  filter_upwards [H U S K b hbias hK] with n hn σ I Acc c hfan hsize
  refine hn σ I Acc c hfan ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul : (r - 1 : ℝ) * c.innerSize ≤
      (r - 1 : ℝ) * ((gateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) * n) := by
    have hsub :
        Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - ε ≤
          (r - 1 : ℝ) * (gateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) := by
      have hid : (r - 1 : ℝ) * (ε / (r - 1 : ℝ)) = ε := mul_div_cancel₀ ε hr1_pos.ne'
      linarith
    exact hsize.trans ((mul_le_mul_of_nonneg_right hsub hn0).trans_eq (mul_assoc _ _ _))
  exact le_of_mul_le_mul_left hmul hr1_pos

end Family2

/-! ### Family 3: Low-reuse circuit lower bounds at fan-in two -/

section Family3

/-- Shared eventual Steiner layout-supply bound at fan-in two charging multi-fanout inner gates:
under `(c.innerSize : ℝ) + (2 ^ k₀ - k₀) * multiFanoutSize c ≤ (k₀ + 2 - ε) * n` and fewer than
`K_fn n` assignments to unreachable inputs, some node layout `π` has total Steiner log-supply at
most `(1 - δ / 5) * n` where `δ = ε / 2 ^ k₀`. -/
private theorem eventually_exists_layout_signalWidth_le_multiFanoutSize {U : Type u}
    [Finite U] [Nontrivial U] {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {K_fn : ℕ → ℕ}
    (hK_pos : ∀ᶠ n in atTop, 1 ≤ K_fn n)
    (hlogK : (fun n => Real.logb (Nat.card U) (K_fn n)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    let δ := ε / (2 : ℝ) ^ k₀
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ n 1),
      c.FanInAtMost 2 →
      (c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c ≤
        ((k₀ + 2 : ℝ) - ε) * n →
      Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K_fn n →
      ∃ π : Layout (Compiler.Node c),
        (Compiler.signalWidth c π : ℝ) + ((3 * 2 + 2 : ℕ) : ℝ) +
          3 * Real.logb (Nat.card U) (K_fn n) +
          Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ≤
            (1 - δ / 5) * n := by
  intro δ
  let q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card : 1 < q)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let K_lin : ℝ := (k₀ + 3 : ℝ)
  obtain ⟨B, _, hB_lb⟩ := exists_nat_pos_mul_ge (A := 10 * K_lin) (mul_pos two_pos hδ)
  obtain ⟨M, hM1, hM_lb⟩ := exists_nat_pos_mul_ge (A := 30 * K_lin) hδ
  obtain ⟨N_c, _, hNc_lb⟩ := exists_nat_pos_mul_ge (A := 90) hδ
  obtain ⟨N_sq, _, hNsq_lb⟩ := exists_nat_pos_mul_ge
    (A := (3 * √((M : ℝ) * (2 * (B : ℝ) + 1) * K_lin)) ^ 2)
    (mul_pos (by positivity : 0 < δ / 10) (by positivity : 0 < δ / 10))
  have hlogV := isLittleO_log_affine (α := k₀ + 2) (β := 2) (by positivity) (by norm_num)
  filter_upwards [hK_pos,
    hlogK.bound (show 0 < δ / (10 * (3 + (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀)) by positivity),
    hlogV.bound (show 0 < δ / (10 * (4 + 1 / Real.log 2)) by positivity),
    eventually_ge_atTop 1,
    eventually_ge_atTop N_c,
    eventually_ge_atTop N_sq] with
    n hKn1 hnK hnlogV hn1 hnC hn_sqrt σ c hfan hsize hunread
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_reuse_le c hfan B hM1
  refine ⟨π, ?_⟩
  let V := Nat.card (Compiler.Node c)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h2k_ge : (0 : ℝ) ≤ (2 : ℝ) ^ k₀ - k₀ := by
    have hnat : k₀ + 1 ≤ 2 ^ k₀ := Nat.succ_le_of_lt k₀.lt_two_pow_self
    have hr : (k₀ + 1 : ℝ) ≤ (2 : ℝ) ^ k₀ := by exact_mod_cast hnat
    linarith
  have hs_le : (c.innerSize : ℝ) ≤ (k₀ + 2 : ℝ) * n := by
    have hmf_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c :=
      mul_nonneg h2k_ge (Nat.cast_nonneg _)
    have hεn : 0 ≤ ε * n := by positivity
    linarith
  have hnode_le : (V : ℝ) ≤ (k₀ + 2 : ℝ) * n + 1 := by
    have hnat : (V : ℝ) ≤ c.innerSize + 1 := by exact_mod_cast Compiler.card_node_le c
    linarith
  have hnode_Klin : (V : ℝ) ≤ K_lin * n := by dsimp only [K_lin]; linarith
  have hd_un_le : ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ) ≤
      Real.logb q (K_fn n) := by
    have hpow : (q : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard ≤ K_fn n := by
      exact_mod_cast hunread.le
    calc ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ)
        = Real.logb q ((q : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :=
          (Real.logb_self_pow (by linarith) hq.ne' _).symm
      _ ≤ Real.logb q (K_fn n) := Real.logb_le_logb_of_le hq (by positivity) hpow
  have hstr := sum_nonUnit_straddle_le_of_tangent hk₀ c hfan
  have hs_term :
      ((c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c) / (2 : ℝ) ^ k₀ ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n - δ * n := by
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
    have h1 := div_le_div_of_nonneg_right hsize hpos2.le
    have h2 : (((k₀ + 2 : ℝ) - ε) * n) / (2 : ℝ) ^ k₀ =
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n - δ * n := by
      dsimp only [δ]
      ring
    rwa [h2] at h1
  have hB_term : (V : ℝ) / (2 * (B + 1)) ≤ (δ / 10) * n := by
    have hB_pos : (0 : ℝ) < 2 * (B + 1) := by positivity
    rw [div_le_iff₀ hB_pos]
    nlinarith [mul_le_mul_of_nonneg_right hB_lb hn0]
  have hM_term : (3 * V : ℝ) / M ≤ (δ / 10) * n := by
    have hM_pos : (0 : ℝ) < M := by positivity
    rw [div_le_iff₀ hM_pos]
    nlinarith [mul_le_mul_of_nonneg_right hM_lb hn0]
  have hsqrt_term :
      3 * √((M * (2 * B + 1) * V : ℝ)) ≤ (δ / 10) * n :=
    mul_sqrt_le_of_sq_le (by norm_num) (by positivity) (by dsimp only [K_lin]; positivity)
      (by positivity) hnode_Klin hNsq_lb hn_sqrt
  have hK_err : (3 + (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * Real.logb q (K_fn n) ≤ (δ / 10) * n :=
    mul_le_of_norm_le (by positivity) (Real.logb_nonneg hq (by exact_mod_cast hKn1))
      (by norm_num) hnK
  have hlogV_err : Real.logb q (V + 1) ≤ (δ / 10) * n :=
    logb_node_err_le hq2 (Nat.cast_nonneg _) (by norm_num) hnode_le hnlogV
  have hconst_err : ((3 * 2 + 2 : ℕ) : ℝ) + 1 / (2 : ℝ) ^ k₀ ≤ (δ / 10) * n := by
    have hp1 : 1 / (2 : ℝ) ^ k₀ ≤ 1 := div_le_one_of_le₀
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by positivity)
    have hNc_n : (N_c : ℝ) ≤ n := by exact_mod_cast hnC
    have hC2 : 90 ≤ δ * n := hNc_lb.trans (mul_le_mul_of_nonneg_left hNc_n hδ.le)
    have h8 : ((3 * 2 + 2 : ℕ) : ℝ) = 8 := by norm_num
    rw [h8]
    linarith
  have hd_term :
      ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * Real.logb q (K_fn n) :=
    mul_le_mul_of_nonneg_left hd_un_le (by positivity)
  rw [Nat.cast_one] at hstr
  exact supply_ten_le (mul_nonneg hδ.le hn0) hπ hstr hs_term hd_term hB_term hM_term hsqrt_term
    hK_err hlogV_err hconst_err

/-- **Family 3 (worst-case) — Low-reuse lower bound at fan-in two.** For every `k₀ ≥ 1` and
`ε > 0`, circuits of fan-in at most two deciding dense rectangle-free sets `S_n ⊆ U^n` satisfy
`c.innerSize + (2 ^ k₀ - k₀) * Compiler.multiFanoutSize c > (k₀ + 2 - ε) n` for all large `n`. -/
theorem eventually_lt_innerSize_add_multiFanoutSize {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        ((k₀ + 2 : ℝ) - ε) * n <
          c.innerSize + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c := by
  set δ := ε / (2 : ℝ) ^ k₀
  have hδ : 0 < δ := by positivity
  have hK_pos : ∀ᶠ n in atTop, 1 ≤ K n := hSK.eventually_rectangleFree.mono fun _ h => h.pos
  have hlogK := isLittleO_logb_of_log hSK.isLittleO_log (Nat.card U)
  have hdef := isLittleO_sub_logb_ncard hSK.isLittleO_deficit
  filter_upwards [
    eventually_exists_layout_signalWidth_le_multiFanoutSize.{u, v} hk₀ hK_pos hlogK hε,
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    hdef.bound (show 0 < δ / 10 by positivity), eventually_ge_atTop 1] with
    n hsupply hfree hbig hndef hn1 σ I Acc c hfan hdec
  by_contra! hsize
  obtain ⟨_, hunread⟩ := logb_ncard_le_signalWidth I Acc c (by decide) hfan hdec hfree hbig
    (Finite.equivFin (Compiler.Node c))
  obtain ⟨π, hB⟩ := hsupply σ c hfan hsize hunread
  obtain ⟨hdem, _⟩ := logb_ncard_le_signalWidth I Acc c (by decide) hfan hdec hfree hbig π
  have hdef_err : (n : ℝ) - Real.logb (Nat.card U) (S n).ncard ≤ (δ / 10) * n := by
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hndef
    exact (le_abs_self _).trans hndef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact contra_of_logb_ten (mul_pos hδ (by linarith)) hdef_err hdem hB

/-- Concrete `k₀ = 4` low-reuse corollary: `c.innerSize + 12 * Compiler.multiFanoutSize c >
(6 - ε) n` (strictly exceeding `4.57597 n` whenever `multiFanoutSize c ≤ 0.1186 n`). -/
theorem eventually_six_sub_lt_innerSize_add_twelve_mul_multiFanoutSize {U : Type u}
    [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (6 - ε) * n < c.innerSize + 12 * Compiler.multiFanoutSize c := by
  filter_upwards [eventually_lt_innerSize_add_multiFanoutSize.{u, v} (k₀ := 4) (by decide)
    hSK hε] with n hn σ I Acc c hfan hdec
  have h := hn σ I Acc c hfan hdec
  have h6 : (((4 : ℕ) + 2 : ℝ) - ε) = 6 - ε := by norm_num
  have h12 : ((2 : ℝ) ^ (4 : ℕ) - (4 : ℕ)) = 12 := by norm_num
  rwa [h6, h12] at h

/-- **Family 3 (average-case) — Low-reuse agreement bound at fan-in two.** Below
`(k₀ + 2 - ε) n` in `c.innerSize + (2 ^ k₀ - k₀) * Compiler.multiFanoutSize c`, agreement with any
`RectangleBias` family is at most `1 / 2 + b n + exp (-γ n)`. -/
theorem exists_eventually_agreement_le_multiFanoutSize {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (U : Type u) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U))
      (K : ℕ → ℕ) (b : ℕ → ℝ), (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
        (c : Circuit σ n 1), c.FanInAtMost 2 →
          (c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c ≤
            ((k₀ + 2 : ℝ) - ε) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  set δ := ε / (2 : ℝ) ^ k₀
  have hδ : 0 < δ := by positivity
  have hμ : 0 < min (δ / 5) (1 / 2) := lt_min (by positivity) (by norm_num)
  refine ⟨min (δ / 5) (1 / 2) * Real.log 2, by positivity, fun U _ _ S K b hbias hK => ?_⟩
  exact eventually_agreement_le_of_signalWidth_supply.{u, v} (by decide) (by positivity) hbias hK
    (eventually_exists_layout_signalWidth_le_multiFanoutSize.{u, v} hk₀
      (Eventually.of_forall fun _ => one_le_two.trans (le_max_right _ _))
      (isLittleO_logb_max_two hK (Nat.card U)) hε)

end Family3

/-! ### Family 4: Nondeterministic bounded-fan-in lower bounds -/

namespace Compiler

/-- **The hidden Steiner network** of a circuit with `n + k` inputs: its post-layout Steiner
constraint network along `π`, with the last `k` witness inputs hidden. -/
noncomputable def hiddenSteinerNetwork {σ : Signature.{v}} {U : Type u} {n k m : ℕ}
    (c : Circuit σ (n + k) m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (π : Layout (Node c)) : Network U (Fin n) (Node c) (SteinerEdge c) :=
  ((steinerNetwork c I Acc π).reindex finSumFinEquiv.symm).hide

@[simp] theorem hiddenSteinerNetwork_toMultigraph {σ : Signature.{v}} {U : Type u} {n k m : ℕ}
    (c : Circuit σ (n + k) m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (π : Layout (Node c)) :
    (hiddenSteinerNetwork c I Acc π).toMultigraph = steinerGraph c π :=
  steinerNetwork_toMultigraph

theorem accepted_hiddenSteinerNetwork {σ : Signature.{v}} {U : Type u} [Nonempty U] {n k m : ℕ}
    (c : Circuit σ (n + k) m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (π : Layout (Node c)) :
    (hiddenSteinerNetwork c I Acc π).accepted =
      {x | ∃ y : Fin k → U, ∀ o, c.eval I (Fin.append x y) o ∈ Acc o} := by
  ext x
  simp only [hiddenSteinerNetwork, Network.accepted_hide, Network.accepted_reindex,
    accepted_steinerNetwork, mem_ofPred_eq]
  refine exists_congr fun y => ?_
  have happend : Sum.elim x y ∘ finSumFinEquiv.symm = Fin.append x y := by
    rw [← Fin.append_comp_sumElim, Function.comp_assoc]
    exact congrArg (Fin.append x y ∘ ·) finSumFinEquiv.self_comp_symm
  rw [happend]

end Compiler

section Family4

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **Family 4 — Nondeterministic bounded-fan-in lower bound.** For every `r ≥ 2` and `ε > 0`,
nondeterministic circuits of fan-in at most `r` with arbitrary witness count `k : ℕ` deciding dense
rectangle-free sets `S_n ⊆ U^n` satisfy `c.innerSize > (4 / (r + 1) - ε) n` uniformly in `k`. -/
theorem eventually_four_div_lt_innerSize_of_nondeterministicDecides {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (4 / (r + 1 : ℝ) - ε) * n < c.innerSize := by
  let q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card : 1 < q)
  set δ := (r + 1 : ℝ) * ε / 4
  have hδ : 0 < δ := by positivity
  set L₀ : ℝ := 4 / (r + 1 : ℝ)
  have hL₀_pos : 0 < L₀ := by positivity
  obtain ⟨M, hM1, hM_lb⟩ := exists_nat_pos_mul_ge (A := 8 * (r + 1 : ℝ) * (L₀ + 1)) hδ
  obtain ⟨N_c, _, hNc_lb⟩ := exists_nat_pos_mul_ge (A := 8 * ((3 * r + 3 : ℕ) : ℝ)) hδ
  obtain ⟨N_sq, _, hNsq_lb⟩ := exists_nat_pos_mul_ge
    (A := ((r + 1 : ℝ) * √((M : ℝ) * (L₀ + 1))) ^ 2)
    (mul_pos (by positivity : 0 < δ / 8) (by positivity : 0 < δ / 8))
  have hlogK := isLittleO_logb_of_log hSK.isLittleO_log q
  have hdef := isLittleO_sub_logb_ncard hSK.isLittleO_deficit
  have hlogV := isLittleO_log_affine (α := L₀) (β := 2) hL₀_pos.le (by norm_num)
  filter_upwards [hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    hlogK.bound (show 0 < δ / 24 by positivity),
    hdef.bound (show 0 < δ / 8 by positivity),
    hlogV.bound (show 0 < δ / (8 * (4 + 1 / Real.log 2)) by positivity),
    eventually_ge_atTop 1,
    eventually_ge_atTop N_c,
    eventually_ge_atTop N_sq] with
    n hfree hbig hnK hndef hnlogV hn1 hnC hn_sqrt
  intro k σ I Acc c hfan hndec
  by_contra! hsize
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs_L₀ : (c.innerSize : ℝ) ≤ L₀ * n := by
    have : 0 ≤ ε * n := by positivity
    linarith
  have hnode_le : (Nat.card (Compiler.Node c) : ℝ) ≤ L₀ * n + 1 := by
    have hnat : (Nat.card (Compiler.Node c) : ℝ) ≤ c.innerSize + 1 := by
      exact_mod_cast Compiler.card_node_le c
    linarith
  have hnode_mul : (Nat.card (Compiler.Node c) : ℝ) ≤ (L₀ + 1) * n := by linarith
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_le c hfan hM1
  set H := Compiler.hiddenSteinerNetwork c I (fun _ => Acc) π
  have hacc : H.accepted = S n := by
    rw [Compiler.accepted_hiddenSteinerNetwork]
    ext x
    rw [hndec x]
    exact exists_congr fun y => ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have hw : H.width π ≤ Compiler.signalWidth c π := by
    rw [Compiler.hiddenSteinerNetwork_toMultigraph, Compiler.width_steinerGraph_eq]
  have hd : H.MaxDegreeLE (2 * (r + 1)) := by
    rw [Compiler.hiddenSteinerNetwork_toMultigraph]
    exact Compiler.maxDegreeLE_steinerGraph hfan
  have hm : ∀ u : Compiler.Node c, (H.readAt u).ncard ≤ r := fun u =>
    (Network.ncard_readAt_hide_le _ u).trans
      ((Network.ncard_readAt_reindex _ _ u).trans_le
        ((Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega))))
  have hdem := H.logb_ncard_accepted_le (hacc ▸ hfree) (hacc ▸ hbig) π hw hd hm
  rw [hacc] at hdem
  have hstr :
      (∑ w : Compiler.ActiveSignal c,
          (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
        (1 - δ) * n + 1 / 4 := by
    have h4 :
        4 * (∑ w : Compiler.ActiveSignal c,
            (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
          ∑ w : Compiler.ActiveSignal c, ((Compiler.support c w).ncard : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun w _ =>
        Compiler.four_mul_one_sub_two_pow_le (Compiler.support c w).ncard
    have hsupp :
        (∑ w : Compiler.ActiveSignal c, ((Compiler.support c w).ncard : ℝ)) ≤
          (r + 1 : ℝ) * c.innerSize + 1 := by
      exact_mod_cast Compiler.sum_ncard_support_le hfan
    have hs_mul : (r + 1 : ℝ) * c.innerSize ≤ (4 - 4 * δ) * n := by
      have h1 := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)
      have hid : (r + 1 : ℝ) * ((L₀ - ε) * n) = (4 - 4 * δ) * n := by
        dsimp only [L₀, δ]
        field_simp
      rwa [hid] at h1
    linarith
  have hM_term : ((r + 1) * Nat.card (Compiler.Node c) : ℝ) / M ≤ (δ / 8) * n := by
    have hM_pos : (0 : ℝ) < M := by positivity
    rw [div_le_iff₀ hM_pos]
    have h2 : ((r + 1) * Nat.card (Compiler.Node c) : ℝ) ≤ (r + 1 : ℝ) * ((L₀ + 1) * n) :=
      mul_le_mul_of_nonneg_left hnode_mul (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hM_lb hn0]
  have hsqrt_term : (r + 1 : ℝ) * √((M * Nat.card (Compiler.Node c) : ℝ)) ≤ (δ / 8) * n :=
    mul_sqrt_le_of_sq_le (by positivity) (Nat.cast_nonneg M) (by positivity) (by positivity)
      hnode_mul hNsq_lb hn_sqrt
  have hK_err : 3 * Real.logb q (K n) ≤ (δ / 8) * n := by
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hnK
    have hlogK_nn : 0 ≤ Real.logb q (K n) :=
      Real.logb_nonneg hq (by exact_mod_cast hfree.pos)
    rw [abs_of_nonneg hlogK_nn] at hnK
    linarith
  have hdef_err : (n : ℝ) - Real.logb q (S n).ncard ≤ (δ / 8) * n := by
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hndef
    exact (le_abs_self _).trans hndef
  have hlogV_err : Real.logb q (Nat.card (Compiler.Node c) + 1) ≤ (δ / 8) * n :=
    logb_node_err_le hq2 (Nat.cast_nonneg _) (by norm_num) hnode_le hnlogV
  have hconst_err : ((2 * (r + 1) : ℕ) : ℝ) + r + 1 / 4 ≤ (δ / 8) * n := by
    have hNc_n : (N_c : ℝ) ≤ n := by exact_mod_cast hnC
    have hC2 : 8 * ((3 * r + 3 : ℕ) : ℝ) ≤ δ * n :=
      hNc_lb.trans (mul_le_mul_of_nonneg_left hNc_n hδ.le)
    have hcast : ((3 * r + 3 : ℕ) : ℝ) = ((2 * (r + 1) : ℕ) : ℝ) + r + 1 := by push_cast; ring
    linarith
  have hdem' :
      Real.logb q (S n).ncard ≤
        Compiler.signalWidth c π + (((2 * (r + 1) : ℕ) : ℝ) + r) + 3 * Real.logb q (K n) +
          Real.logb q (Nat.card (Compiler.Node c) + 1) :=
    hdem.trans_eq (by push_cast; ring)
  exact contra_of_nondet_eight (mul_pos hδ (by linarith)) hdef_err hdem' hπ hstr hM_term
    hsqrt_term hK_err hlogV_err hconst_err

/-- Scaled `(r - 1) * c.innerSize` form of
`eventually_four_div_lt_innerSize_of_nondeterministicDecides` (approaching `4 n` as `r → ∞`). -/
theorem eventually_four_mul_div_lt_mul_innerSize_of_nondeterministicDecides {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (4 * (r - 1 : ℝ) / (r + 1 : ℝ) - ε) * n < (r - 1) * c.innerSize := by
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  filter_upwards [eventually_four_div_lt_innerSize_of_nondeterministicDecides.{u, v} hr hSK
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)] with n hn k σ I Acc c hfan hndec
  have hlt := mul_lt_mul_of_pos_left (hn k σ I Acc c hfan hndec) hr1_pos
  have hid : (r - 1 : ℝ) * ((4 / (r + 1 : ℝ) - ε / (r - 1 : ℝ)) * n) =
      (4 * (r - 1 : ℝ) / (r + 1 : ℝ) - ε) * n := by
    field_simp
  rwa [hid] at hlt

end Family4

end Cslib.Circuits.Frontier
