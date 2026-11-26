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

/-- The gate-sweep denominator `r + 2 ^ k₀ - k₀ - 1` is positive for `1 ≤ r`. -/
private theorem gateSweep_denom_pos {r : ℕ} (hr : 1 ≤ r) (k₀ : ℕ) :
    (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
  linarith [quadFormGateSweep_denom_ge r k₀, (by exact_mod_cast hr : (1 : ℝ) ≤ r)]

theorem gateSweepCoefficient_pos {r : ℕ} (hr : 1 ≤ r) (k₀ : ℕ) :
    0 < gateSweepCoefficient r k₀ := by
  unfold gateSweepCoefficient
  exact div_pos (by positivity) (gateSweep_denom_pos hr k₀)

/-- Explicit `Ω(log r)` choice of `k₀` for `gateSweepCoefficient`: for every `r ≥ 2`, some `k₀ : ℕ`
satisfies `log₂ r - log₂ log₂ r - 1 ≤ (r - 1) · gateSweepCoefficient r k₀`. -/
theorem exists_log_sub_log_log_le_mul_gateSweepCoefficient {r : ℕ} (hr : 2 ≤ r) :
    ∃ k₀ : ℕ,
      Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 ≤
        (r - 1 : ℝ) * gateSweepCoefficient r k₀ := by
  rcases lt_or_ge r 4 with hsmall | hr4
  · refine ⟨1, ?_⟩
    obtain rfl | rfl : r = 2 ∨ r = 3 := by omega
    · rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 : ℕ) by norm_num, Real.logb_two_pow, Nat.cast_one,
        Real.logb_one]
      norm_num [gateSweepCoefficient]
    · have hlog3_ge : 1 ≤ Real.logb 2 (3 : ℝ) := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      have hlog3_le : Real.logb 2 (3 : ℝ) ≤ 2 := by
        calc Real.logb 2 (3 : ℝ)
            ≤ Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
          _ = 2 := by rw [Real.logb_two_pow]; norm_num
      norm_num [gateSweepCoefficient]
      linarith [Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hlog3_ge]
  · obtain ⟨k₀, _, hk₀_pow, hlog⟩ := exists_mul_two_pow_le_and_logb_sub_logb_le hr4
    refine ⟨k₀, ?_⟩
    have hk₀_alg : (k₀ : ℝ) ≤ (r - 1 : ℝ) * gateSweepCoefficient r k₀ := by
      unfold gateSweepCoefficient
      rw [mul_div_assoc', le_div_iff₀ (gateSweep_denom_pos (by omega) k₀)]
      have hk₀_pow_r : (k₀ : ℝ) * (2 : ℝ) ^ k₀ ≤ r := by exact_mod_cast hk₀_pow
      have hr4_r : (4 : ℝ) ≤ r := by exact_mod_cast hr4
      nlinarith [sq_nonneg (k₀ : ℝ), Nat.cast_nonneg (α := ℝ) k₀]
    linarith

/-! ### Tangent upper bounds on expected straddle counts -/

private theorem card_activeSignal_eq {σ : Signature.{v}} {n m : ℕ} (c : Circuit σ n m)
    [Fintype (Compiler.ActiveSignal c)] :
    Fintype.card (Compiler.ActiveSignal c) =
      {i : Fin n | Compiler.Reach c (.input i)}.ncard + Nat.card (Compiler.InnerGate c) := by
  classical
  have := Fintype.ofFinite {i : Fin n // Compiler.Reach c (.input i)}
  have := Fintype.ofFinite (Compiler.InnerGate c)
  rw [Fintype.card_congr (Compiler.ActiveSignal.equiv c), Fintype.card_sum,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact congrArg (· + Nat.card (Compiler.InnerGate c))
    (Nat.card_coe_set_eq {i : Fin n | Compiler.Reach c (.input i)})

private theorem sum_straddle_le_of_tangent_on {σ : Signature.{v}} {n m : ℕ} (k₀ : ℕ)
    (c : Circuit σ n m) (S : Finset (Compiler.ActiveSignal c)) {G B gs : ℝ}
    (hcard : (S.card : ℝ) = ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) + G)
    (hsupp : (∑ w ∈ S, ((Compiler.support c w).ncard : ℝ)) ≤ B + m)
    (hgs : (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * G + B / (2 : ℝ) ^ k₀ ≤ gs) :
    (∑ w ∈ S, (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n + gs +
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
        (m : ℝ) / (2 : ℝ) ^ k₀ := by
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hcompl :
      ({i : Fin n | Compiler.Reach c (.input i)}.ncard : ℝ) +
        {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard = n := by
    rw [show {i : Fin n | ¬ Compiler.Reach c (.input i)} =
      {i : Fin n | Compiler.Reach c (.input i)}ᶜ from rfl, ← Nat.cast_add, ncard_add_ncard_compl,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hd_nn : (0 : ℝ) ≤ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard := Nat.cast_nonneg _
  have htan :
      (∑ w ∈ S, (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
        (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * (S.card : ℝ) +
          (∑ w ∈ S, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
    calc (∑ w ∈ S, (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1)))
        ≤ ∑ w ∈ S, ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c w).ncard : ℝ) / (2 : ℝ) ^ k₀) :=
          Finset.sum_le_sum fun w _ => Compiler.one_sub_two_pow_le_tangent k₀
            ((ncard_pos (toFinite _)).mpr (Compiler.support_nonempty w))
      _ = (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * (S.card : ℝ) +
            (∑ w ∈ S, ((Compiler.support c w).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm, ← Finset.sum_div]
  linear_combination htan + div_le_div_of_nonneg_right hsupp hpos2.le + hgs + hd_nn +
    (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * (hcard + hcompl)

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
  refine sum_straddle_le_of_tangent_on k₀ c Finset.univ
    (G := Nat.card (Compiler.InnerGate c))
    (B := (r + 1 : ℝ) * Nat.card (Compiler.InnerGate c))
    (by rw [Finset.card_univ]; exact_mod_cast card_activeSignal_eq c)
    (by exact_mod_cast Compiler.sum_ncard_support_le_card_innerGate hfan) ?_
  have hG_le : (Nat.card (Compiler.InnerGate c) : ℝ) ≤ c.innerSize := by
    exact_mod_cast Compiler.card_innerGate_le (c := c)
  have hDr_nn : (0 : ℝ) ≤ ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀ :=
    div_nonneg (gateSweep_denom_pos hr k₀).le (by positivity)
  calc (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * Nat.card (Compiler.InnerGate c) +
          ((r + 1 : ℝ) * Nat.card (Compiler.InnerGate c)) / (2 : ℝ) ^ k₀
      = (((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀) *
          Nat.card (Compiler.InnerGate c) := by field_simp; ring
    _ ≤ (((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1) / (2 : ℝ) ^ k₀) * c.innerSize :=
        mul_le_mul_of_nonneg_left hG_le hDr_nn

/-- Supporting-line bound on non-unit active signals at fan-in two. -/
private theorem sum_nonUnit_straddle_le_of_tangent {σ : Signature.{v}} {n m : ℕ} (k₀ : ℕ)
    (c : Circuit σ n m) (hfan : c.FanInAtMost 2) [Fintype (Compiler.ActiveSignal c)]
    [DecidablePred (Compiler.IsUnitGateSignal c)] :
    (∑ w : Compiler.ActiveSignal c with ¬ Compiler.IsUnitGateSignal c w,
        (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n +
      ((c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c) / (2 : ℝ) ^ k₀ +
      ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard +
      (m : ℝ) / (2 : ℝ) ^ k₀ := by
  have hcard_unit : (Finset.univ.filter (Compiler.IsUnitGateSignal c)).card =
      {g : Compiler.InnerGate c | g ∉ Compiler.multiFanoutGates c}.ncard := by
    let emb : Compiler.InnerGate c ↪ Compiler.ActiveSignal c :=
      ⟨Compiler.ActiveSignal.gate, fun _ _ h => Compiler.ActiveSignal.gate.inj h⟩
    have himg : emb '' {g : Compiler.InnerGate c | g ∉ Compiler.multiFanoutGates c} =
        (Finset.univ.filter (Compiler.IsUnitGateSignal c) : Set (Compiler.ActiveSignal c)) := by
      ext w
      simp only [mem_image, mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, emb, Compiler.multiFanoutGates]
      refine ⟨?_, fun hw => ?_⟩
      · rintro ⟨g, hg, rfl⟩
        have hp := Compiler.fanout_pos ((.gate g : Compiler.ActiveSignal c).toSignal)
        change Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal) = 1
        omega
      · cases w with
        | input _ _ => exact absurd hw id
        | gate g =>
          change Compiler.fanout c ((.gate g : Compiler.ActiveSignal c).toSignal) = 1 at hw
          exact ⟨g, by omega, rfl⟩
    rw [← ncard_coe_finset, ← himg, ncard_image_of_injective _ emb.injective]
  have hG_split : {g : Compiler.InnerGate c | g ∉ Compiler.multiFanoutGates c}.ncard +
      Compiler.multiFanoutSize c = Nat.card (Compiler.InnerGate c) := by
    rw [show {g : Compiler.InnerGate c | g ∉ Compiler.multiFanoutGates c} =
      (Compiler.multiFanoutGates c)ᶜ from rfl, add_comm, Compiler.multiFanoutSize,
      ncard_add_ncard_compl]
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (Compiler.IsUnitGateSignal c)
  rw [Finset.card_univ, card_activeSignal_eq c, hcard_unit] at htot
  refine sum_straddle_le_of_tangent_on k₀ c _
    (G := Compiler.multiFanoutSize c)
    (B := (c.innerSize : ℝ) + 2 * Compiler.multiFanoutSize c)
    (by exact_mod_cast (show (Finset.univ.filter fun w => ¬ Compiler.IsUnitGateSignal c w).card =
      {i : Fin n | Compiler.Reach c (.input i)}.ncard + Compiler.multiFanoutSize c by omega))
    (by exact_mod_cast ((Compiler.sum_ncard_support_nonUnit_le hfan).trans
      (Nat.add_le_add_right (Nat.add_le_add_right (Compiler.card_innerGate_le (c := c)) _) m)))
    (le_of_eq (by field_simp; ring))

/-! ### Single-circuit Steiner demand and agreement lemmas -/

section SingleCircuit

/-- If a single-output circuit `c` decides `S`, so does `steinerNetwork c I (fun _ => Acc) π`. -/
theorem Compiler.accepted_steinerNetwork_of_decides {U : Type u} {σ : Signature.{v}} {n : ℕ}
    {c : Circuit σ n 1} {I : Interpretation σ U} {Acc : Set U} {S : Set (Fin n → U)}
    (hS : c.Decides I Acc S) {π : Layout (Compiler.Node c)} :
    (Compiler.steinerNetwork c I (fun _ => Acc) π).accepted = S :=
  Compiler.accepted_steinerNetwork_single.trans (Set.ext fun x => (hS x).symm)

private theorem logb_ncard_le_of_steinerGraph {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n n_in m r K : ℕ} {c : Circuit σ n_in m} {S : Set (Fin n → U)}
    {π : Layout (Compiler.Node c)}
    {N : Network U (Fin n) (Compiler.Node c) (Compiler.SteinerEdge c)}
    (hg : N.toMultigraph = Compiler.steinerGraph c π) (hfan : c.FanInAtMost r)
    (hm : ∀ u : Compiler.Node c, (N.readAt u).ncard ≤ r)
    (hacc : N.accepted = S) (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Real.logb (Nat.card U) S.ncard ≤
      Compiler.signalWidth c π + (3 * r + 2 : ℕ) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) := by
  have hw : N.width π ≤ Compiler.signalWidth c π := by rw [hg, Compiler.width_steinerGraph_eq]
  have hd : N.MaxDegreeLE (2 * (r + 1)) := hg ▸ Compiler.maxDegreeLE_steinerGraph hfan
  have hdem := N.logb_ncard_accepted_le (hacc ▸ hfree) (hacc ▸ hbig) π hw hd hm
  rw [hacc] at hdem
  exact hdem.trans_eq (by push_cast; ring)

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
  have hunread := hfree.pow_ncard_compl_lt (hacc ▸ N.dependsOn_read) hbig
  rw [congrArg compl Compiler.read_steinerNetwork] at hunread
  exact ⟨logb_ncard_le_of_steinerGraph Compiler.steinerNetwork_toMultigraph hfan
    (fun u => (Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega)))
    hacc hfree hbig, hunread⟩

/-- **Agreement when many inputs are unreachable.** -/
theorem agreement_le_of_not_reach {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hu : K ≤ Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤
      1 / 2 + b + (Nat.card U * K ^ 2 : ℕ) / (Nat.card U : ℝ) ^ n :=
  agreement_le_of_unread I Acc c hS hb hK
    ((congrArg compl (Compiler.read_network I fun _ => Acc)).symm ▸ hu)

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
      (Compiler.steinerNetwork_toMultigraph ▸ Compiler.maxDegreeLE_steinerGraph hfan)
      (fun u => (Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega)))
  have hread (A : Set U) : (Compiler.steinerNetwork c I (fun _ => A) π).readᶜ =
      {i : Fin n | ¬ Compiler.Reach c (.input i)} :=
    congrArg compl Compiler.read_steinerNetwork
  have hdeg_eq : w + 2 * (r + 1) + r = w + 3 * r + 2 := by omega
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [Compiler.accepted_steinerNetwork_single, hread, hdeg_eq] at h₁
  rw [show (Compiler.steinerNetwork c I (fun _ => Accᶜ) π).accepted =
      {x | c.eval I x 0 ∈ Acc}ᶜ from Compiler.accepted_steinerNetwork_single, hread,
    hdeg_eq] at h₂
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
  rw [show (Nat.card (Fin n → U) : ℝ) = (q : ℝ) ^ n by simp [q, Nat.card_fun]] at h
  refine h.trans ?_
  rw [← two_mul, mul_div_mul_left _ _ two_ne_zero]
  linarith [div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hres)
    (pow_nonneg (Nat.cast_nonneg q) n)]

end SingleCircuit

/-! ### Asymptotic helper bounds for logarithms and residuals -/

private theorem isLittleO_logb_of_log {K : ℕ → ℕ}
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) (q : ℝ) :
    (fun n => Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
  (hK.const_mul_left (1 / Real.log q)).congr_left fun n => by simp only [Real.logb]; ring

private theorem exists_nat_pos_mul_ge {A δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, 1 ≤ M ∧ A ≤ δ * M := by
  refine ⟨⌈A / δ⌉₊ + 1, Nat.le_add_left 1 _,
    mul_comm _ δ ▸ (div_le_iff₀ hδ).mp ((Nat.le_ceil _).trans ?_)⟩
  exact_mod_cast Nat.le_succ _

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

private theorem mul_le_of_norm_le {c x η : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 ≤ x)
    (hn : ‖x‖ ≤ (η / c) * ‖(n : ℝ)‖) :
    c * x ≤ η * n := by
  rw [Real.norm_eq_abs, abs_of_nonneg hx, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n),
    div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm] at hn
  exact hn

private theorem logb_node_err_le {q V L₀ η : ℝ} {n : ℕ}
    (hq2 : 2 ≤ q) (hV0 : 0 ≤ V) (hV : V ≤ L₀ * n + 1)
    (hnlogV : ‖Real.log (L₀ * n + 2)‖ ≤ (η / (4 + 1 / Real.log 2)) * ‖(n : ℝ)‖) :
    Real.logb q (V + 1) ≤ η * n := by
  have hbound := mul_le_of_norm_le (by positivity : (0 : ℝ) < 4 + 1 / Real.log 2)
    (Real.log_nonneg (by linarith)) hnlogV
  calc Real.logb q (V + 1)
      ≤ (4 + 1 / Real.log 2) * Real.log (V + 1) := logb_le_mul_log hq2 (by linarith)
    _ ≤ (4 + 1 / Real.log 2) * Real.log (L₀ * n + 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
          (by positivity)
    _ ≤ η * n := hbound

private theorem ncard_not_reach_le_logb {U : Type u} [Finite U] [Nontrivial U]
    {σ : Signature.{v}} {n m K : ℕ} {c : Circuit σ n m}
    (hunread : Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K) :
    ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ) ≤ Real.logb (Nat.card U) K := by
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hpow : (Nat.card U : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard ≤ K := by
    exact_mod_cast hunread.le
  calc ({i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard : ℝ)
      = Real.logb (Nat.card U)
          ((Nat.card U : ℝ) ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard) :=
        (Real.logb_self_pow (by linarith) hq.ne' _).symm
    _ ≤ Real.logb (Nat.card U) K := Real.logb_le_logb_of_le hq (by positivity) hpow

/-- Unified asymptotic discretization engine bounding bucket, Efron–Stein concentration,
`log_q K`, `log_q (|Node c| + 1)`, and additive degree/output constants by `η * n`. -/
private theorem eventually_signalWidth_err_le {U : Type u} [Finite U] [Nontrivial U]
    (r R : ℕ) {L₀ a C_const η : ℝ} (hL₀ : 0 ≤ L₀) (ha : 0 ≤ a) (hη : 0 < η)
    {K_fn : ℕ → ℕ} (hK_pos : ∀ᶠ n in atTop, 1 ≤ K_fn n)
    (hlogK : (fun n => Real.logb (Nat.card U) (K_fn n)) =o[atTop] fun n => (n : ℝ)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ᶠ n in atTop,
      1 ≤ n ∧
      (3 + a) * Real.logb (Nat.card U) (K_fn n) ≤ η * n ∧
      C_const ≤ η * n ∧
      ∀ {n_in : ℕ} {σ : Signature.{v}} (c : Circuit σ n_in 1),
        (c.innerSize : ℝ) ≤ L₀ * n →
        ((r + 1) * Nat.card (Compiler.Node c) : ℝ) / M ≤ η * n ∧
        (r + 1 : ℝ) * √((M * R * Nat.card (Compiler.Node c) : ℝ)) ≤ η * n ∧
        Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ≤ η * n := by
  let q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card : 1 < q)
  obtain ⟨M, hM1, hM_lb⟩ := exists_nat_pos_mul_ge (A := (r + 1 : ℝ) * (L₀ + 1)) hη
  obtain ⟨N_c, _, hNc_lb⟩ := exists_nat_pos_mul_ge (A := C_const) hη
  obtain ⟨N_sq, _, hNsq_lb⟩ := exists_nat_pos_mul_ge
    (A := ((r + 1 : ℝ) * √(((M * R : ℕ) : ℝ) * (L₀ + 1))) ^ 2) (mul_pos hη hη)
  have hlogV := isLittleO_log_affine (α := L₀) (β := 2) hL₀ (by norm_num)
  refine ⟨M, hM1, ?_⟩
  filter_upwards [hK_pos,
    hlogK.bound (show 0 < η / (3 + a) by positivity),
    hlogV.bound (show 0 < η / (4 + 1 / Real.log 2) by positivity),
    eventually_ge_atTop 1,
    eventually_ge_atTop N_c,
    eventually_ge_atTop N_sq] with n hKn1 hnK hnlogV hn1 hnC hn_sqrt
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  refine ⟨hn1,
    mul_le_of_norm_le (by positivity) (Real.logb_nonneg hq (by exact_mod_cast hKn1)) hnK,
    hNc_lb.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnC) hη.le),
    fun c hs_L₀ => ?_⟩
  let V := Nat.card (Compiler.Node c)
  have hnode_le : (V : ℝ) ≤ L₀ * n + 1 :=
    le_trans (b := (c.innerSize : ℝ) + 1) (by exact_mod_cast Compiler.card_node_le c) (by linarith)
  have hnode_mul : (V : ℝ) ≤ (L₀ + 1) * n := by linarith
  refine ⟨?_, ?_, logb_node_err_le hq2 (Nat.cast_nonneg _) hnode_le hnlogV⟩
  · have hM_pos : (0 : ℝ) < M := by positivity
    rw [div_le_iff₀ hM_pos]
    nlinarith [mul_le_mul_of_nonneg_left hnode_mul (by positivity : (0 : ℝ) ≤ r + 1),
      mul_le_mul_of_nonneg_right hM_lb hn0]
  · simpa only [Nat.cast_mul, mul_assoc] using mul_sqrt_le_of_sq_le (by positivity)
      (Nat.cast_nonneg _) (by positivity) hη hnode_mul hNsq_lb hn_sqrt

private theorem supply_base_le {b n δ a p W C_deg L_K L_V S_str gs U_un E : ℝ}
    (hb : 1 < b)
    (hπ : W ≤ S_str + E)
    (hstr : S_str ≤ (1 - a) * n + gs + a * U_un + p)
    (hgs : gs ≤ a * n - δ * n)
    (hd : a * U_un ≤ a * L_K)
    (hE : E ≤ 3 * (((b - 1) / (6 * b) * δ) * n))
    (hK : (3 + a) * L_K ≤ ((b - 1) / (6 * b) * δ) * n)
    (hV : L_V ≤ ((b - 1) / (6 * b) * δ) * n)
    (hc : C_deg + p ≤ ((b - 1) / (6 * b) * δ) * n) :
    W + C_deg + 3 * L_K + L_V ≤ (1 - δ / b) * n := by
  have hb0 : b ≠ 0 := by linarith
  have hid : ((1 - a) * n + (a * n - δ * n) + a * L_K + p + E) + C_deg + 3 * L_K + L_V =
      (1 - δ / b) * n +
        (E + (3 + a) * L_K + L_V + (C_deg + p) - 6 * (((b - 1) / (6 * b) * δ) * n)) := by
    field_simp
    ring
  linarith

private theorem contra_of_logb_base {b n δ L_S B : ℝ} (hb : 1 < b) (hδn : 0 < δ * n)
    (hdef : n - L_S ≤ (δ / (2 * b)) * n) (hdem : L_S ≤ B) (hB : B ≤ (1 - δ / b) * n) : False := by
  have hb0 : 0 < 2 * b := by linarith
  have h1 : (δ / (2 * b)) * n + (1 - δ / b) * n = n - (δ * n) / (2 * b) := by
    field_simp
    ring
  have hpos : 0 < (δ * n) / (2 * b) := div_pos hδn hb0
  linarith

private theorem eventually_not_decides_of_signalWidth_supply {U : Type u}
    [Finite U] [Nontrivial U] {r : ℕ} (hr : 2 ≤ r) {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ)
    {P : ∀ {n : ℕ} {σ : Signature.{v}}, Circuit σ n 1 → Prop}
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    (hSK : DenseRectangleFree S K)
    (hsupply : ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (c : Circuit σ n 1),
      c.FanInAtMost r → P c →
      Nat.card U ^ {i : Fin n | ¬ Compiler.Reach c (.input i)}.ncard < K n →
      ∃ π : Layout (Compiler.Node c),
        (Compiler.signalWidth c π : ℝ) + ((3 * r + 2 : ℕ) : ℝ) +
          3 * Real.logb (Nat.card U) (K n) +
          Real.logb (Nat.card U) (Nat.card (Compiler.Node c) + 1) ≤ (1 - δ / b) * n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) → ¬ P c := by
  have hb0 : 0 < b := one_pos.trans hb
  have hdef := isLittleO_sub_logb_ncard hSK.isLittleO_deficit
  filter_upwards [hsupply, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    hdef.bound (show 0 < δ / (2 * b) by positivity), eventually_ge_atTop 1] with
    n hsup hfree hbig hndef hn1 σ I Acc c hfan hdec hPc
  obtain ⟨_, hunread⟩ :=
    logb_ncard_le_signalWidth I Acc c hr hfan hdec hfree hbig (Finite.equivFin (Compiler.Node c))
  obtain ⟨π, hB⟩ := hsup σ c hfan hPc hunread
  obtain ⟨hdem, _⟩ := logb_ncard_le_signalWidth I Acc c hr hfan hdec hfree hbig π
  simp only [Real.norm_eq_abs, Nat.abs_cast] at hndef
  exact contra_of_logb_base hb (mul_pos hδ (Nat.cast_pos.mpr hn1)) ((le_abs_self _).trans hndef)
    hdem hB

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
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_pos : 0 < D_r := gateSweep_denom_pos (by omega) k₀
  set L₀ := gateSweepCoefficient r k₀
  have hL₀_pos : 0 < L₀ := gateSweepCoefficient_pos (by omega) k₀
  have hDr_L₀ : (D_r / (2 : ℝ) ^ k₀) * L₀ = (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀ := by
    change (D_r / (2 : ℝ) ^ k₀) * ((k₀ + 2 : ℝ) / D_r) = _
    field_simp [hDr_pos.ne']
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  set η : ℝ := ((4 : ℝ) - 1) / (6 * 4) * δ
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨M, hM1, herr⟩ := eventually_signalWidth_err_le.{u, v} r 1
    (a := (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) (C_const := ((3 * r + 2 : ℕ) : ℝ) + 1 / (2 : ℝ) ^ k₀)
    hL₀_pos.le (by positivity) hη hK_pos hlogK
  filter_upwards [herr] with n ⟨_, hK_err, hconst_err, hcerr⟩ σ c hfan hsize hunread
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_le c hfan hM1
  refine ⟨π, ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hM_term, hsqrt_term, hlogV_err⟩ :=
    hcerr c (by have := mul_nonneg hε.le hn0; linarith)
  simp only [Nat.cast_one, mul_one] at hsqrt_term
  have hstr := sum_straddle_le_of_tangent (by omega : 1 ≤ r) k₀ c hfan
  rw [Nat.cast_one] at hstr
  have hs_term :
      (D_r / (2 : ℝ) ^ k₀) * c.innerSize ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n - δ * n := by
    have h1 := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ D_r / (2 : ℝ) ^ k₀)
    have hexp : (D_r / (2 : ℝ) ^ k₀) * ((L₀ - ε) * n) =
        ((D_r / (2 : ℝ) ^ k₀) * L₀) * n - δ * n := by dsimp only [δ, D_r]; ring
    rwa [hexp, hDr_L₀] at h1
  have hη_nn : 0 ≤ η * n := by positivity
  exact supply_base_le (b := 4) (by norm_num) (hπ.trans_eq (add_assoc _ _ _)) hstr hs_term
    (mul_le_mul_of_nonneg_left (ncard_not_reach_le_logb hunread) (by positivity))
    (by dsimp only [η] at hM_term hsqrt_term hη_nn ⊢; linarith) hK_err hlogV_err hconst_err

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
  have hDr_pos : (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := gateSweep_denom_pos (by omega) k₀
  filter_upwards [eventually_not_decides_of_signalWidth_supply.{u, v} hr (b := 4) (by norm_num)
    (by positivity) hSK (eventually_exists_layout_signalWidth_le_gateSweep.{u, v} hr k₀
      (hSK.eventually_rectangleFree.mono fun _ h => h.pos)
      (isLittleO_logb_of_log hSK.isLittleO_log (Nat.card U)) hε)] with n hn σ I Acc c hfan hdec
  exact lt_of_not_ge (hn σ I Acc c hfan hdec)

private theorem scale_lower_bound {b a ε n s : ℝ} (hb : 0 < b)
    (h : (a - ε / b) * n < s) : (b * a - ε) * n < b * s := by
  have hs := mul_lt_mul_of_pos_left h hb
  rwa [← mul_assoc, mul_sub, mul_div_cancel₀ _ hb.ne'] at hs

/-- Scaled `(r - 1) * c.innerSize` form of `eventually_gateSweep_lt_innerSize`. -/
theorem eventually_gateSweep_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r) (k₀ : ℕ)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ((r - 1 : ℝ) * gateSweepCoefficient r k₀ - ε) * n < (r - 1) * c.innerSize := by
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr)
  filter_upwards [eventually_gateSweep_lt_innerSize.{u, v} hr k₀ hSK
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)] with n hn σ I Acc c hfan hdec
  exact scale_lower_bound hr1_pos (hn σ I Acc c hfan hdec)

private theorem eventually_lt_mul_innerSize_of_le_gateSweepCoefficient {r : ℕ} (hr : 2 ≤ r)
    (k₀ : ℕ) {a : ℝ} (ha : a ≤ (r - 1 : ℝ) * gateSweepCoefficient r k₀)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (a - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [eventually_gateSweep_lt_mul_innerSize.{u, v} hr k₀ hSK hε] with
    n hn σ I Acc c hfan hdec
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right ha _) n.cast_nonneg).trans_lt
    (hn σ I Acc c hfan hdec)

/-- **Explicit `Ω(log r)` bounded-fan-in lower bound.** For every `r ≥ 2` and `ε > 0`, circuits of
fan-in at most `r` deciding dense rectangle-free sets `S_n ⊆ U^n` satisfy
`(r - 1) * c.innerSize > (log₂ r - log₂ log₂ r - 1 - ε) n` for all large `n`. -/
theorem eventually_log_sub_log_log_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 1 - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨k₀, hk₀⟩ := exists_log_sub_log_log_le_mul_gateSweepCoefficient hr
  exact eventually_lt_mul_innerSize_of_le_gateSweepCoefficient hr k₀ hk₀ hSK hε

/-- At fan-in `r = 8` (`k₀ = 2`), `7 * c.innerSize > (28 / 9 - ε) n` (`28 / 9 ≈ 3.1111`). -/
theorem eventually_twenty_eight_div_nine_lt_seven_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 8 → c.Decides I Acc (S n) →
        (28 / 9 - ε) * n < 7 * c.innerSize := by
  simpa only [Nat.cast_ofNat, show (8 : ℝ) - 1 = 7 by norm_num] using
    eventually_lt_mul_innerSize_of_le_gateSweepCoefficient (r := 8) (by decide) 2
      (by norm_num [gateSweepCoefficient]) hSK hε

/-- At fan-in `r = 40` (`k₀ = 4`), `39 * c.innerSize > (78 / 17 - ε) n` (`78 / 17 ≈ 4.5882`,
surpassing `4.57597`). -/
theorem eventually_seventy_eight_div_seventeen_lt_thirty_nine_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 40 → c.Decides I Acc (S n) →
        (78 / 17 - ε) * n < 39 * c.innerSize := by
  simpa only [Nat.cast_ofNat, show (40 : ℝ) - 1 = 39 by norm_num] using
    eventually_lt_mul_innerSize_of_le_gateSweepCoefficient (r := 40) (by decide) 4
      (by norm_num [gateSweepCoefficient]) hSK hε

/-- At fan-in `r = 64` (`k₀ = 4`), `63 * c.innerSize > (126 / 25 - ε) n` (`5.04 n`). -/
theorem eventually_one_hundred_twenty_six_div_twenty_five_lt_sixty_three_mul_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 64 → c.Decides I Acc (S n) →
        (126 / 25 - ε) * n < 63 * c.innerSize := by
  simpa only [Nat.cast_ofNat, show (64 : ℝ) - 1 = 63 by norm_num] using
    eventually_lt_mul_innerSize_of_le_gateSweepCoefficient (r := 64) (by decide) 4
      (by norm_num [gateSweepCoefficient]) hSK hε

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
  have hDr_pos : 0 < D_r := gateSweep_denom_pos (by omega) k₀
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
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr)
  obtain ⟨γ, hγ, H⟩ := exists_eventually_agreement_le_gateSweep.{u, v} hr k₀
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)
  refine ⟨γ, hγ, fun U _ _ S K b hbias hK => ?_⟩
  filter_upwards [H U S K b hbias hK] with n hn σ I Acc c hfan hsize
  refine hn σ I Acc c hfan (le_of_mul_le_mul_left (hsize.trans ?_) hr1_pos)
  calc _ ≤ ((r - 1 : ℝ) * gateSweepCoefficient r k₀ - ε) * n := by gcongr
    _ = _ := by field_simp

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
  have _ := hk₀
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  set η : ℝ := ((5 : ℝ) - 1) / (6 * 5) * δ
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B, _, hB_lb⟩ := exists_nat_pos_mul_ge (A := (k₀ + 3 : ℝ)) (mul_pos two_pos hη)
  obtain ⟨M, hM1, herr⟩ := eventually_signalWidth_err_le.{u, v} 2 (2 * B + 1)
    (L₀ := k₀ + 2) (a := (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀)
    (C_const := ((3 * 2 + 2 : ℕ) : ℝ) + 1 / (2 : ℝ) ^ k₀)
    (by positivity) (by positivity) hη hK_pos hlogK
  filter_upwards [herr] with n ⟨hn1, hK_err, hconst_err, hcerr⟩ σ c hfan hsize hunread
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_reuse_le c hfan B hM1
  refine ⟨π, ?_⟩
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs_le : (c.innerSize : ℝ) ≤ (k₀ + 2 : ℝ) * n := by
    have hr : (k₀ + 1 : ℝ) ≤ (2 : ℝ) ^ k₀ := by
      exact_mod_cast Nat.succ_le_of_lt k₀.lt_two_pow_self
    have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ k₀ - k₀ := by linarith
    linarith [mul_nonneg hr0 (Nat.cast_nonneg (Compiler.multiFanoutSize c)), mul_nonneg hε.le hn0]
  obtain ⟨hM_term, hsqrt_term, hlogV_err⟩ := hcerr c hs_le
  have hM3 : (3 * Nat.card (Compiler.Node c) : ℝ) / M ≤ η * n := by
    simpa only [show ((2 : ℕ) + 1 : ℝ) = 3 by norm_num] using hM_term
  have hsqrt3 : 3 * √((M * (2 * B + 1) * Nat.card (Compiler.Node c) : ℝ)) ≤ η * n := by
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, mul_assoc] using hsqrt_term
  have hB_term : (Nat.card (Compiler.Node c) : ℝ) / (2 * (B + 1)) ≤ η * n := by
    have hnat : (Nat.card (Compiler.Node c) : ℝ) ≤ c.innerSize + 1 := by
      exact_mod_cast Compiler.card_node_le c
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hB_lb hn0]
  have hstr := sum_nonUnit_straddle_le_of_tangent k₀ c hfan
  rw [Nat.cast_one] at hstr
  have hs_term :
      ((c.innerSize : ℝ) + ((2 : ℝ) ^ k₀ - k₀) * Compiler.multiFanoutSize c) / (2 : ℝ) ^ k₀ ≤
        ((k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) * n - δ * n := by
    refine (div_le_div_of_nonneg_right hsize (by positivity)).trans_eq ?_
    dsimp only [δ]
    ring
  exact supply_base_le (b := 5) (by norm_num)
    ((hπ.trans_eq (add_assoc _ _ _)).trans_eq (add_assoc _ _ _)) hstr hs_term
    (mul_le_mul_of_nonneg_left (ncard_not_reach_le_logb hunread) (by positivity))
    (by dsimp only [η] at hB_term hM3 hsqrt3 ⊢; linarith) hK_err hlogV_err hconst_err

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
  filter_upwards [eventually_not_decides_of_signalWidth_supply.{u, v} (by decide) (b := 5)
    (by norm_num) (by positivity) hSK
    (eventually_exists_layout_signalWidth_le_multiFanoutSize.{u, v} hk₀
      (hSK.eventually_rectangleFree.mono fun _ h => h.pos)
      (isLittleO_logb_of_log hSK.isLittleO_log (Nat.card U)) hε)] with n hn σ I Acc c hfan hdec
  exact lt_of_not_ge (hn σ I Acc c hfan hdec)

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
  convert hn σ I Acc c hfan hdec using 2 <;> norm_num

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
  set δ := (r + 1 : ℝ) * ε / 4
  have hδ : 0 < δ := by positivity
  set L₀ : ℝ := 4 / (r + 1 : ℝ)
  set η : ℝ := ((4 : ℝ) - 1) / (6 * 4) * δ
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨M, hM1, herr⟩ := eventually_signalWidth_err_le.{u, v} r 1
    (L₀ := L₀) (a := 0) (C_const := ((3 * r + 2 : ℕ) : ℝ) + 1 / 4)
    (by positivity) le_rfl hη (hSK.eventually_rectangleFree.mono fun _ h => h.pos)
    (isLittleO_logb_of_log hSK.isLittleO_log (Nat.card U))
  have hdef := isLittleO_sub_logb_ncard hSK.isLittleO_deficit
  filter_upwards [hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    hdef.bound (show 0 < δ / (2 * 4) by positivity), herr] with
    n hfree hbig hndef ⟨hn1, hK_err, hconst_err, hcerr⟩ k σ I Acc c hfan hndec
  by_contra! hsize
  classical
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  obtain ⟨π, hπ⟩ := Compiler.exists_layout_signalWidth_le c hfan hM1
  obtain ⟨hM_term, hsqrt_term, hlogV_err⟩ :=
    hcerr c (by have := mul_nonneg hε.le (Nat.cast_nonneg n); linarith)
  simp only [Nat.cast_one, mul_one] at hsqrt_term
  set H := Compiler.hiddenSteinerNetwork c I (fun _ => Acc) π
  have hacc : H.accepted = S n := by
    ext x
    simp only [H, Compiler.accepted_hiddenSteinerNetwork, mem_ofPred_eq, hndec x]
    exact exists_congr fun y => ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have hdem := logb_ncard_le_of_steinerGraph (Compiler.hiddenSteinerNetwork_toMultigraph c I _ π)
    hfan (fun u => (Network.ncard_readAt_hide_le _ u).trans
      ((Network.ncard_readAt_reindex _ _ u).trans_le
        ((Compiler.ncard_readAt_steinerNetwork_le hfan u).trans_eq (max_eq_left (by omega)))))
    hacc hfree hbig
  have hstr :
      (∑ w : Compiler.ActiveSignal c,
          (1 - (1 / 2 : ℝ) ^ ((Compiler.support c w).ncard - 1))) ≤
        (1 - 0) * n + (-(δ * n)) + 0 * 0 + 1 / 4 := by
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
    have hs_mul : (r + 1 : ℝ) * c.innerSize ≤ (4 - 4 * δ) * n :=
      (mul_le_mul_of_nonneg_left hsize (by positivity)).trans_eq
        (by dsimp only [L₀, δ]; field_simp)
    linarith
  simp only [Real.norm_eq_abs, Nat.abs_cast] at hndef
  have hη_nn : 0 ≤ η * n := by positivity
  have hB := supply_base_le (b := 4) (L_K := Real.logb (Nat.card U) (K n)) (by norm_num)
    (hπ.trans_eq (add_assoc _ _ _)) hstr (by linarith) (by simp)
    (by dsimp only [η] at hM_term hsqrt_term hη_nn ⊢; linarith) hK_err hlogV_err hconst_err
  exact contra_of_logb_base (b := 4) (by norm_num) (mul_pos hδ (Nat.cast_pos.mpr hn1))
    ((le_abs_self _).trans hndef) hdem hB

/-- Scaled `(r - 1) * c.innerSize` form of
`eventually_four_div_lt_innerSize_of_nondeterministicDecides` (approaching `4 n` as `r → ∞`). -/
theorem eventually_four_mul_div_lt_mul_innerSize_of_nondeterministicDecides {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (4 * (r - 1 : ℝ) / (r + 1 : ℝ) - ε) * n < (r - 1) * c.innerSize := by
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr)
  filter_upwards [eventually_four_div_lt_innerSize_of_nondeterministicDecides.{u, v} hr hSK
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)] with n hn k σ I Acc c hfan hndec
  simpa only [mul_div_assoc', mul_comm (4 : ℝ)] using
    scale_lower_bound hr1_pos (hn k σ I Acc c hfan hndec)

end Family4

end Cslib.Circuits.Frontier
