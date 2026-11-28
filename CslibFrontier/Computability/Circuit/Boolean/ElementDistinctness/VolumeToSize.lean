/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Full
public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Frontier.Compiler.OpenBitNetwork
import CslibFrontier.Computability.Circuit.InnerSize
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Embedding

/-!
# From dyadic distinctness volume to circuit size

The one-list case of [OpenAI2026MatrixExponentNineFourths, Theorem 2.2] gives a volume lower
bound for `2 ^ w` records of `2 * w` bits. This module proves the conditional transfer from that
bound to a gate lower bound for every sufficiently large record count.

For `m` records take `w = ⌈log₂ m⌉ - 1`, so that `2 ^ w < m ≤ 2 ^ (w + 1)`. Keep the payload
positions of the first `2 ^ w` records, mark these rows with zero, and assign the remaining rows
distinct fixed words marked with one. Pinning these bits in the compiled circuit leaves a network
for the smaller list. A power of two as the original record count uses the same construction.

* `exists_pin_distinctness` restricts the exact tensor on the same internal graph.
* `exists_dyadic_network_of_computes` bounds the resulting volume in terms of the circuit size.
* `eventual_complexity_of_single_copy_volume` transfers the log-power exponent.
* `eventually_gt_mul_of_log_power` derives eventual domination of any linear gate bound.
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Filter Function Frontier

variable {m k d : ℕ}

private def positions (m k d r : ℕ) : Fin (m * k) ↪ Fin ((m + d) * (k + r)) :=
  finProdFinEquiv.symm.toEmbedding.trans
    (((Fin.castAddEmb d).prodMap (Fin.castAddEmb r)).trans finProdFinEquiv.toEmbedding)

private theorem positions_apply (r : ℕ) (i : Fin m) (j : Fin k) :
    positions m k d r (finProdFinEquiv (i, j)) =
      finProdFinEquiv (Fin.castAdd d i, Fin.castAdd r j) := by
  simp [positions]

private def sentinel (hd : d ≤ 2 ^ k) (j : Fin d) : BitString k :=
  (BitString.equivFin k).symm (Fin.castLE hd j)

private def padded (hd : d ≤ 2 ^ k) (q : ℕ) (x : BitString (m * k)) :
    BitString ((m + d) * (k + (q + 1))) :=
  BitString.blocksEquiv.symm (Fin.append
    (fun i => Fin.append (BitString.block x i) (fun _ => false))
    (fun j => Fin.append (sentinel hd j) (fun _ => true)))

private theorem extend_padded (hd : d ≤ 2 ^ k) (q : ℕ) (x : BitString (m * k)) :
    extend (positions m k d (q + 1)) x (padded hd q (fun _ => false)) = padded hd q x := by
  let e := positions m k d (q + 1)
  funext p
  by_cases hp : ∃ j, e j = p
  · obtain ⟨j, rfl⟩ := hp
    rw [e.injective.extend_apply]
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective j
    simp [e, positions_apply, padded, BitString.blocksEquiv_symm_apply]
  · rw [extend_apply' _ _ _ hp]
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    cases i using Fin.addCases with
    | left i =>
      cases j using Fin.addCases with
      | left j =>
        exact False.elim (hp ⟨finProdFinEquiv (i, j), positions_apply (q + 1) i j⟩)
      | right j => simp [padded, BitString.blocksEquiv_symm_apply]
    | right i => simp [padded, BitString.blocksEquiv_symm_apply]

private theorem elementDistinctness_padded (hd : d ≤ 2 ^ k) (q : ℕ) (x : BitString (m * k)) :
    elementDistinctness _ _ (padded hd q x) = elementDistinctness m k x := by
  simp only [elementDistinctness, padded, BitString.block_blocksEquiv_symm,
    Fin.append_injective_iff]
  congr 1
  apply propext
  constructor
  · intro ⟨h, _, _⟩ i j e
    exact h (congrArg (fun a => Fin.append a fun _ => false) e)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j e
      exact h (funext fun b => by simpa using congrFun e (Fin.castAdd (q + 1) b))
    · intro i j e
      have hs : sentinel hd i = sentinel hd j := funext fun b => by
        simpa using congrFun e (Fin.castAdd (q + 1) b)
      exact Fin.castLE_injective hd ((BitString.equivFin k).symm.injective hs)
    · intro i j e
      simpa using congrFun e (Fin.natAdd k (0 : Fin (q + 1)))

/-- Keep `m` rows of `k` bits from a list of wider records. All other bits are pinned.
The remaining `count - m` rows receive distinct fixed names. -/
public theorem exists_pin_distinctness {R V E : Type*} [CommSemiring R] [Fintype V] [Fintype E]
    [DecidableEq E] {count bits : ℕ} (hm : m ≤ count) (hk : k < bits) (hfill : count - m ≤ 2 ^ k)
    (N : OpenBitNetwork R (Fin (count * bits)) V E) (hN : N.Trivalent)
    (hD : ∀ x, N.contraction x = if elementDistinctness count bits x then 1 else 0) :
    ∃ M : OpenBitNetwork R (Fin (m * k)) V E, M.toMultigraph = N.toMultigraph ∧ M.Trivalent ∧
      M.volume ≤ N.volume ∧ ∀ x, M.contraction x = if elementDistinctness m k x then 1 else 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hk
  have hbits : bits = k + (q + 1) := by lia
  clear hq
  subst bits
  have hd : d ≤ 2 ^ k := by simpa using hfill
  obtain ⟨M, hg, _, ht, hv, hc⟩ := N.exists_pin hN (positions m k d (q + 1))
    (padded hd q (fun _ => false))
  refine ⟨M, hg, ht, hv, fun x => ?_⟩
  rw [hc, extend_padded, hD, elementDistinctness_padded]

/-- A fan-in-two circuit for a list of the prescribed width gives a trivalent network for the
greatest dyadic list strictly shorter than it. Pinning drops exactly the discarded exterior bits
and keeps the internal graph. -/
public theorem exists_dyadic_network_of_computes {σ : Signature} {m : ℕ} (hm : 1 < m)
    (I : Interpretation σ Bool) (C : Circuit σ (m * (2 * Nat.clog 2 m)) 1)
    (hf : C.FanInAtMost 2) (hc : C.Computes I (single (elementDistinctness m (2 * Nat.clog 2 m))))
    (R : Type*) [CommSemiring R] :
    let w := Nat.clog 2 m - 1
    let D := 2 ^ w * (2 * w)
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork R (Fin D) V E), M.Trivalent ∧
        M.volume ≤ m * (2 * Nat.clog 2 m) + D + 8 * C.size + 5 ∧
        ∀ x, M.contraction x = if elementDistinctness (2 ^ w) (2 * w) x then 1 else 0 := by
  let w := Nat.clog 2 m - 1
  let D := 2 ^ w * (2 * w)
  have ht : Nat.clog 2 m = w + 1 := by
    have := Nat.clog_pos (b := 2) (by decide) hm
    dsimp [w]
    lia
  have hlow : 2 ^ w < m := Nat.pow_pred_clog_lt_self 2 hm
  have hhigh := Nat.le_pow_clog (b := 2) (by decide) m
  rw [ht, pow_succ] at hhigh
  have hfill : m - 2 ^ w ≤ 2 ^ (2 * w) := by
    exact (by lia : m - 2 ^ w ≤ 2 ^ w).trans (Nat.pow_le_pow_right (by decide) (by lia))
  obtain ⟨V, E, vT, eT, dE, N, hN, hvol, heval⟩ :=
    Compiler.exists_trivalent_openBitNetwork C I R hf
  obtain ⟨M, _, hM, _, hentry⟩ := exists_pin_distinctness hlow.le
    (by lia : 2 * w < 2 * Nat.clog 2 m) hfill N hN fun x => by
      simpa only [hc x, single] using heval x
  refine ⟨V, E, vT, eT, dE, M, hM, ?_, hentry⟩
  have hcost : M.volume + m * (2 * Nat.clog 2 m) = N.volume + D := by
    simp [OpenBitNetwork.volume, D, add_right_comm]
  lia

private theorem input_length_window {m w : ℕ} (hw : 0 < w) (ht : Nat.clog 2 m = w + 1)
    (hm : 0 < m) :
    let N := m * (2 * Nat.clog 2 m)
    N ≤ 4 * (2 ^ w * (2 * w)) ∧ Real.logb 2 N ≤ 4 * (w : ℝ) := by
  let N := m * (2 * Nat.clog 2 m)
  have hm' := Nat.le_pow_clog (b := 2) (by decide) m
  rw [ht] at hm'
  constructor
  · rw [ht]
    calc
      _ ≤ 2 ^ (w + 1) * (2 * (w + 1)) := Nat.mul_le_mul_right _ hm'
      _ ≤ 4 * (2 ^ w * (2 * w)) := by rw [pow_succ]; nlinarith [Nat.two_pow_pos w]
  · have hnpos : 0 < N := by dsimp [N]; rw [ht]; positivity
    have hn : N ≤ 2 ^ ((w + 1) + (w + 1)) := by
      rw [pow_add]
      exact Nat.mul_le_mul hm' (by rw [ht, pow_succ]; have := Nat.lt_two_pow_self (n := w); lia)
    calc
      _ ≤ Real.logb 2 ((2 : ℝ) ^ ((w + 1) + (w + 1))) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hnpos) (by exact_mod_cast hn)
      _ ≤ 4 * (w : ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        push_cast
        linarith [show (1 : ℝ) ≤ w by exact_mod_cast hw]

/-- Assuming a log-power volume lower bound for one dyadic list, the same exponent gives a gate
lower bound at every sufficiently large record count. The gate basis contains every binary
Boolean function and both constants. -/
public theorem eventual_complexity_of_single_copy_volume (R : Type*) [CommSemiring R]
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hvol : ∀ᶠ w : ℕ in atTop,
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E]
        (M : OpenBitNetwork R (Fin (2 ^ w * (2 * w))) V E), M.Trivalent →
        (∀ x, M.contraction x = if elementDistinctness (2 ^ w) (2 * w) x then 1 else 0) →
        a * (2 ^ w * (2 * w) : ℕ) * (w : ℝ) ^ ε ≤ M.volume) :
    ∀ᶠ m : ℕ in atTop, let N := m * (2 * Nat.clog 2 m)
      a / (64 * 4 ^ ε) * N * (Real.logb 2 N) ^ ε <
        complexity (fullInterpretation (k := 2))
          (single (elementDistinctness m (2 * Nat.clog 2 m))) := by
  let width (m : ℕ) := Nat.clog 2 m - 1
  have hwidth : Tendsto width atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (Nat.tendsto_clog_atTop one_lt_two)
  have hpow : Tendsto (fun m => (width m : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop.comp hwidth)
  filter_upwards [hwidth.eventually hvol, hpow.eventually_gt_atTop (20 / a),
    hwidth.eventually_ge_atTop 1, eventually_gt_atTop 1] with m hdy hscale hw hm
  let w := width m
  let D := 2 ^ w * (2 * w)
  let N := m * (2 * Nat.clog 2 m)
  let s := complexity (fullInterpretation (k := 2))
    (single (elementDistinctness m (2 * Nat.clog 2 m)))
  change a / (64 * 4 ^ ε) * N * (Real.logb 2 N) ^ ε < s
  have hcw : Nat.clog 2 m = w + 1 := by
    dsimp only [w, width] at hw ⊢
    lia
  obtain ⟨hlen, hlog⟩ := input_length_window (m := m) (w := w) hw hcw (by lia)
  have hNpos : 0 < N := by dsimp [N]; rw [hcw]; positivity
  have hDpos : 0 < D := Nat.mul_pos (Nat.two_pow_pos _) (by dsimp [D, w]; lia)
  obtain ⟨C, hc, hs⟩ := exists_computes_size_eq_complexity (I := fullInterpretation (k := 2))
    (f := single (elementDistinctness m (2 * Nat.clog 2 m)))
  obtain ⟨V, E, iV, iE, dE, M, ht, hv, hentry⟩ :=
    exists_dyadic_network_of_computes hm fullInterpretation C C.fanInAtMost_fullSignature hc R
  have hcost : a * D * (w : ℝ) ^ ε ≤ (N : ℝ) + D + 8 * s + 5 := by
    refine (@hdy V E iV iE dE M ht hentry).trans ?_
    rw [hs] at hv
    exact_mod_cast hv
  have hlen' : (N : ℝ) ≤ 4 * D := by exact_mod_cast hlen
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
  have hgain : 20 * (D : ℝ) < a * D * (w : ℝ) ^ ε := by
    have h : 20 < a * (w : ℝ) ^ ε := by simpa [mul_comm] using (div_lt_iff₀ ha).1 hscale
    calc _ < (a * (w : ℝ) ^ ε) * D := mul_lt_mul_of_pos_right h (by exact_mod_cast hDpos)
         _ = _ := by ring
  have hlog0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hNpos)
  calc
    _ ≤ a / (64 * 4 ^ ε) * (4 * D) * ((4 : ℝ) ^ ε * (w : ℝ) ^ ε) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg w)]
      gcongr
    _ = a * D * (w : ℝ) ^ ε / 16 := by field_simp; ring
    _ < s := by linarith

/-- An eventual log-power gate lower bound at the specified record widths dominates every
fixed real multiple of the input length. -/
public theorem eventually_gt_mul_of_log_power {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hbound : ∀ᶠ m : ℕ in atTop, let N := m * (2 * Nat.clog 2 m)
      c * N * (Real.logb 2 N) ^ ε <
        complexity (fullInterpretation (k := 2))
          (single (elementDistinctness m (2 * Nat.clog 2 m))))
    (A : ℝ) : ∀ᶠ m : ℕ in atTop, A * (m * (2 * Nat.clog 2 m) : ℕ) <
      complexity (fullInterpretation (k := 2))
        (single (elementDistinctness m (2 * Nat.clog 2 m))) := by
  let N (m : ℕ) := m * (2 * Nat.clog 2 m)
  have hN : Tendsto (fun m => (N m : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_gt_atTop 1] with m hm
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by decide) (Nat.clog_pos (by decide) hm))
  have hlog := (tendsto_rpow_atTop hε).comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hN)
  filter_upwards [hbound, hlog.eventually_ge_atTop (A / c)] with m hm ha
  refine lt_of_le_of_lt ?_ hm
  change A * (N m : ℝ) ≤ c * N m * (Real.logb 2 (N m)) ^ ε
  rw [mul_right_comm c]
  exact mul_le_mul_of_nonneg_right
    (by simpa [mul_comm] using (div_le_iff₀ hc).mp ha) (Nat.cast_nonneg _)

end Cslib.Circuits.Boolean.ElementDistinctness
