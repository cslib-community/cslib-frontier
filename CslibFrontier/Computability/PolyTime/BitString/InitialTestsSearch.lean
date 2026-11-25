/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.GenericRAM.Native.IndexFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Foundations.Combinatorics.Expander.TannerCode
public import CslibFrontier.Foundations.Data.BitString.ParityTestBounds
public import CslibFrontier.Foundations.Data.BitString.List.Dot
import CslibFrontier.Computability.GenericRAM.Native.BooleanFold
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.InitialTests
import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Nat.CeilDiv
import CslibFrontier.Probability.SmallBias.Random
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import Mathlib.Analysis.Complex.ExponentialBounds
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Sequential initial-test search and shortened Tanner check matrices

Deterministic sequential search and shortened Tanner parity-check construction from
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1, Lemma 6.1 (pp. 40–42),
giving the executable counterpart to `Cslib.BitString.exists_initialTests`. Given `n, B ≥ 1` and
`m ≤ B * n`, `initialTestsRows m B` constructs a binary matrix `A^(0)` on `m` columns with at most
`3 * n` rows of weight at most `initialRowWeightBound B m` whose `GF(2)` kernel excludes every
nonzero vector of weight below `m / greedyRowListLength B m`, in `exp(poly(B, log(m + 2)))` bit
operations and `poly(n, m, B)` working space via `Cslib.GenericRAM.IndexFold.run`.

## Main definitions

* `dG`, `ellG`, `qG`, `cG`, `hDist`, `biasDen`: Lemma 6.1 parameter schedule.
* `checkSmallBiasShifts`, `checkLocalCodeDistance`, `findSmallBiasShifts`, `findLocalCheckMatrix`:
  streaming `IndexFold.run` checkers and sequential searchers.
* `buildShortenedTannerRows`, `initialTestsRows`: shortened Tanner check-matrix assembly.
* `encLocalCodeParams`: the encoding of local check-matrix parameters `(c, d, minDist)` in unary.

## Main results

* `checkSmallBiasShifts_eq_true_iff`, `checkLocalCodeDistance_eq_true_iff`,
  `isSmallBias_findSmallBiasShifts`, `weight_le_of_findLocalCheckMatrix`: checker/searcher specs.
* `initialTestsRows_spec`, `map_ofList_initialTestsRows_spec`, `initialTestsRows_computableInO`,
  `initialTestsRows_computableInO_nmb`: unconditional Lemma 6.1 correctness and `ComputableInO`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1, Lemma 6.1
* [R. M. Tanner, *A recursive approach to low complexity codes*][Tanner1981]
* [J. Naor, M. Naor, *Small-bias probability spaces*][NaorNaor1993]
-/

@[expose] public section

namespace Cslib.Complexity.InitialTestsSearch
open Finset Cslib.BitString Cslib.GenericRAM Cslib.Probability.PMF Turing.MultiTapeTM
open ComputableInPolyTime

/-! ### Lemma 6.1 integer parameter schedule -/
private abbrev mu (m : ℕ) : ℕ := Nat.log 2 m + 1

/-- Cayley degree `d_G = min(m, D₀)` (`D₀ = initialRowWeightBound B m`) of [OpenAI2026ETH],
Lemma 6.1. -/
def dG (m B : ℕ) : ℕ := min m (initialRowWeightBound B m)
/-- Cube dimension `ℓ_G = ⌈log₂ ⌈m / d_G⌉⌉` of [OpenAI2026ETH], Lemma 6.1 (`0` if `d_G = 0`). -/
def ellG (m B : ℕ) : ℕ := Nat.clog 2 ((m + dG m B - 1) / dG m B)
/-- Vertex-side size `q_G = 2 ^ ℓ_G` of the double cover in [OpenAI2026ETH], Lemma 6.1. -/
def qG (m B : ℕ) : ℕ := 2 ^ ellG m B
/-- Local parity-check row count `c_G = ⌈d_G / (8 B)⌉` of [OpenAI2026ETH], Lemma 6.1
(`0` if `B = 0`). -/
def cG (m B : ℕ) : ℕ := (dG m B + 8 * B - 1) / (8 * B)
/-- Maximum rejected weight `h = ⌈d_G / (100 B μ)⌉ - 1` for the local code of Lemma 6.1
(`0` if `d_G = 0` or `B = 0`). -/
def hDist (m B : ℕ) : ℕ :=
  (dG m B + 100 * B * (Nat.log 2 m + 1) - 1) / (100 * B * (Nat.log 2 m + 1)) - 1
/-- Reciprocal bias denominator `200 B μ` (`ε = 1 / biasDen m B`) in [OpenAI2026ETH], (6.2). -/
def biasDen (m B : ℕ) : ℕ := 200 * B * (Nat.log 2 m + 1)

theorem dG_pos {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : 0 < dG m B := by
  unfold dG initialRowWeightBound; exact Nat.lt_min.2 ⟨hm, by positivity⟩
theorem le_qG_mul_dG {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : m ≤ qG m B * dG m B :=
  (Nat.le_ceilDiv_mul (dG_pos hm hB)).trans <| by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide : 1 < 2) _)
theorem qG_mul_dG_lt_two_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : qG m B * dG m B < 2 * m := by
  have hd := dG_pos hm hB; set k := (m + dG m B - 1) / dG m B
  rcases le_or_gt k 1 with hk | hk
  · have h0 : ellG m B = 0 := Nat.clog_of_right_le_one hk 2
    have : dG m B ≤ m := Nat.min_le_left _ _; simp only [qG, h0, pow_zero, one_mul]; omega
  · have hell : 0 < Nat.clog 2 k := (Nat.lt_clog_iff_pow_lt (by decide)).2 hk
    have hlt : 2 ^ (Nat.clog 2 k - 1) < k := (Nat.lt_clog_iff_pow_lt (by decide)).1 (by omega)
    have hle := (Nat.mul_le_mul_left _ hlt).trans (Nat.mul_div_le (m + dG m B - 1) (dG m B))
    have hq : qG m B * dG m B = 2 * (dG m B * 2 ^ (Nat.clog 2 k - 1)) := by
      change 2 ^ Nat.clog 2 k * dG m B = _; conv_lhs => rw [← Nat.sub_add_cancel hell, Nat.pow_succ]
      ring
    rw [Nat.succ_eq_add_one, Nat.mul_add, mul_one] at hle; omega
theorem qG_lt_two_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : qG m B < 2 * m :=
  (Nat.le_mul_of_pos_right _ (dG_pos hm hB)).trans_lt (qG_mul_dG_lt_two_mul hm hB)
theorem qG_le_two_mul_add_one (m B : ℕ) : qG m B ≤ 2 * m + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm; · simp only [qG, ellG, dG, Nat.zero_min]; decide
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp only [qG, ellG, dG, initialRowWeightBound, sq, mul_zero, zero_mul, Nat.min_zero,
      Nat.div_zero]; change 1 ≤ 2 * m + 1; omega
  have := qG_lt_two_mul hm hB; omega
private theorem dG_eq_of_ellG_pos {m B : ℕ} (hpos : 0 < ellG m B) :
    dG m B = initialRowWeightBound B m := by
  by_contra hne; have hd : dG m B = m := Nat.min_eq_left (by unfold dG at hne; omega)
  rcases Nat.eq_zero_or_pos m with rfl | hm; · rw [ellG, hd] at hpos; exact absurd hpos (by decide)
  have hdiv : (m + m - 1) / m ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hm).2 (by omega))
  have h0 : ellG m B = 0 := by unfold ellG; rw [hd]; exact Nat.clog_of_right_le_one hdiv 2
  omega
private theorem ellG_le_mu (m B : ℕ) : ellG m B ≤ mu m := by
  rw [ellG, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [dG, Nat.zero_min, add_zero, Nat.zero_sub, Nat.div_zero, Nat.zero_le]
  rcases Nat.eq_zero_or_pos (dG m B) with hd | hd; · simp only [hd, Nat.div_zero, Nat.zero_le]
  refine ((Nat.div_le_iff_le_mul_add_pred hd).2 ?_).trans
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m).le
  have := Nat.le_mul_of_pos_left m hd; omega
private theorem cG_le_dG_add_one (m B : ℕ) : cG m B ≤ dG m B + 1 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB; · simp only [cG, mul_zero, Nat.div_zero, Nat.zero_le]
  refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega : 0 < 8 * B)).2
    ((Nat.sub_le _ _).trans_lt ?_))
  have := Nat.le_mul_of_pos_right (dG m B) (by omega : 0 < 8 * B)
  have : (dG m B + 1 + 1) * (8 * B) = dG m B * (8 * B) + 16 * B := by ring
  change dG m B + 8 * B < (dG m B + 1 + 1) * (8 * B); omega
theorem two_mul_qG_mul_cG_le_three_mul {n m B : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hmn : m ≤ B * n) : 2 * qG m B * cG m B ≤ 3 * n := by
  have hmul : 8 * B * cG m B ≤ dG m B + 8 * B - 1 := Nat.mul_div_le _ (8 * B)
  have hBn : B ≤ B * n := Nat.le_mul_of_pos_right B hn
  rcases Nat.eq_zero_or_pos (ellG m B) with h0 | hpos
  · have hq : qG m B = 1 := by simp only [qG, h0, pow_zero]
    have h1 := le_qG_mul_dG hm hB; have h2 : dG m B ≤ m := Nat.min_le_left _ _
    have hd : dG m B = m := by rw [hq, one_mul] at h1; omega
    rw [hq, mul_one]; rw [hd] at hmul
    have : B * (8 * cG m B) = 8 * B * cG m B := by ring
    have : B * (12 * n) = 12 * (B * n) := by ring
    have := Nat.lt_of_mul_lt_mul_left (by omega : B * (8 * cG m B) < B * (12 * n)); omega
  · have h8_le_dG : 8 * B ≤ dG m B := by
      rw [dG_eq_of_ellG_pos hpos, initialRowWeightBound]
      have := Nat.mul_le_mul_left (320000 * B)
        (Nat.mul_pos hB (by positivity : 0 < (Nat.log 2 m + 1) ^ 3))
      have : 320000 * B * (B * (Nat.log 2 m + 1) ^ 3) =
        320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3 := by ring
      omega
    have : B * (4 * (2 * qG m B * cG m B)) = qG m B * (8 * B * cG m B) := by ring
    have := Nat.mul_le_mul_left (qG m B) (by omega : 8 * B * cG m B ≤ 2 * dG m B)
    have : qG m B * (2 * dG m B) = 2 * (qG m B * dG m B) := by ring
    have := qG_mul_dG_lt_two_mul hm hB; have : B * (4 * (3 * n)) = 12 * (B * n) := by ring
    have : B * (4 * (2 * qG m B * cG m B)) < B * (4 * (3 * n)) := by omega
    have := Nat.lt_of_mul_lt_mul_left this; omega
private theorem hDist_succ_eq {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    hDist m B + 1 = (dG m B + 100 * B * mu m - 1) / (100 * B * mu m) := by
  have hd : 1 ≤ dG m B := dG_pos hm hB; have hM : 0 < 100 * B * mu m := by positivity
  have h1 : 1 * (100 * B * mu m) ≤ dG m B + 100 * B * mu m - 1 := by omega
  have := (Nat.le_div_iff_mul_le hM).2 h1; unfold hDist; dsimp only [mu] at *; omega
theorem dG_le_hDist_succ_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    dG m B ≤ (hDist m B + 1) * (100 * B * (Nat.log 2 m + 1)) := by
  change dG m B ≤ (hDist m B + 1) * (100 * B * mu m)
  rw [hDist_succ_eq hm hB, ← Nat.ceilDiv_eq_add_pred_div]; exact Nat.le_ceilDiv_mul (by positivity)

private abbrev encMB : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary
section
variable {α : Type} {e : α ↪ List Bool} {m B : α → ℕ}
  (hm : ComputableInPolyTime m e encUnary) (hB : ComputableInPolyTime B e encUnary)
include hm
private theorem mu_polyTime : ComputableInPolyTime (fun a => Nat.log 2 (m a) + 1) e encUnary :=
  .unary_add'
    ((ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary).comp hm)
    (.const 1)
include hB
@[fun_prop] theorem greedyRowListLength_polyTime :
    ComputableInPolyTime (fun a => greedyRowListLength (B a) (m a)) e encUnary :=
  .unary_mul' (.unary_mul' (.const 20000) ((unary_pow 2).comp hB))
    ((unary_pow 2).comp (mu_polyTime hm))
@[fun_prop] theorem initialRowWeightBound_polyTime :
    ComputableInPolyTime (fun a => initialRowWeightBound (B a) (m a)) e encUnary :=
  .unary_mul' (.unary_mul' (.const 320000) ((unary_pow 2).comp hB))
    ((unary_pow 3).comp (mu_polyTime hm))
@[fun_prop] theorem dG_polyTime : ComputableInPolyTime (fun a => dG (m a) (B a)) e encUnary :=
  unary_min' hm (initialRowWeightBound_polyTime hm hB)
@[fun_prop] theorem ellG_polyTime : ComputableInPolyTime (fun a => ellG (m a) (B a)) e encUnary :=
  have hd := dG_polyTime hm hB
  (unary_clog_const 2).comp (unary_div.comp ((unary_sub' (.unary_add' hm hd) (.const 1)).prod hd))
@[fun_prop] theorem qG_polyTime : ComputableInPolyTime (fun a => qG (m a) (B a)) e encUnary :=
  have hd := dG_polyTime hm hB
  unary_pow_clog_const (unary_div.comp ((unary_sub' (.unary_add' hm hd) (.const 1)).prod hd)) 2 2
@[fun_prop] theorem cG_polyTime : ComputableInPolyTime (fun a => cG (m a) (B a)) e encUnary :=
  have h8 := unary_mul' (.const 8) hB
  unary_div.comp ((unary_sub' (.unary_add' (dG_polyTime hm hB) h8) (.const 1)).prod h8)
@[fun_prop] theorem hDist_polyTime : ComputableInPolyTime (fun a => hDist (m a) (B a)) e encUnary :=
  have h100 := unary_mul' (.unary_mul' (.const 100) hB) (mu_polyTime hm)
  .unary_sub' (unary_div.comp
    ((unary_sub' (.unary_add' (dG_polyTime hm hB) h100) (.const 1)).prod h100)) (.const 1)
@[fun_prop] theorem biasDen_polyTime :
    ComputableInPolyTime (fun a => biasDen (m a) (B a)) e encUnary :=
  .unary_mul' (.unary_mul' (.const 200) hB) (mu_polyTime hm)
end

/-! ### Private streaming `IndexFold` and matrix-search combinators -/
private abbrev pOf := @PolyBounded.of_polynomiallyBounded
private theorem equivFin_symm_eq_zero_iff {width : ℕ} (k : Fin (2 ^ width)) :
    (equivFin width).symm k = 0 ↔ k.val = 0 := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, show (0 : BitString width) = fun _ => false from rfl,
    val_equivFin_false]
private theorem length_encList_listRows (count width : ℕ) (word : List Bool) :
    (encList encBits (listRows count width word)).length = count * (2 * width + 1) := by
  simp only [length_encList, listRows, List.map_map, Function.comp_def, encBits_apply,
    length_listRow, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
private abbrev allPositiveIndices {γ : Type} (width : ℕ) (ctx : γ) (initOk : Bool)
    (test : γ → ℕ → Bool) : Bool :=
  (IndexFold.run (fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
    (2 ^ width) (ctx, initOk)).2.2
private theorem run_allIndex_fst {γ : Type} (test : γ → ℕ → Bool) (n : ℕ) (ctx : γ)
    (initOk : Bool) :
    (IndexFold.run (fun p : ℕ × γ × Bool => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
      n (ctx, initOk)).2.1 = ctx := by
  induction n with | zero => rfl | succ n ih => simp only [IndexFold.run_succ, IndexFold.step, ih]
private theorem allPositiveIndices_eq_true_iff {γ : Type} (width : ℕ) (ctx : γ) (initOk : Bool)
    (test : γ → ℕ → Bool) : allPositiveIndices width ctx initOk test = true ↔
      initOk = true ∧ ∀ i < 2 ^ width, i ≠ 0 → test ctx i = true := by
  suffices ∀ n, (IndexFold.run
      (fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
      n (ctx, initOk)).2.2 = true ↔ initOk = true ∧ ∀ i < n, i ≠ 0 → test ctx i = true from
    this (2 ^ width)
  intro n; induction n with
  | zero => simp only [IndexFold.run_zero, Nat.not_lt_zero, false_implies, implies_true, and_true]
  | succ n ih =>
    rw [IndexFold.run_succ]; simp only [IndexFold.step, IndexFold.run_index, run_allIndex_fst,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ih]
    refine ⟨fun ⟨⟨hinit, hprev⟩, hlast⟩ => ⟨hinit, fun i hi hne => ?_⟩,
      fun ⟨hinit, hall⟩ => ⟨⟨hinit, fun i hi hne => hall i (Nat.lt_succ_of_lt hi) hne⟩, ?_⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl; · exact hprev i hlt hne
      exact hlast.resolve_left hne
    · exact if h0 : n = 0 then Or.inl h0 else Or.inr (hall n (Nat.lt_succ_self n) h0)
private theorem allPositiveIndices_lowBits_eq_true_iff {γ : Type} (widthOf : γ → ℕ) (ctx : γ)
    (initOk : Bool) (test : γ → List Bool → Bool) :
    allPositiveIndices (widthOf ctx) ctx initOk (fun c i => test c (lowBits (widthOf c) i)) =
      true ↔
      initOk = true ∧ ∀ w : BitString (widthOf ctx), w ≠ 0 → test ctx (List.ofFn w) = true := by
  rw [allPositiveIndices_eq_true_iff]
  refine and_congr_right' ⟨fun hall w hw0 => ?_, fun hall idx hidx hne => ?_⟩
  · let k := equivFin (widthOf ctx) w
    have hk0 : k.val ≠ 0 := fun hk => hw0 <| by
      rw [← (equivFin (widthOf ctx)).symm_apply_apply w]
      exact (equivFin_symm_eq_zero_iff k).2 hk
    have htest := hall k.val k.isLt hk0
    rwa [lowBits_eq_ofFn_equivFin_symm _ k, Equiv.symm_apply_apply] at htest
  · let k : Fin (2 ^ widthOf ctx) := ⟨idx, hidx⟩
    have hw0 : (equivFin (widthOf ctx)).symm k ≠ 0 :=
      fun h0 => hne ((equivFin_symm_eq_zero_iff k).1 h0)
    rw [lowBits_eq_ofFn_equivFin_symm _ k]
    exact hall _ hw0
private theorem allPositiveIndices_cert {α γ : Type} {encIn : α ↪ List Bool}
    {encCtx : γ ↪ List Bool} {f : α → Bool} (width : α → ℕ) (ctx : α → γ) (initOk : α → Bool)
    (test : γ → ℕ → Bool) (hw : ComputableInPolyTime width encIn encUnary)
    (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hinit : ComputableInPolyTime initOk encIn encBool)
    (htest : ComputableInPolyTime (fun q : γ × ℕ => test q.1 q.2)
      (encPair encCtx encNat) encBool)
    (hf : ∀ a, allPositiveIndices (width a) (ctx a) (initOk a) test = f a) :
    ∃ c : NativeCertificate f encIn encBool,
      c.FactorTimePolySpace (fun a => 2 ^ width a + 1) := by
  have hp1 := fst encNat (encPair encCtx encBool)
  have hp2 := snd encNat (encPair encCtx encBool)
  have hbody := hp2.fst'.prod (.bool_and' hp2.snd' (bool_or.comp'
    ((decide_eq' hp1 (.const 0)).prod (htest.comp' (hp2.fst'.prod hp1)))))
  refine ⟨_, (((IndexFold.certificate_factorTimePolySpace
    (NativeCertificate.ofPolyTime_isPolynomial (binary_two_pow.comp' hw))
    (NativeCertificate.ofPolyTime_isPolynomial (hctx.prod hinit))
    (.ofPolyTime hbody) (K := fun _ => 1)
    (B := fun a => 2 * (encCtx (ctx a)).length + 2)
    (fun _ => le_rfl) (by growth_poly)
    (fun _ _ _ => le_rfl) fun a j _ => ?_).snd.snd).mono_const 1 fun _ => by omega).congr hf⟩
  rw [length_encPair, run_allIndex_fst test]; simp only [encBool_apply, List.length_singleton]
  omega
private abbrev searchMatrixStep {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool)
    (p : ℕ × (Q × (Bool × List (List Bool)))) : Q × (Bool × List (List Bool)) :=
  let q := p.2.1
  (q, if p.2.2.1 then p.2.2 else
    let cand := listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) p.1)
    if check q cand then (true, cand) else p.2.2)
private abbrev searchMatrix {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (q : Q) : List (List Bool) :=
  (IndexFold.run (searchMatrixStep rowsOf colsOf check) (2 ^ (rowsOf q * colsOf q))
    (q, (false, listRows (rowsOf q) (colsOf q) []))).2.2.2
private theorem run_searchMatrixStep_inv {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (n : ℕ) (q : Q) :
    let out := (IndexFold.run (searchMatrixStep rowsOf colsOf check) n
      (q, (false, listRows (rowsOf q) (colsOf q) []))).2
    out.1 = q ∧ (∃ w, out.2.2 = listRows (rowsOf q) (colsOf q) w) ∧
      (out.2.1 = true → check q out.2.2 = true) ∧
      ((∃ i < n, check q (listRows (rowsOf q) (colsOf q)
        (lowBits (rowsOf q * colsOf q) i)) = true) → out.2.1 = true) := by
  induction n with
  | zero => exact ⟨rfl, ⟨[], rfl⟩, fun h => Bool.noConfusion h,
      fun ⟨_, hi, _⟩ => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨hq, ⟨w, hw⟩, hsound, hcomp⟩ := ih; dsimp only; rw [IndexFold.run_succ]
    set cur := (IndexFold.run (searchMatrixStep rowsOf colsOf check) n
      (q, (false, listRows (rowsOf q) (colsOf q) []))).2
    have hpair : IndexFold.run (searchMatrixStep rowsOf colsOf check) n
        (q, (false, listRows (rowsOf q) (colsOf q) [])) = (n, cur) :=
      Prod.ext (IndexFold.run_index _ _ _) rfl
    rw [hpair]; dsimp only [IndexFold.step, searchMatrixStep]; rw [hq]; refine ⟨rfl, ?_⟩
    cases hfound : cur.2.1
    · rw [ite_eq_right Bool.false_ne_true]
      set cand := listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) n)
      cases hcand : check q cand
      · rw [ite_eq_right Bool.false_ne_true]
        refine ⟨⟨w, hw⟩, fun h => Bool.noConfusion (hfound.symm.trans h), fun ⟨i, hi, hok⟩ => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (Bool.false_ne_true (hfound.symm.trans (hcomp ⟨i, hlt, hok⟩))).elim
        · exact Bool.noConfusion (hcand.symm.trans hok)
      · rw [ite_eq_left rfl]; exact ⟨⟨_, rfl⟩, fun _ => hcand, fun _ => rfl⟩
    · rw [ite_eq_left rfl]; exact ⟨⟨w, hw⟩, fun _ => hsound hfound, fun _ => hfound⟩
private theorem searchMatrix_sound {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (q : Q)
    (hex : ∃ M : Fin (rowsOf q) → BitString (colsOf q),
      check q (List.ofFn fun r => List.ofFn (M r)) = true) :
    check q (searchMatrix rowsOf colsOf check q) = true := by
  obtain ⟨M, hM⟩ := hex
  have hinv := run_searchMatrixStep_inv rowsOf colsOf check (2 ^ (rowsOf q * colsOf q)) q
  let k : Fin (2 ^ (rowsOf q * colsOf q)) := equivFin (rowsOf q * colsOf q) (blocksEquiv.symm M)
  have hcand : listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) k.val) =
      List.ofFn (fun r => List.ofFn (M r)) := by
    rw [lowBits_eq_ofFn_equivFin_symm _ k, Equiv.symm_apply_apply, listRows_ofFn,
      block_blocksEquiv_symm]
  exact hinv.2.2.1 (hinv.2.2.2 ⟨k.val, k.isLt, by rwa [hcand]⟩)
private theorem searchMatrix_cert {α Q : Type} {encIn : α ↪ List Bool} {encQ : Q ↪ List Bool}
    {rowsOf colsOf wCheck : Q → ℕ} {qOf : α → Q} {check : Q → List (List Bool) → Bool}
    (hq : ComputableInPolyTime qOf encIn encQ) (hrows : ComputableInPolyTime rowsOf encQ encUnary)
    (hcols : ComputableInPolyTime colsOf encQ encUnary)
    (hCheck : ∃ c : NativeCertificate (fun x : Q × List (List Bool) => check x.1 x.2)
      (encPair encQ (encList encBits)) encBool,
      c.FactorTimePolySpace (fun x => 2 ^ wCheck x.1 + 1)) :
    ∃ c : NativeCertificate
        (fun a => searchMatrix rowsOf colsOf check (qOf a)) encIn (encList encBits),
      c.FactorTimePolySpace
        (fun a => (2 ^ (rowsOf (qOf a) * colsOf (qOf a)) + 1) * (2 ^ wCheck (qOf a) + 1)) := by
  obtain ⟨_, hCheck⟩ := hCheck
  let encPay := encPair encBool (encList encBits)
  let encSt := encPair encQ encPay; let encFull := encPair encNat encSt
  have hra := hrows.comp hq; have hca := hcols.comp hq; have hrcQ := unary_mul' hrows hcols
  have hinit := hq.prod ((ComputableInPolyTime.const (encOut := encBool) false).prod
    (bitsRowsWithInput hra hca (.const [])))
  have hp2 := snd encNat encSt; have hpQ := hp2.fst'; have hpPay := hp2.snd'
  have hcand := bitsRowsWithInput (hrows.comp hpQ) (hcols.comp hpQ)
    (bitsLow (hrcQ.comp hpQ) (fst encNat encSt))
  have hx1 := fst (encPair encPay (encList encBits)) encBool
  have hx2 := snd (encPair encPay (encList encBits)) encBool
  have hSel := hx1.fst'.fst'.ite hx1.fst'
    (hx2.ite ((ComputableInPolyTime.const (encOut := encBool) true).prod hx1.snd') hx1.fst')
  have hPayStep := (((NativeCertificate.FactorTimePolySpace.ofPolyTime (hpPay.prod hcand)).mono
      fun _ => Nat.le_add_left 1 _).prod_same
    (hCheck.comp_polyPre (hpQ.prod hcand) fun _ => Nat.le_add_left 1 _)).comp_ofPolyTime
    (fun _ => Nat.le_add_left 1 _) hSel
  have hStep := (((NativeCertificate.FactorTimePolySpace.ofPolyTime hpQ).mono
      fun _ => Nat.le_add_left 1 _).prod_same hPayStep).congr
    (f' := searchMatrixStep rowsOf colsOf check) (fun _ => rfl)
  let B (a : α) : ℕ :=
    2 * (encQ (qOf a)).length + 1 + (3 + rowsOf (qOf a) * (2 * colsOf (qOf a) + 1))
  have hBP : PolyBounded (fun a => (encIn a).length) B := by growth_poly
  have hB (a : α) (j : ℕ) (_ : j ≤ 2 ^ (rowsOf (qOf a) * colsOf (qOf a))) :
      (encSt (IndexFold.run (searchMatrixStep rowsOf colsOf check) j
        (qOf a, (false, listRows (rowsOf (qOf a)) (colsOf (qOf a)) []))).2).length ≤ B a := by
    obtain ⟨hq_eq, ⟨w, hw⟩, -, -⟩ := run_searchMatrixStep_inv rowsOf colsOf check j (qOf a)
    enc_len [encSt, encPay, List.length_singleton, hq_eq, hw, length_encList_listRows, B]
  exact ⟨_, (IndexFold.certificate_factorTimePolySpace
    (NativeCertificate.ofPolyTime_isPolynomial (binary_two_pow.comp (hrcQ.comp hq)))
    (NativeCertificate.ofPolyTime_isPolynomial hinit) hStep
    (K := fun a => 2 ^ wCheck (qOf a) + 1) (B := B)
    (fun _ => Nat.le_add_left 1 _) hBP
    (fun a j _ => Nat.le_of_eq (congrArg (fun x => 2 ^ wCheck x + 1)
      (run_searchMatrixStep_inv rowsOf colsOf check j (qOf a)).1)) hB).snd.snd.snd⟩

/-! ### Polynomial-time and streaming checkers -/
private theorem checkMatrixShape_polyTime {α : Type} {encIn : α ↪ List Bool} (r c : α → ℕ)
    (M : α → List (List Bool)) (hr : ComputableInPolyTime r encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary)
    (hM : ComputableInPolyTime M encIn (encList encBits)) :
    ComputableInPolyTime (fun a => ((M a).length == r a) && (M a).all fun row => row.length == c a)
      encIn encBool :=
  .bool_and' (.beq ((length_list encBits).comp hM) hr)
    (allWithInput hM (.beq (length_bits_comp (snd encIn encBits))
      (hc.comp (fst encIn encBits))))
private theorem list_eq_ofFn_ofList {r c : ℕ} {M : List (List Bool)}
    (hlen : M.length = r) (hrows : ∀ row ∈ M, row.length = c) :
    M = List.ofFn fun i : Fin r => List.ofFn (ofList c (M.getD i.val [])) := by
  apply List.ext_getElem (by simp only [List.length_ofFn, hlen]); intro i hi _
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, ofFn_ofList (hrows _ (List.getElem_mem hi))]
private theorem ofList_getD_ofFn {r c : ℕ} (A : Fin r → BitString c) (i : Fin r) :
    ofList c ((List.ofFn fun k => List.ofFn (A k)).getD i.val []) = A i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some, ofList_ofFn]
private abbrev BiasHdr := ℕ × ℕ × ℕ × ℕ
private abbrev BiasQ := BiasHdr × List (List Bool)
private abbrev encBiasHdr : BiasHdr ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat encNat))
private abbrev encBiasQ : BiasQ ↪ List Bool := encPair encBiasHdr (encList encBits)

/-- Streaming small-bias shift checker ([OpenAI2026ETH], Lemma 6.1, eq. (6.2)): checks that
`shifts` has `d` rows of length `ell` and `|d - 2 * odd(b)| * maxBiasDen ≤ maxBiasNum * d` on all
nonzero masks `b ∈ {0, 1} ^ ell \ {0}`, returning `false` on any shape or bias violation. -/
def checkSmallBiasShifts (ell d maxBiasNum maxBiasDen : ℕ) (shifts : List (List Bool)) : Bool :=
  let (_, _, ok) := IndexFold.run
    (fun (idx, ((ell, d, maxBiasNum, maxBiasDen), shifts), ok) =>
      (((ell, d, maxBiasNum, maxBiasDen), shifts), ok && (decide (idx = 0) ||
        let odd := shifts.countP fun row =>
          listDot row (lowBits ell idx)
        let diff := (d - 2 * odd) + (2 * odd - d)
        decide (diff * maxBiasDen ≤ maxBiasNum * d))))
    (2 ^ ell) (((ell, d, maxBiasNum, maxBiasDen), shifts),
      (shifts.length == d) && shifts.all (fun row => row.length == ell))
  ok
/-- Exact characterization of `checkSmallBiasShifts` for `d ≥ 1` and `0 < maxBiasDen`. -/
theorem checkSmallBiasShifts_eq_true_iff {ell d maxBiasNum maxBiasDen : ℕ} [NeZero d]
    (hden : 0 < maxBiasDen) (shifts : List (List Bool)) :
    checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true ↔
      shifts.length = d ∧ (∀ row ∈ shifts, row.length = ell) ∧
        IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen)
          ((uniformOfFintype (Fin d)).map fun j => ofList ell (shifts.getD j.val [])) := by
  have hd : 0 < d := NeZero.pos d; have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdenR : (0 : ℝ) < maxBiasDen := by exact_mod_cast hden
  rw [show checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts =
    allPositiveIndices ((fun q : BiasQ => q.1.1) ((ell, d, maxBiasNum, maxBiasDen), shifts))
      ((ell, d, maxBiasNum, maxBiasDen), shifts)
      ((shifts.length == d) && shifts.all (fun row => row.length == ell))
      (fun q idx =>
        let bits := lowBits q.1.1 idx
        let odd := q.2.countP (fun row => listDot row bits)
        let diff := (q.1.2.1 - 2 * odd) + (2 * odd - q.1.2.1)
        decide (diff * q.1.2.2.2 ≤ q.1.2.2.1 * q.1.2.1)) from rfl,
    allPositiveIndices_lowBits_eq_true_iff (fun q : BiasQ => q.1.1) _ _
      (fun q bits =>
        let odd := q.2.countP (fun row => listDot row bits)
        let diff := (q.1.2.1 - 2 * odd) + (2 * odd - q.1.2.1)
        decide (diff * q.1.2.2.2 ≤ q.1.2.2.1 * q.1.2.1))]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  set s : Fin d → Fin ell → Bool := fun j => ofList ell (shifts.getD j.val [])
  have hodd_eq (hlen : shifts.length = d) (hrows : ∀ row ∈ shifts, row.length = ell)
      (b : BitString ell) : shifts.countP (fun row => listDot row (List.ofFn b)) =
        #{j : Fin d | parityOn {i : Fin ell | b i = true} (s j) = true} := by
    nth_rw 1 [list_eq_ofFn_ofList hlen hrows]
    rw [List.countP_ofFn]; congr 1; ext j
    simp only [mem_filter, mem_univ, true_and]; rw [listDot_ofFn, dotProduct_eq_parityOn]
  have hbias_iff (S : Finset (Fin ell)) :
      ((d - 2 * #{j : Fin d | parityOn S (s j) = true}) +
        (2 * #{j : Fin d | parityOn S (s j) = true} - d)) * maxBiasDen ≤ maxBiasNum * d ↔
        |bias ((uniformOfFintype (Fin d)).map s) S| ≤ (maxBiasNum : ℝ) / maxBiasDen := by
    have hcast (a b : ℕ) : (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
      rcases le_total a b with h | h <;>
        simp only [Nat.sub_eq_zero_of_le h, zero_add, add_zero, Nat.cast_sub h]
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
      · exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))).symm
    rw [← @Nat.cast_le ℝ, Nat.cast_mul, Nat.cast_mul, hcast, Nat.cast_mul,
      Nat.cast_ofNat, ← sum_chi_eq S s, bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card,
      Fintype.card_fin, abs_div, abs_of_pos hdR, div_le_div_iff₀ hdR hdenR]
  refine ⟨fun ⟨⟨hlen, hrows⟩, hall⟩ => ⟨hlen, hrows, fun S hS => ?_⟩,
    fun ⟨hlen, hrows, hbias⟩ => ⟨⟨hlen, hrows⟩, fun b hb0 => ?_⟩⟩
  · let b : BitString ell := fun i => decide (i ∈ S)
    have hb0 : b ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := hS; intro h0; have := congrFun h0 i₀
      simp only [b, hi₀, decide_true] at this; exact Bool.false_ne_true this.symm
    have htest := hall b hb0
    have hS_eq : ({i : Fin ell | b i = true} : Finset (Fin ell)) = S := by
      ext i; simp only [b, mem_filter, mem_univ, decide_eq_true_eq, true_and]
    rw [decide_eq_true_eq, hodd_eq hlen hrows b, hS_eq] at htest; exact (hbias_iff S).1 htest
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb0; rw [decide_eq_true_eq, hodd_eq hlen hrows b]
    exact (hbias_iff _).2 (hbias _ ⟨i₀, mem_filter.mpr ⟨mem_univ i₀,
      Bool.eq_true_of_not_eq_false hi₀⟩⟩)
private theorem checkSmallBiasShifts_cert_aux :
    ∃ c : NativeCertificate
        (fun q : BiasQ => checkSmallBiasShifts q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
        encBiasQ encBool,
      c.FactorTimePolySpace (fun q => 2 ^ q.1.1 + 1) := by
  have hq1 := fst encBiasHdr (encList encBits); have hq2 := snd encBiasHdr (encList encBits)
  have hellQ := hq1.fst'; have hdQ := hq1.snd'.fst'
  have hshape := checkMatrixShape_polyTime (encIn := encBiasQ) (fun q => q.1.2.1) (fun q => q.1.1)
    (fun q => q.2) hdQ hellQ hq2
  let testFn (q : BiasQ) (idx : ℕ) : Bool :=
    let odd := q.2.countP (fun row => listDot row (lowBits q.1.1 idx))
    let diff := (q.1.2.1 - 2 * odd) + (2 * odd - q.1.2.1)
    decide (diff * q.1.2.2.2 ≤ q.1.2.2.1 * q.1.2.1)
  have hp1 := fst encBiasQ encNat; have hp2 := snd encBiasQ encNat
  have hhdrP := hq1.comp' hp1; have hdP := hdQ.comp' hp1
  have hr1 := fst (encPair encBiasQ encNat) encBits
  have hr2 := snd (encPair encBiasQ encNat) encBits
  have hodd := countPWithInput (test := fun p row => listDot row (lowBits p.1.1.1 p.2))
    (hq2.comp' hp1) (bitsListDot hr2 (bitsLow (hellQ.comp' (hp1.comp' hr1)) (hp2.comp' hr1)))
  have h2odd := unary_mul' (.const 2) hodd
  have hdiff := unary_add' (.unary_sub' hdP h2odd) (.unary_sub' h2odd hdP)
  have htest := binary_le.comp ((binary_mul' (unary_to_binary.comp hdiff)
    hhdrP.snd'.snd'.snd').prod (binary_mul' hhdrP.snd'.snd'.fst'
      (unary_to_binary.comp hdP)))
  exact allPositiveIndices_cert (fun q => q.1.1) id
    (fun q => (q.2.length == q.1.2.1) && q.2.all (fun row => row.length == q.1.1)) testFn
    hellQ (.of_eq fun _ => rfl) hshape htest fun _ => rfl
/-- Native `ComputableInO` certificate for `checkSmallBiasShifts`. -/
theorem checkSmallBiasShifts_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encQ := encPair (encPair encUnary (encPair encUnary (encPair encNat encNat)))
        (encList encBits)
      ComputableInO (fun ((ell, d, maxBiasNum, maxBiasDen), shifts) =>
          checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts) encQ encBool
        (fun q => let ((ell, _), _) := q; (2 ^ ell + 1) * pT (encQ q).length)
        (fun q => pS (encQ q).length) :=
  let ⟨_, h⟩ := checkSmallBiasShifts_cert_aux
  let ⟨p, hp, hc⟩ := h.exists_poly_computableInO; ⟨p, p, hp, hp, hc⟩
/-- Plain polynomial-time certificate for `checkSmallBiasShifts` when `2 ^ ell` is poly-bounded. -/
theorem checkSmallBiasShifts_polyTime {α : Type} {encIn : α ↪ List Bool}
    {ell d maxBiasNum maxBiasDen : α → ℕ} {shifts : α → List (List Bool)}
    (hell : ComputableInPolyTime ell encIn encUnary) (hd : ComputableInPolyTime d encIn encUnary)
    (hnum : ComputableInPolyTime maxBiasNum encIn encNat)
    (hden : ComputableInPolyTime maxBiasDen encIn encNat)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hq : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ ell a)) :
    ComputableInPolyTime
      (fun a => checkSmallBiasShifts (ell a) (d a) (maxBiasNum a) (maxBiasDen a) (shifts a))
      encIn encBool := by
  obtain ⟨_, h⟩ := checkSmallBiasShifts_cert_aux
  exact (h.comp_polyPre ((hell.prod (hd.prod (hnum.prod hden))).prod hshifts)
    fun _ => Nat.le_add_left 1 _).polyTime (hq.add (.const 1))
/-- Specialization of `checkSmallBiasShifts_polyTime` when `2 ^ ell ≤ 2 * m + 1`. -/
theorem checkSmallBiasShifts_polyTime_of_two_pow_le {α : Type} {encIn : α ↪ List Bool}
    {m ell d maxBiasNum maxBiasDen : α → ℕ} {shifts : α → List (List Bool)}
    (hm : ComputableInPolyTime m encIn encUnary) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hnum : ComputableInPolyTime maxBiasNum encIn encNat)
    (hden : ComputableInPolyTime maxBiasDen encIn encNat)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hle : ∀ a, 2 ^ ell a ≤ 2 * m a + 1) :
    ComputableInPolyTime
      (fun a => checkSmallBiasShifts (ell a) (d a) (maxBiasNum a) (maxBiasDen a) (shifts a))
      encIn encBool :=
  checkSmallBiasShifts_polyTime hell hd hnum hden hshifts
    ((((PolyBounded.const 2).mul (polyBounded hm)).add (.const 1)).mono hle)
private abbrev LocalHdr := ℕ × ℕ × ℕ
private abbrev LocalQ := LocalHdr × List (List Bool)
/-- Parameters `(c, d, minDist)` of a local check matrix, all in unary: the row count `c`, the row
length `d` and the required minimum distance `minDist`. The unary `c` is framed, then the unary `d`
is framed, then the unary `minDist` follows. -/
abbrev encLocalCodeParams : ℕ × ℕ × ℕ ↪ List Bool := encPair encUnary (encPair encUnary encUnary)
private abbrev encLocalQ : LocalQ ↪ List Bool := encPair encLocalCodeParams (encList encBits)
/-- Streaming local-code distance checker ([OpenAI2026ETH], Lemma 6.1) via `IndexFold.run`:
checks that `H0` has `c` rows of length `d` and every nonzero `w ∈ {0, 1} ^ d \ {0}` in its
`GF(2)` kernel has Hamming weight at least `minDist`, returning `false` on any violation. -/
def checkLocalCodeDistance (c d minDist : ℕ) (H0 : List (List Bool)) : Bool :=
  let (_, _, ok) := IndexFold.run
    (fun (idx, ((c, d, minDist), H0), ok) =>
      (((c, d, minDist), H0), ok && (decide (idx = 0) ||
        let w := lowBits d idx
        !(H0.all fun row => !listDot row w) ||
          decide (minDist ≤ w.count true))))
    (2 ^ d) (((c, d, minDist), H0), (H0.length == c) && H0.all (fun row => row.length == d))
  ok
/-- Exact characterization of `checkLocalCodeDistance`. -/
theorem checkLocalCodeDistance_eq_true_iff (c d minDist : ℕ) (H0 : List (List Bool)) :
    checkLocalCodeDistance c d minDist H0 = true ↔
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
        ∀ w : Fin d → Bool, w ≠ 0 →
          (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → minDist ≤ weight w := by
  rw [show checkLocalCodeDistance c d minDist H0 =
    allPositiveIndices ((fun q : LocalQ => q.1.2.1) ((c, d, minDist), H0)) ((c, d, minDist), H0)
      ((H0.length == c) && H0.all (fun row => row.length == d))
      (fun q idx =>
        let w := lowBits q.1.2.1 idx
        !(q.2.all (fun row => !listDot row w)) || decide (q.1.2.2 ≤ w.count true)) from rfl,
    allPositiveIndices_lowBits_eq_true_iff (fun q : LocalQ => q.1.2.1) _ _
      (fun q w => !(q.2.all (fun row => !listDot row w)) || decide (q.1.2.2 ≤ w.count true))]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  have hker_iff (hlen : H0.length = c) (hrows : ∀ row ∈ H0, row.length = d) (w : BitString d) :
      H0.all (fun row => !listDot row (List.ofFn w)) = true ↔
        ∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false := by
    nth_rw 1 [list_eq_ofFn_ofList hlen hrows]
    simp only [List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
      Bool.not_eq_true', listDot_ofFn]
  refine ⟨fun ⟨⟨hlen, hrows⟩, hall⟩ => ⟨hlen, hrows, fun w hw0 hker => ?_⟩,
    fun ⟨hlen, hrows, hdist⟩ => ⟨⟨hlen, hrows⟩, fun w hw0 => ?_⟩⟩
  · have htest := hall w hw0
    rw [(hker_iff hlen hrows w).2 hker] at htest
    simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq, count_true_ofFn] using htest
  · by_cases hkerList : H0.all (fun row => !listDot row (List.ofFn w)) = true
    · rw [hkerList, Bool.not_true, Bool.false_or, decide_eq_true_eq, count_true_ofFn]
      exact hdist w hw0 ((hker_iff hlen hrows w).1 hkerList)
    · rw [Bool.eq_false_iff.mpr hkerList]; rfl
private theorem checkLocalCodeDistance_cert_aux :
    ∃ c : NativeCertificate
        (fun q : LocalQ => checkLocalCodeDistance q.1.1 q.1.2.1 q.1.2.2 q.2)
        encLocalQ encBool,
      c.FactorTimePolySpace (fun q => 2 ^ q.1.2.1 + 1) := by
  have hq1 := fst encLocalCodeParams (encList encBits)
  have hq2 := snd encLocalCodeParams (encList encBits)
  have hdQ := hq1.snd'.fst'
  have hshape := checkMatrixShape_polyTime (encIn := encLocalQ) (fun q => q.1.1)
    (fun q => q.1.2.1) (fun q => q.2) hq1.fst' hdQ hq2
  let testFn (q : LocalQ) (idx : ℕ) : Bool :=
    let w := lowBits q.1.2.1 idx
    !(q.2.all (fun row => !listDot row w)) || decide (q.1.2.2 ≤ w.count true)
  have hp1 := fst encLocalQ encNat; have hp2 := snd encLocalQ encNat
  have hw := bitsLow (hdQ.comp' hp1) hp2; have hr1 := fst (encPair encLocalQ encNat) encBits
  have hr2 := snd (encPair encLocalQ encNat) encBits
  have hall := allWithInput (test := fun p row => !listDot row (lowBits p.1.1.2.1 p.2))
    (hq2.comp' hp1) (bool_not.comp' (bitsListDot hr2 (hw.comp' hr1)))
  have htest := bool_or.comp ((bool_not.comp hall).prod
    (unary_le' (hq1.snd'.snd'.comp hp1) (bitsCountWithInput hw (.const true))))
  exact allPositiveIndices_cert (fun q => q.1.2.1) id
    (fun q => (q.2.length == q.1.1) && q.2.all (fun row => row.length == q.1.2.1)) testFn
    hdQ (.of_eq fun _ => rfl) hshape htest fun _ => rfl
/-- Native `ComputableInO` certificate for `checkLocalCodeDistance`. -/
theorem checkLocalCodeDistance_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encQ := encPair encLocalCodeParams (encList encBits)
      ComputableInO (fun ((c, d, minDist), H0) =>
          checkLocalCodeDistance c d minDist H0) encQ encBool
        (fun q => let ((_, d, _), _) := q; (2 ^ d + 1) * pT (encQ q).length)
        (fun q => pS (encQ q).length) :=
  let ⟨_, h⟩ := checkLocalCodeDistance_cert_aux
  let ⟨p, hp, hc⟩ := h.exists_poly_computableInO; ⟨p, p, hp, hp, hc⟩
/-! ### Sequential `IndexFold` searchers -/
/-- Sequential `IndexFold` search ([OpenAI2026ETH], Lemma 6.1) over `0 .. 2 ^ (d * ell) - 1`,
returning the first `d × ell` shift table passing `checkSmallBiasShifts`, or the total all-`false`
fallback `listRows d ell []` when no candidate passes. -/
def findSmallBiasShifts (ell d maxBiasNum maxBiasDen : ℕ) : List (List Bool) :=
  let (_, _, _, rows) := IndexFold.run
    (fun (idx, (ell, d, maxBiasNum, maxBiasDen), (found, best)) =>
      ((ell, d, maxBiasNum, maxBiasDen), if found then (found, best) else
        let cand := listRows d ell (lowBits (d * ell) idx)
        if checkSmallBiasShifts ell d maxBiasNum maxBiasDen cand then (true, cand)
        else (found, best)))
    (2 ^ (d * ell)) ((ell, d, maxBiasNum, maxBiasDen), (false, listRows d ell []))
  rows
/-- Soundness of `findSmallBiasShifts` for `d ≥ 1` and `0 < maxBiasDen` when a witness exists. -/
theorem isSmallBias_findSmallBiasShifts {ell d maxBiasNum maxBiasDen : ℕ} [NeZero d]
    (hden : 0 < maxBiasDen) (hex : ∃ s : Fin d → Fin ell → Bool,
      IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen) ((uniformOfFintype (Fin d)).map s)) :
    let shifts := findSmallBiasShifts ell d maxBiasNum maxBiasDen
    checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true ∧
      shifts.length = d ∧ (∀ row ∈ shifts, row.length = ell) ∧
      IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen)
        ((uniformOfFintype (Fin d)).map fun j => ofList ell (shifts.getD j.val [])) := by
  obtain ⟨s, hs⟩ := hex
  have hcheck : checkSmallBiasShifts ell d maxBiasNum maxBiasDen
      (findSmallBiasShifts ell d maxBiasNum maxBiasDen) = true := by
    apply searchMatrix_sound (fun q => q.2.1) (fun q => q.1) (fun q => checkSmallBiasShifts
      q.1 q.2.1 q.2.2.1 q.2.2.2) (ell, d, maxBiasNum, maxBiasDen)
    refine ⟨s, (checkSmallBiasShifts_eq_true_iff hden _).2 ⟨List.length_ofFn, by
      simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, List.length_ofFn,
        implies_true], ?_⟩⟩
    convert hs using 2; funext j; exact ofList_getD_ofFn s j
  exact ⟨hcheck, (checkSmallBiasShifts_eq_true_iff hden _).1 hcheck⟩
private theorem findSmallBiasShifts_cert_aux {α : Type} {encIn : α ↪ List Bool}
    (ell d num den : α → ℕ) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hnum : ComputableInPolyTime num encIn encNat)
    (hden : ComputableInPolyTime den encIn encNat) :
    ∃ c : NativeCertificate
        (fun a => findSmallBiasShifts (ell a) (d a) (num a) (den a)) encIn (encList encBits),
      c.FactorTimePolySpace (fun a => (2 ^ (d a * ell a) + 1) * (2 ^ ell a + 1)) := by
  obtain ⟨_, h⟩ := searchMatrix_cert (wCheck := fun q : BiasHdr => q.1)
    (check := fun q : BiasHdr => checkSmallBiasShifts q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hell.prod (hd.prod (hnum.prod hden)))
    (snd encUnary (encPair encUnary (encPair encNat encNat))).fst'
    (fst encUnary (encPair encUnary (encPair encNat encNat)))
    checkSmallBiasShifts_cert_aux
  exact ⟨_, h.congr fun _ => rfl⟩
/-- Native `ComputableInO` certificate for `findSmallBiasShifts`. -/
theorem findSmallBiasShifts_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encH := encPair encUnary (encPair encUnary (encPair encNat encNat))
      ComputableInO
        (fun (ell, d, maxBiasNum, maxBiasDen) => findSmallBiasShifts ell d maxBiasNum maxBiasDen)
        encH (encList encBits)
        (fun p => let (ell, d, _, _) := p; (2 ^ (d * ell) + 1) * (2 ^ ell + 1) * pT (encH p).length)
        (fun p => pS (encH p).length) := by
  have hp2 := snd encUnary (encPair encUnary (encPair encNat encNat))
  obtain ⟨_, h⟩ := findSmallBiasShifts_cert_aux (encIn := encBiasHdr)
    (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2.1) (fun p => p.2.2.2)
    (fst encUnary (encPair encUnary (encPair encNat encNat))) hp2.fst' hp2.snd'.fst' hp2.snd'.snd'
  obtain ⟨p, hp, hc⟩ := h.exists_poly_computableInO; exact ⟨p, p, hp, hp, hc⟩
/-- Sequential `IndexFold` search ([OpenAI2026ETH], Lemma 6.1) over `0 .. 2 ^ (c * d) - 1`,
returning the first `c × d` check matrix passing `checkLocalCodeDistance`, or the total all-`false`
fallback `listRows c d []` when no candidate passes. -/
def findLocalCheckMatrix (c d minDist : ℕ) : List (List Bool) :=
  let (_, _, _, rows) := IndexFold.run
    (fun (idx, (c, d, minDist), (found, best)) =>
      ((c, d, minDist), if found then (found, best) else
        let cand := listRows c d (lowBits (c * d) idx)
        if checkLocalCodeDistance c d minDist cand then (true, cand) else (found, best)))
    (2 ^ (c * d)) ((c, d, minDist), (false, listRows c d []))
  rows
/-- Soundness of `findLocalCheckMatrix` when a check matrix of distance `minDist` exists. -/
theorem weight_le_of_findLocalCheckMatrix {c d minDist : ℕ}
    (hex : ∃ A : Fin c → Fin d → Bool,
      ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → minDist ≤ weight w) :
    let H0 := findLocalCheckMatrix c d minDist
    checkLocalCodeDistance c d minDist H0 = true ∧
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
      ∀ w : Fin d → Bool, w ≠ 0 →
        (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → minDist ≤ weight w := by
  obtain ⟨A, hA⟩ := hex
  have hcheck : checkLocalCodeDistance c d minDist (findLocalCheckMatrix c d minDist) = true := by
    apply searchMatrix_sound (fun q => q.1) (fun q => q.2.1)
      (fun q cand => checkLocalCodeDistance q.1 q.2.1 q.2.2 cand) (c, d, minDist)
    refine ⟨A, (checkLocalCodeDistance_eq_true_iff c d minDist _).2 ⟨List.length_ofFn, by
      simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, List.length_ofFn,
        implies_true], ?_⟩⟩
    intro w hw0 hker; exact hA w hw0 fun i => by simpa only [ofList_getD_ofFn] using hker i
  exact ⟨hcheck, (checkLocalCodeDistance_eq_true_iff c d minDist _).1 hcheck⟩
private theorem findLocalCheckMatrix_cert_aux {α : Type} {encIn : α ↪ List Bool}
    (c d md : α → ℕ) (hc : ComputableInPolyTime c encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hmin : ComputableInPolyTime md encIn encUnary) :
    ∃ cert : NativeCertificate
        (fun a => findLocalCheckMatrix (c a) (d a) (md a)) encIn (encList encBits),
      cert.FactorTimePolySpace (fun a => (2 ^ (c a * d a) + 1) * (2 ^ d a + 1)) := by
  obtain ⟨_, h⟩ := searchMatrix_cert (wCheck := fun q : LocalHdr => q.2.1)
    (check := fun q : LocalHdr => checkLocalCodeDistance q.1 q.2.1 q.2.2) (hc.prod (hd.prod hmin))
    (fst encUnary (encPair encUnary encUnary)) (snd encUnary (encPair encUnary encUnary)).fst'
    checkLocalCodeDistance_cert_aux
  exact ⟨_, h.congr fun _ => rfl⟩
/-- Native `ComputableInO` certificate for `findLocalCheckMatrix`. -/
theorem findLocalCheckMatrix_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encH := encLocalCodeParams
      ComputableInO (fun (c, d, minDist) => findLocalCheckMatrix c d minDist)
        encH (encList encBits)
        (fun p => let (c, d, _) := p; (2 ^ (c * d) + 1) * (2 ^ d + 1) * pT (encH p).length)
        (fun p => pS (encH p).length) := by
  have hp2 := snd encUnary (encPair encUnary encUnary)
  obtain ⟨_, h⟩ := findLocalCheckMatrix_cert_aux (encIn := encLocalCodeParams)
    (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2)
    (fst encUnary (encPair encUnary encUnary)) hp2.fst' hp2.snd'
  obtain ⟨p, hp, hc⟩ := h.exists_poly_computableInO; exact ⟨p, p, hp, hp, hc⟩

/-! ### Shortened Tanner parity-check matrix builder -/
private def edgeEmbedding {m ell d : ℕ} (hd : 0 < d) (hm : m ≤ 2 ^ ell * d) :
    Fin m ↪ (Fin ell → Bool) × Fin d where
  toFun e := ((equivFin ell).symm ⟨e.val / d, (Nat.div_lt_iff_lt_mul hd).2 (e.isLt.trans_le hm)⟩,
    ⟨e.val % d, Nat.mod_lt e.val hd⟩)
  inj' e₁ e₂ h := by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    have hdiv : e₁.val / d = e₂.val / d := congrArg Fin.val ((equivFin ell).symm.injective h₁)
    have hmod : e₁.val % d = e₂.val % d := congrArg Fin.val h₂
    ext; rw [← Nat.div_add_mod e₁.val d, ← Nat.div_add_mod e₂.val d, hdiv, hmod]

/-- Construct the `2 * 2 ^ ell * c` parity-check rows of length `m` for the shortened Tanner code
([OpenAI2026ETH], Lemma 6.1, p. 42), matching `Cslib.BitString.Tanner.shortRow`. Fills entries with
`false` when `d = 0` and pads/truncates missing `shifts` or `H0` entries with `false`. -/
def buildShortenedTannerRows (m ell d c : ℕ) (shifts H0 : List (List Bool)) : List (List Bool) :=
  [false, true].flatMap fun side =>
    (List.range (2 ^ ell)).flatMap fun vIdx =>
      let vBits := lowBits ell vIdx
      (List.range c).map fun i =>
        let aRow := H0.getD i []
        (List.range m).map fun e =>
          if d == 0 then false else
            let uBits := lowBits ell (e / d); let port := e % d
            let sBits := listRow ell 0 (shifts.getD port [])
            let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
            if !(endBits.zipWith Bool.xor vBits).any id then aRow.getD port false else false

@[simp] theorem length_buildShortenedTannerRows (m ell d c : ℕ) (shifts H0 : List (List Bool)) :
    (buildShortenedTannerRows m ell d c shifts H0).length = 2 * 2 ^ ell * c := by
  simp only [buildShortenedTannerRows, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_nil, List.length_flatMap, List.length_map, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]; ring
theorem length_mem_buildShortenedTannerRows {m ell d c : ℕ} {shifts H0 : List (List Bool)}
    {row : List Bool} (hrow : row ∈ buildShortenedTannerRows m ell d c shifts H0) :
    row.length = m := by
  simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_range, List.mem_map] at hrow
  obtain ⟨_, _, _, _, _, _, rfl⟩ := hrow; simp only [List.length_map, List.length_range]
private theorem xor_any_eq_false_iff {ell : ℕ} (x y : BitString ell) :
    ((List.ofFn x).zipWith Bool.xor (List.ofFn y)).any id = false ↔ x = y := by
  have hxor (a b : Bool) : (a ^^ b) = false ↔ a = b := by cases a <;> cases b <;> decide
  rw [← ofFn_add, List.any_eq_false]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, id_eq,
    Bool.not_eq_true, Pi.add_apply, Bool.add_eq_xor, hxor, funext_iff]
private theorem buildRow_eq_ofFn_shortRow {m ell d c : ℕ} (hd : 0 < d) (hm : m ≤ 2 ^ ell * d)
    (shifts H0 : List (List Bool)) (side : Bool) (v : Fin (2 ^ ell)) (i : Fin c) :
    (List.range m).map (fun e =>
      if d == 0 then false else
        let uBits := lowBits ell (e / d); let port := e % d
        let sBits := listRow ell 0 (shifts.getD port [])
        let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
        if !(endBits.zipWith Bool.xor (lowBits ell v.val)).any id then
          (H0.getD i.val []).getD port false else false) =
      List.ofFn (Tanner.shortRow (fun j : Fin d => ofList ell (shifts.getD j.val []))
        (fun r : Fin c => ofList d (H0.getD r.val []))
        (edgeEmbedding hd hm) (side, (equivFin ell).symm v, i)) := by
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_ofFn])
  intro e he _; simp only [List.length_map, List.length_range] at he; let ef : Fin m := ⟨e, he⟩
  set endPt := if side then (edgeEmbedding hd hm ef).1 +
      ofList ell (shifts.getD (edgeEmbedding hd hm ef).2.val []) else (edgeEmbedding hd hm ef).1
  have hu : lowBits ell (e / d) = List.ofFn (edgeEmbedding hd hm ef).1 :=
    lowBits_eq_ofFn_equivFin_symm _ ⟨e / d, (Nat.div_lt_iff_lt_mul hd).2 (he.trans_le hm)⟩
  have hs : listRow ell 0 (shifts.getD (e % d) []) =
      List.ofFn (ofList ell (shifts.getD (edgeEmbedding hd hm ef).2.val [])) :=
    listRow_zero ell (shifts.getD (e % d) [])
  have hend : (if side then (lowBits ell (e / d)).zipWith Bool.xor
        (listRow ell 0 (shifts.getD (e % d) [])) else lowBits ell (e / d)) = List.ofFn endPt := by
    rw [hu, hs]; cases side <;> simp only [endPt, ↓reduceIte, Bool.false_eq_true, ofFn_add]
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, beq_false_of_ne hd.ne',
    Bool.false_eq_true, ↓reduceIte, hend, lowBits_eq_ofFn_equivFin_symm _ v, Tanner.shortRow]
  change (if !((List.ofFn endPt).zipWith Bool.xor (List.ofFn ((equivFin ell).symm v))).any id then
      (H0.getD i.val []).getD (e % d) false else false) =
    if endPt = (equivFin ell).symm v then ofList d (H0.getD i.val []) (edgeEmbedding hd hm ef).2
      else false
  by_cases heq : endPt = (equivFin ell).symm v
  · rw [(xor_any_eq_false_iff _ _).2 heq]; simp only [heq, Bool.not_false, ↓reduceIte]; rfl
  · rw [Bool.eq_true_of_not_eq_false fun h => heq ((xor_any_eq_false_iff _ _).1 h)]
    simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
theorem count_true_mem_buildShortenedTannerRows_le {m ell d c : ℕ} (hd : 0 < d)
    (hm : m ≤ 2 ^ ell * d) {shifts H0 : List (List Bool)} {row : List Bool}
    (hrow : row ∈ buildShortenedTannerRows m ell d c shifts H0) : row.count true ≤ d := by
  simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_range, List.mem_map] at hrow
  obtain ⟨side, _, vIdx, hv, i, hi, rfl⟩ := hrow
  rw [buildRow_eq_ofFn_shortRow hd hm shifts H0 side ⟨vIdx, hv⟩ ⟨i, hi⟩, count_true_ofFn]
  exact Tanner.weight_shortRow_le _ _ _ _

/-- Distance transfer from `Tanner.le_weight_of_shortRow` for `d ≥ 1`, `0 < maxBiasDen`. -/
theorem le_weight_of_buildShortenedTannerRows {m ell d c maxBiasNum maxBiasDen h : ℕ}
    [NeZero d] (hden : 0 < maxBiasDen) (hm : m ≤ 2 ^ ell * d) {shifts H0 : List (List Bool)}
    (hshifts : checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true)
    (hH0 : checkLocalCodeDistance c d (h + 1) H0 = true) {z : Fin m → Bool} (hz0 : z ≠ 0)
    (hz : ∀ row ∈ buildShortenedTannerRows m ell d c shifts H0, ofList m row ⬝ᵥ z = false) :
    ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ((maxBiasNum : ℝ) / maxBiasDen) * d) * 2 ^ ell ≤
      d * weight z := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdenR : (0 : ℝ) < maxBiasDen := by exact_mod_cast hden
  have hs := ((checkSmallBiasShifts_eq_true_iff hden shifts).1 hshifts).2.2
  have hA := ((checkLocalCodeDistance_eq_true_iff c d (h + 1) H0).1 hH0).2.2
  refine Tanner.le_weight_of_shortRow (fun j : Fin d => ofList ell (shifts.getD j.val []))
    (by positivity) hs (fun i : Fin c => ofList d (H0.getD i.val []))
    (fun w hw0 hker => Nat.lt_of_succ_le (hA w hw0 hker)) (edgeEmbedding hd hm) ?_ hz0
  rintro ⟨side, u, i⟩; let v : Fin (2 ^ ell) := equivFin ell u
  have hrow := hz _ (by
    simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_range, List.mem_map]
    exact ⟨side, by cases side <;> decide, v.val, v.isLt, i.val, i.isLt, rfl⟩)
  rwa [buildRow_eq_ofFn_shortRow hd hm shifts H0 side v i, ofList_ofFn,
    (equivFin ell).symm_apply_apply u] at hrow
/-- Specialization of `buildShortenedTannerRows` to Lemma 6.1 (`1 ≤ n, m, B`, `m ≤ B * n`). -/
theorem le_mul_weight_of_buildShortenedTannerRows_params {n m B : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hB : 1 ≤ B) (hmn : m ≤ B * n) {shifts H0 : List (List Bool)}
    (hshifts : checkSmallBiasShifts (ellG m B) (dG m B) 1 (biasDen m B) shifts = true)
    (hH0 : checkLocalCodeDistance (cG m B) (dG m B) (hDist m B + 1) H0 = true) :
    let rows := buildShortenedTannerRows m (ellG m B) (dG m B) (cG m B) shifts H0
    rows.length ≤ 3 * n ∧
      (∀ row ∈ rows, row.length = m ∧ row.count true ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList m row ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  have hd : 0 < dG m B := dG_pos hm hB; have : NeZero (dG m B) := ⟨hd.ne'⟩
  have hqd : m ≤ 2 ^ ellG m B * dG m B := le_qG_mul_dG hm hB
  have hden : 0 < biasDen m B := by unfold biasDen; positivity
  refine ⟨(length_buildShortenedTannerRows _ _ _ _ _ _).le.trans
      (two_mul_qG_mul_cG_le_three_mul hn hm hB hmn),
    fun row hrow => ⟨length_mem_buildShortenedTannerRows hrow,
      (count_true_mem_buildShortenedTannerRows_le hd hqd hrow).trans (Nat.min_le_right _ _)⟩,
    fun z hz0 hz => ?_⟩
  have htan := le_weight_of_buildShortenedTannerRows hden hqd hshifts hH0 hz0 hz
  set D : ℝ := 100 * (B : ℝ) * (mu m : ℝ); have hM : 0 < D := by positivity
  have hh_ge : (dG m B : ℝ) / D ≤ ((hDist m B + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hM]; dsimp only [D, mu]; exact_mod_cast dG_le_hDist_succ_mul hm hB
  have hdiff_ge : (dG m B : ℝ) / (2 * D) ≤
      ((hDist m B + 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) / (biasDen m B : ℝ) * (dG m B : ℝ) := by
    have : ((1 : ℕ) : ℝ) / (biasDen m B : ℝ) * (dG m B : ℝ) = (dG m B : ℝ) / (2 * D) := by
      dsimp only [D]; unfold biasDen mu; push_cast; ring
    have : (dG m B : ℝ) / D = 2 * ((dG m B : ℝ) / (2 * D)) := by ring
    linarith
  have hd0 : 0 ≤ (dG m B : ℝ) / D := by positivity
  have hmulP := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right
    (mul_le_mul hh_ge hdiff_ge (by positivity) (hd0.trans hh_ge)) (by positivity)).trans htan)
    (by unfold greedyRowListLength; positivity : (0 : ℝ) ≤ greedyRowListLength B m)
  have hP_ident : ((dG m B : ℝ) / D) * ((dG m B : ℝ) / (2 * D)) * 2 ^ ellG m B *
      (greedyRowListLength B m : ℝ) = (dG m B : ℝ) * ((qG m B * dG m B : ℕ) : ℝ) := by
    dsimp only [D]; unfold greedyRowListLength qG mu; push_cast; field_simp; ring
  rw [hP_ident] at hmulP
  have := le_of_mul_le_mul_left (hmulP.trans_eq ((mul_right_comm _ _ _).trans (mul_assoc _ _ _)))
    (by exact_mod_cast hd : (0 : ℝ) < dG m B)
  exact (le_qG_mul_dG hm hB).trans (by exact_mod_cast this)
/-- Plain polynomial-time certificate for `buildShortenedTannerRows` when `2 ^ ell ≤ bound`. -/
theorem buildShortenedTannerRows_polyTime {α : Type} {encIn : α ↪ List Bool}
    {m ell d c bound : α → ℕ} {shifts H0 : α → List (List Bool)}
    (hm : ComputableInPolyTime m encIn encUnary) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hc : ComputableInPolyTime c encIn encUnary)
    (hbound : ComputableInPolyTime bound encIn encUnary)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hH0 : ComputableInPolyTime H0 encIn (encList encBits)) (hle : ∀ a, 2 ^ ell a ≤ bound a) :
    ComputableInPolyTime
      (fun a => buildShortenedTannerRows (m a) (ell a) (d a) (c a) (shifts a) (H0 a))
      encIn (encList encBits) := by
  have hq := binary_to_unary_bounded (binary_two_pow.comp hell) hbound hle
  unfold buildShortenedTannerRows
  have hp1 := fst encIn encUnary; have hp2 := fst (encPair encIn encUnary) encUnary
  have hp3 := fst (encPair (encPair encIn encUnary) encUnary) encUnary
  have ha := (hp1.comp' hp2).comp' hp3; have hvIdx := ((snd encIn encUnary).comp' hp2).comp' hp3
  have hi := (snd (encPair encIn encUnary) encUnary).comp' hp3; have hell_x := hell.comp' ha
  have he := snd (encPair (encPair encIn encUnary) encUnary) encUnary; have hd_x := hd.comp' ha
  have hport := unary_mod.comp' (he.prod hd_x)
  have huBits := bitsLow hell_x (unary_to_binary.comp' (unary_div.comp' (he.prod hd_x)))
  have hsBits := bitsRowWithInput hell_x (.const 0) (listGetDWithInput (hshifts.comp' ha) hport [])
  have hvBits := bitsLow hell_x (unary_to_binary.comp' hvIdx)
  have haRow := listGetDWithInput (hH0.comp' ha) hi []
  have hside (side : Bool) : ComputableInPolyTime
      (fun a => (List.range (2 ^ ell a)).flatMap fun vIdx =>
        let vBits := lowBits (ell a) vIdx; (List.range (c a)).map fun i =>
          let aRow := (H0 a).getD i []; (List.range (m a)).map fun e =>
            if d a == 0 then false else
              let uBits := lowBits (ell a) (e / d a); let port := e % d a
              let sBits := listRow (ell a) 0 ((shifts a).getD port [])
              let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
              if !(endBits.zipWith Bool.xor vBits).any id then aRow.getD port false else false)
      encIn (encList encBits) :=
    have hendBits := ite (ComputableInPolyTime.const (encOut := encBool) side)
      (bitsZipWithInput Bool.xor huBits hsBits) huBits
    have hcond := bool_not.comp' (bitsAnyWithInput (test := fun _ => id)
      (bitsZipWithInput Bool.xor hendBits hvBits) (snd _ encBool))
    flatMapWithInput (unary_range' hq) (mapWithInput (unary_range' (hc.comp' hp1))
      (mapToBitsWithInput (unary_range' (hm.comp' (hp1.comp' hp2)))
        (ite (beq hd_x (.const 0)) (.const false)
          (ite hcond (bitsGetDWithInput haRow hport false) (.const false)))))
  refine ((hside false).listAppend' (hside true)).of_enc_eq fun a => ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ### Unconditional Lemma 6.1 initial-tests assembly and native resource bounds -/
private theorem exists_shifts_params {m B : ℕ} [NeZero (dG m B)] (hB : 1 ≤ B) :
    ∃ s : Fin (dG m B) → Fin (ellG m B) → Bool,
      IsSmallBias ((1 : ℝ) / biasDen m B) ((uniformOfFintype (Fin (dG m B))).map s) := by
  rcases Nat.eq_zero_or_pos (ellG m B) with h0 | hpos
  · exact ⟨fun _ => 0, fun _ ⟨i, _⟩ => absurd i.isLt (by omega)⟩
  · have hmu : 0 < mu m := Nat.succ_pos _
    have hdenR : (0 : ℝ) < biasDen m B := by unfold biasDen; positivity
    refine exists_isSmallBias_map_of_exp_lt (ι := Fin (ellG m B)) (d := dG m B) (by positivity) ?_
    have hexp : ((1 : ℝ) / biasDen m B) ^ 2 * (dG m B : ℝ) / 2 = 4 * (mu m : ℝ) := by
      rw [dG_eq_of_ellG_pos hpos]; unfold initialRowWeightBound biasDen mu
      push_cast; field_simp; ring
    rw [Fintype.card_fin, hexp, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have hell_mu := ellG_le_mu m B
    have h8 : (2 : ℝ) * 2 ^ ellG m B ≤ (8 : ℝ) ^ mu m := by
      rw [← pow_succ', show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have he4 : (8 : ℝ) < Real.exp 4 := by
      linarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) * (mu m : ℝ) = (mu m : ℝ) * 4 by ring, Real.exp_nat_mul]
    exact h8.trans_lt (pow_lt_pow_left₀ he4 (by norm_num) (by omega))
private theorem exists_localMatrix_params {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    ∃ A : Fin (cG m B) → Fin (dG m B) → Bool,
      ∀ w : Fin (dG m B) → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → hDist m B + 1 ≤ weight w := by
  suffices hball : #{w : Fin (dG m B) → Bool | w ≠ 0 ∧ weight w ≤ hDist m B} < 2 ^ cG m B by
    obtain ⟨A, hA⟩ := exists_forall_weight_le hball
    exact ⟨A, fun w hw0 hker => by_contra fun hlt => by
      obtain ⟨i, hi⟩ := hA w hw0 (by omega); exact Bool.false_ne_true ((hker i).symm.trans hi)⟩
  have hd_lt : dG m B < 2 ^ mu m :=
    (Nat.min_le_left _ _).trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  have hmu_h : mu m * hDist m B < cG m B := by
    have hc_ge : dG m B ≤ cG m B * (8 * B) := by
      rw [cG, ← Nat.ceilDiv_eq_add_pred_div]; exact Nat.le_ceilDiv_mul (by omega)
    have hle := Nat.mul_div_le (dG m B + 100 * B * mu m - 1) (100 * B * mu m)
    rw [← hDist_succ_eq hm hB] at hle; have := dG_pos hm hB
    have : B * (100 * (mu m * hDist m B)) + 100 * B * mu m =
        100 * B * mu m * (hDist m B + 1) := by ring
    have : cG m B * (8 * B) = B * (8 * cG m B) := by ring
    have := Nat.lt_of_mul_lt_mul_left (by omega : B * (100 * (mu m * hDist m B)) < B * (8 * cG m B))
    omega
  calc #{w : Fin (dG m B) → Bool | w ≠ 0 ∧ weight w ≤ hDist m B}
      ≤ #{w : Fin (dG m B) → Bool | weight w ≤ hDist m B} :=
        card_le_card fun w hw => mem_filter.mpr ⟨mem_univ w, (mem_filter.mp hw).2.2⟩
    _ ≤ (dG m B + 1) ^ hDist m B := card_filter_weight_le_le (dG m B) (hDist m B)
    _ ≤ (2 ^ mu m) ^ hDist m B := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (mu m * hDist m B) := (Nat.pow_mul 2 (mu m) (hDist m B)).symm
    _ < 2 ^ cG m B := Nat.pow_lt_pow_right (by decide) hmu_h

/-- Deterministic Lemma 6.1 construction of the initial parity-check matrix `A^(0)` via
`findSmallBiasShifts`, `findLocalCheckMatrix`, and `buildShortenedTannerRows`. Returns `[]` in the
degenerate cases `m = 0` or `B = 0`. -/
def initialTestsRows (m B : ℕ) : List (List Bool) :=
  buildShortenedTannerRows m (ellG m B) (dG m B) (cG m B)
    (findSmallBiasShifts (ellG m B) (dG m B) 1 (biasDen m B))
    (findLocalCheckMatrix (cG m B) (dG m B) (hDist m B + 1))

/-- Unconditional correctness of `initialTestsRows` ([OpenAI2026ETH], 6.1) for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem initialTestsRows_spec {n m B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hmn : m ≤ B * n) :
    let rows := initialTestsRows m B
    rows.length ≤ 3 * n ∧
      (∀ row ∈ rows, row.length = m ∧ row.count true ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList m row ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hc0 : cG 0 B = 0 := by
      simp only [cG, dG, Nat.zero_min, zero_add]; exact Nat.div_eq_of_lt (by omega)
    have hnil : initialTestsRows 0 B = [] := List.eq_nil_of_length_eq_zero
      (by rw [initialTestsRows, length_buildShortenedTannerRows, hc0, mul_zero])
    simp [hnil]
  · have hd := dG_pos hm hB; have : NeZero (dG m B) := ⟨hd.ne'⟩
    have hden : 0 < biasDen m B := by unfold biasDen; positivity
    exact le_mul_weight_of_buildShortenedTannerRows_params hn hm hB hmn
      ((isSmallBias_findSmallBiasShifts (maxBiasNum := 1) hden
        (by simpa only [Nat.cast_one] using exists_shifts_params hB)).1)
      ((weight_le_of_findLocalCheckMatrix (exists_localMatrix_params hm hB)).1)
/-- Executable witness matching `Cslib.BitString.exists_initialTests` for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem map_ofList_initialTestsRows_spec {n m B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hmn : m ≤ B * n) :
    let rows := (initialTestsRows m B).map (ofList m)
    rows.length ≤ 3 * n ∧ (∀ r ∈ rows, weight r ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ r ∈ rows, r ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  obtain ⟨hlen, hrows, hdist⟩ := initialTestsRows_spec hn hB hmn
  refine ⟨by simpa only [List.length_map] using hlen, fun r hr => ?_,
    fun z hz0 hz => hdist z hz0 fun row hmem => hz _ (List.mem_map.mpr ⟨row, hmem, rfl⟩)⟩
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hr
  rw [← count_true_ofFn, ofFn_ofList (hrows row hmem).1]; exact (hrows row hmem).2
/-- Real division corollary `(m : ℝ) / greedyRowListLength B m ≤ weight z` for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem div_greedyRowListLength_le_weight_of_initialTestsRows {n m B : ℕ} (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hmn : m ≤ B * n) {z : Fin m → Bool} (hz0 : z ≠ 0)
    (hz : ∀ row ∈ initialTestsRows m B, ofList m row ⬝ᵥ z = false) :
    (m : ℝ) / (greedyRowListLength B m : ℝ) ≤ (weight z : ℝ) := by
  have hP : (0 : ℝ) < greedyRowListLength B m := by unfold greedyRowListLength; positivity
  rw [div_le_iff₀ hP, mul_comm]; exact_mod_cast (initialTestsRows_spec hn hB hmn).2.2 z hz0 hz

private theorem mul_two_pow_succ_le (a b : ℕ) : (2 ^ a + 1) * (2 ^ b + 1) ≤ 4 * 2 ^ (a + b) := by
  have := @Nat.one_le_two_pow a; have := @Nat.one_le_two_pow b; rw [Nat.pow_add]; nlinarith
private theorem linear_mb_le_two_pow (m B : ℕ) :
    2 * m + 2 + B ≤ 2 ^ (B + Nat.log 2 (m + 2) + 4) := by
  set X := B + Nat.log 2 (m + 2)
  have hm : m + 2 < 2 ^ (X + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m + 2)).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [X]; omega))
  have hB : B < 2 ^ (X + 1) := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [X]; omega))
  have : 2 ^ (X + 4) = 8 * 2 ^ (X + 1) := by ring
  omega
private theorem exists_pow_of_polyBounded_mb {u : ℕ × ℕ → ℕ}
    (hu : PolyBounded (fun p => (encMB p).length) u) :
    ∃ E : ℕ × ℕ → ℕ, PolyBounded (fun p => p.2 + Nat.log 2 (p.1 + 2)) E ∧ ∀ p, u p ≤ 2 ^ E p := by
  obtain ⟨c, d, hle⟩ := hu.exists_le
  refine ⟨fun p => c + d * (p.2 + Nat.log 2 (p.1 + 2) + 4), by growth_poly, fun p => ?_⟩
  have hlen : (encMB p).length + 1 = 2 * p.1 + 2 + p.2 := by enc_len [encMB]
  rw [Nat.pow_add]; refine (hle p).trans (Nat.mul_le_mul Nat.lt_two_pow_self.le ?_)
  rw [Nat.mul_comm, Nat.pow_mul, hlen]; exact Nat.pow_le_pow_left (linear_mb_le_two_pow p.1 p.2) d

/-- Native `ComputableInO` certificate for `initialTestsRows` on unary `(m, B)`, proving pure
`2 ^ q (B + Nat.log 2 (m + 2))` time and `S (m + B)` space. -/
theorem initialTestsRows_computableInO :
    ∃ q S : ℕ → ℕ, Cslib.PolynomiallyBounded q ∧ Cslib.PolynomiallyBounded S ∧
      ComputableInO (fun p : ℕ × ℕ => initialTestsRows p.1 p.2)
        (encPair encUnary encUnary) (encList encBits)
        (fun p => 2 ^ q (p.2 + Nat.log 2 (p.1 + 2))) (fun p => S (p.1 + p.2)) := by
  let lenMB (p : ℕ × ℕ) : ℕ := (encMB p).length; let X (p : ℕ × ℕ) : ℕ := p.2 + Nat.log 2 (p.1 + 2)
  have hm_mb := fst encUnary encUnary; have hB_mb := snd encUnary encUnary
  obtain ⟨cSh, hSh0⟩ := findSmallBiasShifts_cert_aux (encIn := encMB)
    (fun p => ellG p.1 p.2) (fun p => dG p.1 p.2) (fun _ => 1) (fun p => biasDen p.1 p.2)
    (ellG_polyTime hm_mb hB_mb) (dG_polyTime hm_mb hB_mb) (.const 1)
    (unary_to_binary.comp (biasDen_polyTime hm_mb hB_mb))
  obtain ⟨cLo, hLo0⟩ := findLocalCheckMatrix_cert_aux (encIn := encMB)
    (fun p => cG p.1 p.2) (fun p => dG p.1 p.2) (fun p => hDist p.1 p.2 + 1)
    (cG_polyTime hm_mb hB_mb) (dG_polyTime hm_mb hB_mb)
    (unary_add' (hDist_polyTime hm_mb hB_mb) (.const 1))
  have hSh : cSh.ExpTimePolySpace (fun p => dG p.1 p.2 * ellG p.1 p.2 + ellG p.1 p.2) :=
    hSh0.mono_const 4 fun _ => mul_two_pow_succ_le _ _
  have hLo : cLo.ExpTimePolySpace (fun p => cG p.1 p.2 * dG p.1 p.2 + dG p.1 p.2) :=
    hLo0.mono_const 4 fun _ => mul_two_pow_succ_le _ _
  have hMid1 := fst encMB (encPair (encList encBits) (encList encBits))
  have hMid2 := snd encMB (encPair (encList encBits) (encList encBits))
  have hm_mid := hm_mb.comp' hMid1; have hB_mid := hB_mb.comp' hMid1
  have hBuild := buildShortenedTannerRows_polyTime hm_mid (ellG_polyTime hm_mid hB_mid)
    (dG_polyTime hm_mid hB_mid) (cG_polyTime hm_mid hB_mid)
    (unary_add' (unary_mul' (.const 2) hm_mid) (.const 1))
    ((fst (encList encBits) (encList encBits)).comp' hMid2)
    ((snd (encList encBits) (encList encBits)).comp' hMid2)
    (fun x => qG_le_two_mul_add_one x.1.1 x.1.2)
  have hFull : NativeCertificate.ExpTimePolySpace _ _ :=
    NativeCertificate.FactorTimePolySpace.congr
      (((NativeCertificate.expTimePolySpace_ofPolyTime (of_eq fun _ => rfl) (fun _ => 0)).prod
        (hSh.prod hLo)).comp_ofPolyTime hBuild)
      (f' := fun p : ℕ × ℕ => initialTestsRows p.1 p.2) fun _ => rfl
  obtain ⟨e, hcFull⟩ := hFull.computableInO
  have hpM : Cslib.PolynomiallyBounded (fun n => (n + 1) ^ e) :=
    (Cslib.PolynomiallyBounded.id.add (.const 1)).pow e
  have hLenSum : PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) lenMB :=
    (((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)).mono fun p => by
      enc_len [lenMB, encMB]
  obtain ⟨S, hS_poly, hSpace⟩ := (pOf lenMB hpM).comp hLenSum
  obtain ⟨Ep, hEpP, hEp⟩ := exists_pow_of_polyBounded_mb (pOf lenMB hpM)
  have hB_X : PolyBounded X Prod.snd := PolyBounded.self.mono fun _ => by dsimp only [X]; omega
  have hmu_X : PolyBounded X (fun p => mu p.1) :=
    (PolyBounded.self.add (.const 1)).mono fun p => by
      have := Nat.add_le_add_right (Nat.log_mono_right (by omega : p.1 ≤ p.1 + 2) (b := 2)) 1
      dsimp only [X, mu] at this ⊢; omega
  have hdG_X : PolyBounded X (fun p => dG p.1 p.2) := by
    growth_poly [fun p : ℕ × ℕ => Nat.min_le_right (64 * p.1) (initialRowWeightBound p.1 p.2)]
  obtain ⟨q, hq_poly, hEq⟩ := (show PolyBounded X
      (fun p => dG p.1 p.2 * ellG p.1 p.2 + ellG p.1 p.2 +
        (cG p.1 p.2 * dG p.1 p.2 + dG p.1 p.2) + Ep p) by
    growth_poly [ellG_le_mu, cG_le_dG_add_one])
  refine ⟨q, S, hq_poly, hS_poly, hcFull.mono_le (fun p => ?_) hSpace⟩
  refine (Nat.mul_le_mul_left _ (hEp p)).trans ?_
  rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (by have := hEq p; dsimp only [X] at this ⊢; omega)
/-- Triple-input `(n, m, B)` form of `initialTestsRows_computableInO` on unary `(n, m, B)`,
proving `n + 2 ^ q (B + Nat.log 2 (m + 2))` time (where `+ n` scans past the unary `n` prefix on
the input tape) and `S (n + m + B)` space. -/
theorem initialTestsRows_computableInO_nmb :
    ∃ q S : ℕ → ℕ, Cslib.PolynomiallyBounded q ∧ Cslib.PolynomiallyBounded S ∧
      ComputableInO (fun ((_n, m, B) : ℕ × ℕ × ℕ) => initialTestsRows m B)
        (encPair encUnary (encPair encUnary encUnary)) (encList encBits)
        (fun (n, m, B) => n + 2 ^ q (B + Nat.log 2 (m + 2))) (fun (n, m, B) => S (n + m + B)) := by
  obtain ⟨q, S, hq, hS, hcomp⟩ := initialTestsRows_computableInO
  let encNMB := encPair encUnary encMB; let sz (p : ℕ × ℕ × ℕ) : ℕ := p.1 + p.2.1 + p.2.2
  let cRes := (NativeCertificate.mk _ _ hcomp).comp
    (NativeCertificate.linear (ComputableInO.snd encUnary encMB))
  have hLenNMB : PolyBounded sz (fun p => (encNMB p).length) :=
    (((PolyBounded.const 4).mul PolyBounded.self).add (.const 3)).mono fun p => by
      enc_len [sz, encNMB, encMB]
  obtain ⟨S', hS', hSpace⟩ := hLenNMB.add ((pOf id hS).comp ((PolyBounded.self (size := sz)).mono
    (u := fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2) fun _ => by dsimp only [sz]; omega))
  let q' (X : ℕ) : ℕ := q X + (X + 5)
  refine ⟨q', S', hq.add (.add .id (.const 5)), hS', cRes.computes.mono 2 (fun p => ?_) fun p => ?_⟩
  · change (encNMB p).length + 2 ^ q (p.2.2 + Nat.log 2 (p.2.1 + 2)) ≤
      2 * (p.1 + 2 ^ q' (p.2.2 + Nat.log 2 (p.2.1 + 2)) + 1)
    set X := p.2.2 + Nat.log 2 (p.2.1 + 2)
    have hlen : (encNMB p).length = 2 * p.1 + (2 * p.2.1 + 2 + p.2.2) := by
      enc_len [encNMB, encMB]
    have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : X + 4 ≤ q X + (X + 4))
    have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : q X ≤ q X + (X + 4))
    have h3 : 2 ^ q' X = 2 * 2 ^ (q X + (X + 4)) := by dsimp only [q']; ring
    have hmb : 2 * p.2.1 + 2 + p.2.2 ≤ 2 ^ (X + 4) := linear_mb_le_two_pow p.2.1 p.2.2; omega
  · change (encNMB p).length + S (p.2.1 + p.2.2) ≤ 2 * (S' (p.1 + p.2.1 + p.2.2) + 1)
    have hs : (encNMB p).length + S (p.2.1 + p.2.2) ≤ S' (p.1 + p.2.1 + p.2.2) := hSpace p; omega
end Cslib.Complexity.InitialTestsSearch
