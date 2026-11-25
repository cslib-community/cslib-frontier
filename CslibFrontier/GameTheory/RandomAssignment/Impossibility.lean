/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.RandomAssignment.Basic
public import CslibFrontier.GameTheory.RandomAssignment.RandomSerialDictatorship

import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bogomolnaia–Moulin Impossibility Theorem

For `n ≥ 4` agents and `n` indivisible objects, **no** feasible random assignment rule satisfies
all three of:

1. **`sd`-efficiency** (ordinal efficiency, `IsSDEfficient`),
2. **equal treatment of equals** (`IsEqualTreatmentOfEquals`, `ETE`), and
3. **strong `sd`-strategy-proofness** (`IsSDStrategyProof`).

For `n = 4`, the base proof uses an even weaker efficiency assumption: **no pairwise `2`-cycles**
in `tradeRel` (`NoTwoCycle`). It evaluates `φ` along 9 explicit profiles drawn solely from the
three strict rankings `abcd = 0>1>2>3`, `bacd = 1>0>2>3`, and `acbd = 0>2>1>3` (leaving object
`3` least preferred everywhere), deriving `φ U 0 2 = 1/3` along one chain of single-agent
adjacent swaps from `(abcd, abcd, abcd, abcd)` and `φ U 0 2 = 1/4` along a second chain from
`(bacd, bacd, bacd, bacd)`.

To lift `n = 4` to arbitrary `n ≥ 4`, each profile `p : Profile 4` is padded with dummy agents
`k ≥ 4` who rank object `k` strictly first, while agents `0, 1, 2, 3` keep `{0, 1, 2, 3}` in
their top four ranks above `{4, …, n - 1}`. By `sd`-efficiency (acyclicity of `tradeRel`),
every dummy agent `k ≥ 4` must receive object `k` with probability `1`. Thus the top-left `4 × 4`
block restricts to a feasible, `ETE`, `sd`-efficient, and `sd`-strategy-proof rule on `Fin 4`.

Combined with `rsd_isSDEfficient_of_le_three`, this yields the sharp threshold theorem: an
`sd`-efficient, `ETE`, and `sd`-strategy-proof random assignment rule exists if and only if
`n ≤ 3` (`exists_sdEfficient_ete_sdStrategyProof_iff`).

## Main definitions

* `Cslib.GameTheory.RandomAssignment.NoTwoCycle`: pairwise `sd`-efficiency (absence of two-agent
  mutually beneficial probability swaps).

## Main results

* `Cslib.GameTheory.RandomAssignment.bogomolnaiaMoulin_impossibility_four`: impossibility on
  `Fin 4` requiring only `NoTwoCycle`, `ETE`, and `IsSDStrategyProof`.
* `Cslib.GameTheory.RandomAssignment.bogomolnaiaMoulin_impossibility`: impossibility for every
  `n ≥ 4` under `IsSDEfficient`, `ETE`, and `IsSDStrategyProof`.
* `Cslib.GameTheory.RandomAssignment.bogomolnaiaMoulin_impossibility_envyFree`: impossibility
  for every `n ≥ 4` under `IsSDEfficient`, `IsSDEnvyFree`, and `IsSDStrategyProof`.
* `Cslib.GameTheory.RandomAssignment.exists_sdEfficient_ete_sdStrategyProof_iff`: sharp `n ≤ 3`
  characterization.

## References

* [BogomolnaiaMoulin2001] (primary article PDF not consulted; section/theorem locators
  unverified).
-/

public section

namespace Cslib.GameTheory.RandomAssignment

open Finset Matrix

/-- Pairwise ordinal efficiency (`NoTwoCycle`): there is no mutually beneficial swap between two
agents `i, j` over two objects `a, b` carrying positive weight (`0 < P i b` and `0 < P j a`). -/
@[expose] def NoTwoCycle {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j a b : Fin n,
    0 < P i b → (p i).symm a < (p i).symm b →
    0 < P j a → (p j).symm b < (p j).symm a → False

/-- The strict ordering `a > b > c > d` (`0 > 1 > 2 > 3`) on `Fin 4`. -/
private abbrev prefABCD : Equiv.Perm (Fin 4) := Equiv.refl (Fin 4)

/-- The strict ordering `b > a > c > d` (`1 > 0 > 2 > 3`) on `Fin 4`. -/
private abbrev prefBACD : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1

/-- The strict ordering `a > c > b > d` (`0 > 2 > 1 > 3`) on `Fin 4`. -/
private abbrev prefACBD : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2

private lemma symm_abcd (x : Fin 4) : prefABCD.symm x = x := rfl

private lemma prefBACD_eq_swap :
    prefBACD = Equiv.swap (prefABCD 0) (prefABCD 1) * prefABCD := by
  ext x; simp [prefBACD, prefABCD]

private lemma prefACBD_eq_swap :
    prefACBD = Equiv.swap (prefABCD 1) (prefABCD 2) * prefABCD := by
  ext x; simp [prefACBD, prefABCD]

private lemma prefABCD_eq_swap_bacd :
    prefABCD = Equiv.swap (prefBACD 0) (prefBACD 1) * prefBACD := by
  ext x; fin_cases x <;> decide

private lemma col_sum_four {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin 4)) (o : Fin 4) :
    M 0 o + M 1 o + M 2 o + M 3 o = 1 := by
  have h := sum_col_of_mem_doublyStochastic hM o
  simpa [Fin.sum_univ_four, add_assoc] using h

private lemma inv_adjSwap {φ : AssignmentRule 4} (hsp : IsSDStrategyProof φ)
    (p : Profile 4) (i : Fin 4) (k : Fin 4) (hk : k.val + 1 < 4)
    (π' : Equiv.Perm (Fin 4)) (hswap : π' = Equiv.swap (p i k) (p i ⟨k.val + 1, hk⟩) * p i)
    (r₁ r₂ : Fin 4) (hr₁ : r₁ ≠ k ∧ r₁ ≠ ⟨k.val + 1, hk⟩)
    (hr₂ : r₂ ≠ k ∧ r₂ ≠ ⟨k.val + 1, hk⟩) :
    φ (Function.update p i π') i (p i r₁) = φ p i (p i r₁) ∧
    φ (Function.update p i π') i (p i r₂) = φ p i (p i r₂) ∧
    φ (Function.update p i π') i (p i k) +
        φ (Function.update p i π') i (p i ⟨k.val + 1, hk⟩) =
      φ p i (p i k) + φ p i (p i ⟨k.val + 1, hk⟩) := by
  obtain ⟨hother, hpair⟩ := hsp.adjSwap_invariance p i k hk π' hswap
  exact ⟨hother r₁ hr₁.1 hr₁.2, hother r₂ hr₂.1 hr₂.2, hpair⟩

private lemma inv_ab_swap {φ : AssignmentRule 4} (hsp : IsSDStrategyProof φ)
    (p : Profile 4) (i : Fin 4) (hi : p i = prefABCD) :
    φ (Function.update p i prefBACD) i 2 = φ p i 2 ∧
    φ (Function.update p i prefBACD) i 3 = φ p i 3 ∧
    φ (Function.update p i prefBACD) i 0 + φ (Function.update p i prefBACD) i 1 =
      φ p i 0 + φ p i 1 := by
  simpa [hi, prefABCD] using inv_adjSwap hsp p i 0 (by omega) prefBACD
    (by rw [hi]; exact prefBACD_eq_swap) 2 3 (by decide) (by decide)

private lemma inv_bc_swap {φ : AssignmentRule 4} (hsp : IsSDStrategyProof φ)
    (p : Profile 4) (i : Fin 4) (hi : p i = prefABCD) :
    φ (Function.update p i prefACBD) i 0 = φ p i 0 ∧
    φ (Function.update p i prefACBD) i 3 = φ p i 3 ∧
    φ (Function.update p i prefACBD) i 1 + φ (Function.update p i prefACBD) i 2 =
      φ p i 1 + φ p i 2 := by
  simpa [hi, prefABCD] using inv_adjSwap hsp p i 1 (by omega) prefACBD
    (by rw [hi]; exact prefACBD_eq_swap) 0 3 (by decide) (by decide)

private lemma inv_ba_swap {φ : AssignmentRule 4} (hsp : IsSDStrategyProof φ)
    (p : Profile 4) (i : Fin 4) (hi : p i = prefBACD) :
    φ (Function.update p i prefABCD) i 2 = φ p i 2 ∧
    φ (Function.update p i prefABCD) i 3 = φ p i 3 ∧
    φ (Function.update p i prefABCD) i 1 + φ (Function.update p i prefABCD) i 0 =
      φ p i 1 + φ p i 0 := by
  simpa [hi, Equiv.swap_apply_def] using inv_adjSwap hsp p i 0 (by omega) prefABCD
    (by rw [hi]; exact prefABCD_eq_swap_bacd) 2 3 (by decide) (by decide)

/-- Under `NoTwoCycle`, if agent `i` prefers `b` over `a` while every other agent `j ≠ i`
prefers `a` over `b`, and `M i a + M i b < 1`, then `M i a = 0`. -/
private lemma zero_of_noTwoCycle_col {p : Profile 4} {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin 4)) (hntc : NoTwoCycle p M)
    (i a b : Fin 4) (hbound : M i a + M i b < 1)
    (hi_pref : (p i).symm b < (p i).symm a)
    (hother : ∀ j : Fin 4, j ≠ i → (p j).symm a < (p j).symm b) :
    M i a = 0 := by
  have hnn : ∀ j o, 0 ≤ M j o := fun _ _ => nonneg_of_mem_doublyStochastic hM
  by_contra hne
  have hpos : 0 < M i a := lt_of_le_of_ne (hnn i a) (Ne.symm hne)
  have hzero : ∀ j ∈ Finset.univ, j ≠ i → M j b = 0 := fun j _ hj => by
    by_contra hne'
    exact hntc j i a b (lt_of_le_of_ne (hnn j b) (Ne.symm hne')) (hother j hj) hpos hi_pref
  have hcol : M i b = 1 := by
    rw [← sum_col_of_mem_doublyStochastic hM b]
    exact (Finset.sum_eq_single i hzero fun h => absurd (Finset.mem_univ i) h).symm
  linarith only [hcol, hbound, hpos]

/-- Convenience: a constant vector `p` forces uniform row `(1/4, 1/4, 1/4, 1/4)` by ETE. -/
private lemma uniform_of_ete {φ : AssignmentRule 4}
    (hfeas : IsFeasible φ) (hete : ∀ p, IsEqualTreatmentOfEquals p (φ p))
    (π : Equiv.Perm (Fin 4)) (i o : Fin 4) :
    φ (fun _ => π) i o = 1 / 4 := by
  have heq : ∀ j : Fin 4, φ (fun _ => π) j o = φ (fun _ => π) i o := fun j =>
    congrFun (hete (fun _ => π) j i rfl) o
  have hcol := col_sum_four (hfeas (fun _ => π)) o
  rw [heq 0, heq 1, heq 2, heq 3] at hcol
  linarith

/-- **Bogomolnaia–Moulin impossibility theorem for `n = 4`** ([BogomolnaiaMoulin2001], locator
unverified): even weakening `sd`-efficiency to pairwise `NoTwoCycle`, no feasible assignment rule
on 4 agents and 4 objects satisfies equal treatment of equals, `NoTwoCycle`, and strong
`sd`-strategy-proofness. -/
theorem bogomolnaiaMoulin_impossibility_four (φ : AssignmentRule 4)
    (hfeas : IsFeasible φ)
    (hntc : ∀ p : Profile 4, NoTwoCycle p (φ p))
    (hete : ∀ p : Profile 4, IsEqualTreatmentOfEquals p (φ p))
    (hsp : IsSDStrategyProof φ) : False := by
  let pA : Profile 4 := ![prefABCD, prefABCD, prefABCD, prefABCD]
  let pB : Profile 4 := ![prefABCD, prefABCD, prefBACD, prefABCD]
  let pC : Profile 4 := ![prefABCD, prefABCD, prefABCD, prefACBD]
  let pR : Profile 4 := ![prefABCD, prefABCD, prefBACD, prefACBD]
  let pP2 : Profile 4 := ![prefABCD, prefBACD, prefBACD, prefABCD]
  let pU : Profile 4 := ![prefABCD, prefBACD, prefBACD, prefACBD]
  let pA' : Profile 4 := ![prefBACD, prefBACD, prefBACD, prefBACD]
  let pB' : Profile 4 := ![prefBACD, prefBACD, prefBACD, prefABCD]
  let pC' : Profile 4 := ![prefBACD, prefBACD, prefBACD, prefACBD]
  -- Update equations relating adjacent profiles in the chain.
  have hpA_const : pA = fun _ => prefABCD := by funext i; fin_cases i <;> rfl
  have hpA'_const : pA' = fun _ => prefBACD := by funext i; fin_cases i <;> rfl
  have huAB : Function.update pA 2 prefBACD = pB := by funext i; fin_cases i <;> rfl
  have huAC : Function.update pA 3 prefACBD = pC := by funext i; fin_cases i <;> rfl
  have huBR : Function.update pB 3 prefACBD = pR := by funext i; fin_cases i <;> rfl
  have huCR : Function.update pC 2 prefBACD = pR := by funext i; fin_cases i <;> rfl
  have huBP2 : Function.update pB 1 prefBACD = pP2 := by funext i; fin_cases i <;> rfl
  have huRU : Function.update pR 1 prefBACD = pU := by funext i; fin_cases i <;> rfl
  have huP2U : Function.update pP2 3 prefACBD = pU := by funext i; fin_cases i <;> rfl
  have huA'B' : Function.update pA' 3 prefABCD = pB' := by funext i; fin_cases i <;> rfl
  have huB'C' : Function.update pB' 3 prefACBD = pC' := by funext i; fin_cases i <;> rfl
  have huC'U : Function.update pC' 0 prefABCD = pU := by funext i; fin_cases i <;> rfl
  -- Helper strict ranking comparisons used repeatedly.
  have hlt_abcd_01 : prefABCD.symm 0 < prefABCD.symm 1 := by decide
  have hlt_abcd_12 : prefABCD.symm 1 < prefABCD.symm 2 := by decide
  have hlt_bacd_10 : prefBACD.symm 1 < prefBACD.symm 0 := by decide
  have hlt_bacd_12 : prefBACD.symm 1 < prefBACD.symm 2 := by decide
  have hlt_acbd_01 : prefACBD.symm 0 < prefACBD.symm 1 := by decide
  have hlt_acbd_21 : prefACBD.symm 2 < prefACBD.symm 1 := by decide
  have hnn : ∀ p i o, 0 ≤ φ p i o := fun p _ _ => nonneg_of_mem_doublyStochastic (hfeas p)
  have hz : ∀ p i o, ¬ 0 < φ p i o → φ p i o = 0 := fun p i o h =>
    le_antisymm (not_lt.mp h) (hnn p i o)
  have hcol : ∀ p o, φ p 0 o + φ p 1 o + φ p 2 o + φ p 3 o = 1 := fun p =>
    col_sum_four (hfeas p)
  have hclass {p : Profile 4} (i j : Fin 4) (hp : ∀ k ≠ j, p k = p i) (o : Fin 4) :
      3 * φ p i o + φ p j o = 1 := by
    have h := Finset.sum_erase_add Finset.univ (fun k => φ p k o) (Finset.mem_univ j)
    rw [(mem_doublyStochastic_iff_sum.mp (hfeas p)).2.2 o] at h
    rw [Finset.sum_congr rfl (fun k hk => congrFun (hete p k i (hp k
      (Finset.mem_erase.mp hk).1)) o), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] at h
    simpa only [nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat] using h
  -- 1. Profile pA = (abcd, abcd, abcd, abcd): all entries = 1/4.
  have hA : ∀ i o : Fin 4, φ pA i o = 1 / 4 := fun i o => by
    rw [hpA_const]; exact uniform_of_ete hfeas hete prefABCD i o
  -- 2. Profile pB = (abcd, abcd, bacd, abcd): row 2 = (0, 1/2, 1/4, 1/4).
  have hB2_sw := inv_ab_swap hsp pA 2 rfl
  rw [huAB] at hB2_sw
  have hB2_c : φ pB 2 2 = 1 / 4 := by rw [hB2_sw.1, hA]
  have hB2_ab : φ pB 2 0 + φ pB 2 1 = 1 / 2 := by
    rw [hB2_sw.2.2, hA, hA]; norm_num
  have hB2_a0 : φ pB 2 0 = 0 :=
    zero_of_noTwoCycle_col (hfeas pB) (hntc pB) 2 0 1 (by linarith only [hB2_ab])
      hlt_bacd_10 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hB2_b : φ pB 2 1 = 1 / 2 := by linarith only [hB2_ab, hB2_a0]
  have hBcol := hclass (p := pB) 0 2 fun k hk => by
    fin_cases k <;> first | exact absurd rfl hk | rfl
  have hB_ete01 : φ pB 0 = φ pB 1 := hete pB 0 1 rfl
  have hB_ete03 : φ pB 0 = φ pB 3 := hete pB 0 3 rfl
  have hB0_a : φ pB 0 0 = 1 / 3 := by linarith only [hBcol 0, hB2_a0]
  have hB0_b : φ pB 0 1 = 1 / 6 := by linarith only [hBcol 1, hB2_b]
  have hB0_c : φ pB 0 2 = 1 / 4 := by linarith only [hBcol 2, hB2_c]
  have hB3_a : φ pB 3 0 = 1 / 3 := by rw [← congrFun hB_ete03 0, hB0_a]
  have hB3_b : φ pB 3 1 = 1 / 6 := by rw [← congrFun hB_ete03 1, hB0_b]
  have hB3_c : φ pB 3 2 = 1 / 4 := by rw [← congrFun hB_ete03 2, hB0_c]
  have hB1_a : φ pB 1 0 = 1 / 3 := by rw [← congrFun hB_ete01 0, hB0_a]
  have hB1_b : φ pB 1 1 = 1 / 6 := by rw [← congrFun hB_ete01 1, hB0_b]
  have hB1_c : φ pB 1 2 = 1 / 4 := by rw [← congrFun hB_ete01 2, hB0_c]
  -- 3. Profile pC = (abcd, abcd, abcd, acbd): row 3 = (1/4, 0, 1/2, 1/4).
  have hC3_sw := inv_bc_swap hsp pA 3 rfl
  rw [huAC] at hC3_sw
  have hC3_a : φ pC 3 0 = 1 / 4 := by rw [hC3_sw.1, hA]
  have hC3_bc : φ pC 3 1 + φ pC 3 2 = 1 / 2 := by
    rw [hC3_sw.2.2, hA, hA]; norm_num
  have hC3_b0 : φ pC 3 1 = 0 :=
    zero_of_noTwoCycle_col (hfeas pC) (hntc pC) 3 1 2 (by linarith only [hC3_bc])
      hlt_acbd_21 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hC3_c : φ pC 3 2 = 1 / 2 := by linarith only [hC3_bc, hC3_b0]
  have hCcol := hclass (p := pC) 2 3 fun k hk => by
    fin_cases k <;> first | exact absurd rfl hk | rfl
  have hC2_a : φ pC 2 0 = 1 / 4 := by linarith only [hCcol 0, hC3_a]
  have hC2_b : φ pC 2 1 = 1 / 3 := by linarith only [hCcol 1, hC3_b0]
  have hC2_c : φ pC 2 2 = 1 / 6 := by linarith only [hCcol 2, hC3_c]
  -- 4. Profile pR = (abcd, abcd, bacd, acbd): rows 0,1 = (1/3, 5/24, 5/24, 1/4).
  have hR3_sw := inv_bc_swap hsp pB 3 rfl
  rw [huBR] at hR3_sw
  have hR2_sw := inv_ab_swap hsp pC 2 rfl
  rw [huCR] at hR2_sw
  have hR3_a : φ pR 3 0 = 1 / 3 := by rw [hR3_sw.1, hB3_a]
  have hR3_bc : φ pR 3 1 + φ pR 3 2 = 5 / 12 := by
    rw [hR3_sw.2.2, hB3_b, hB3_c]; norm_num
  have hR2_ab : φ pR 2 0 + φ pR 2 1 = 7 / 12 := by
    rw [hR2_sw.2.2, hC2_a, hC2_b]; norm_num
  have hR2_c : φ pR 2 2 = 1 / 6 := by rw [hR2_sw.1, hC2_c]
  have hR2_a0 : φ pR 2 0 = 0 :=
    zero_of_noTwoCycle_col (hfeas pR) (hntc pR) 2 0 1 (by linarith only [hR2_ab])
      hlt_bacd_10 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hR2_b : φ pR 2 1 = 7 / 12 := by linarith only [hR2_ab, hR2_a0]
  have hR3_b0 : φ pR 3 1 = 0 := hz pR 3 1 fun h =>
    hntc pR 2 3 1 2 (by rw [hR2_c]; norm_num) hlt_bacd_12 h hlt_acbd_21
  have hR3_c : φ pR 3 2 = 5 / 12 := by linarith only [hR3_bc, hR3_b0]
  have hR_ete01 : φ pR 0 = φ pR 1 := hete pR 0 1 rfl
  have hR1_a : φ pR 1 0 = 1 / 3 := by
    linarith only [hcol pR 0, congrFun hR_ete01 0, hR2_a0, hR3_a]
  have hR1_b : φ pR 1 1 = 5 / 24 := by
    linarith only [hcol pR 1, congrFun hR_ete01 1, hR2_b, hR3_b0]
  have hR1_c : φ pR 1 2 = 5 / 24 := by
    linarith only [hcol pR 2, congrFun hR_ete01 2, hR2_c, hR3_c]
  -- 5. Profile pP2 = (abcd, bacd, bacd, abcd): rows 0,3 = (1/2, 0, 1/4, 1/4).
  have hP2_sw := inv_ab_swap hsp pB 1 rfl
  rw [huBP2] at hP2_sw
  have hP2_1c : φ pP2 1 2 = 1 / 4 := by rw [hP2_sw.1, hB1_c]
  have hP2_1ab : φ pP2 1 0 + φ pP2 1 1 = 1 / 2 := by
    rw [hP2_sw.2.2, hB1_a, hB1_b]; norm_num
  have hP2_ete12 : φ pP2 1 = φ pP2 2 := hete pP2 1 2 rfl
  have hP2_ete03 : φ pP2 0 = φ pP2 3 := hete pP2 0 3 rfl
  have hP2_1a0 : φ pP2 1 0 = 0 := hz pP2 1 0 fun hpos => by
    have h0b : φ pP2 0 1 = 0 := hz pP2 0 1 fun h =>
      hntc pP2 0 1 0 1 h hlt_abcd_01 hpos hlt_bacd_10
    linarith only [hcol pP2 1, h0b, congrFun hP2_ete03 1, congrFun hP2_ete12 1, hP2_1ab, hpos]
  have hP2_1b : φ pP2 1 1 = 1 / 2 := by linarith only [hP2_1ab, hP2_1a0]
  have hP2_3b : φ pP2 3 1 = 0 := by
    linarith only [hcol pP2 1, congrFun hP2_ete03 1, congrFun hP2_ete12 1, hP2_1b]
  have hP2_3c : φ pP2 3 2 = 1 / 4 := by
    linarith only [hcol pP2 2, congrFun hP2_ete03 2, congrFun hP2_ete12 2, hP2_1c]
  -- 6. Profile pU = (abcd, bacd, bacd, acbd): pin φ pU 0 2 = 1/3 via pR → pU and pP2 → pU.
  have hU1_sw := inv_ab_swap hsp pR 1 rfl
  rw [huRU] at hU1_sw
  have hU1_c : φ pU 1 2 = 5 / 24 := by rw [hU1_sw.1, hR1_c]
  have hU1_ab : φ pU 1 0 + φ pU 1 1 = 13 / 24 := by
    rw [hU1_sw.2.2, hR1_a, hR1_b]; norm_num
  have hU_ete12 : φ pU 1 = φ pU 2 := hete pU 1 2 rfl
  have hU3_b0 : φ pU 3 1 = 0 := hz pU 3 1 fun h => hntc pU 3 1 0 1 h hlt_acbd_01
    (by linarith only [hcol pU 1, congrFun hU_ete12 1, hnn pU 0 1, hnn pU 3 1, hU1_ab])
    hlt_bacd_10
  have hU3_sw := inv_bc_swap hsp pP2 3 rfl
  rw [huP2U] at hU3_sw
  have hU3_c : φ pU 3 2 = 1 / 4 := by
    have hbc : φ pU 3 1 + φ pU 3 2 = 1 / 4 := by
      rw [hU3_sw.2.2, hP2_3b, hP2_3c]; norm_num
    linarith only [hbc, hU3_b0]
  have hU0_c_third : φ pU 0 2 = 1 / 3 := by
    linarith only [hcol pU 2, congrFun hU_ete12 2, hU1_c, hU3_c]
  -- 7. Profile pA' = (bacd, bacd, bacd, bacd): all entries = 1/4.
  have hA' : ∀ i o : Fin 4, φ pA' i o = 1 / 4 := fun i o => by
    rw [hpA'_const]; exact uniform_of_ete hfeas hete prefBACD i o
  -- 8. Profile pB' = (bacd, bacd, bacd, abcd): row 3 = (1/2, 0, 1/4, 1/4).
  have hB'3_sw := inv_ba_swap hsp pA' 3 rfl
  rw [huA'B'] at hB'3_sw
  have hB'3_c : φ pB' 3 2 = 1 / 4 := by rw [hB'3_sw.1, hA']
  have hB'3_ba : φ pB' 3 1 + φ pB' 3 0 = 1 / 2 := by
    rw [hB'3_sw.2.2, hA', hA']; norm_num
  have hB'3_b0 : φ pB' 3 1 = 0 :=
    zero_of_noTwoCycle_col (hfeas pB') (hntc pB') 3 1 0 (by linarith only [hB'3_ba])
      hlt_abcd_01 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  -- 9. Profile pC' = (bacd, bacd, bacd, acbd): row 0 gets c = 1/4.
  have hC'3_sw := inv_bc_swap hsp pB' 3 rfl
  rw [huB'C'] at hC'3_sw
  have hC'3_bc : φ pC' 3 1 + φ pC' 3 2 = 1 / 4 := by
    rw [hC'3_sw.2.2, hB'3_b0, hB'3_c]; norm_num
  have hC'3_b0 : φ pC' 3 1 = 0 :=
    zero_of_noTwoCycle_col (hfeas pC') (hntc pC') 3 1 2 (by linarith only [hC'3_bc])
      hlt_acbd_21 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hC'3_c : φ pC' 3 2 = 1 / 4 := by linarith only [hC'3_bc, hC'3_b0]
  have hC'col := hclass (p := pC') 0 3 fun k hk => by
    fin_cases k <;> first | exact absurd rfl hk | rfl
  have hC'0_c : φ pC' 0 2 = 1 / 4 := by linarith only [hC'col 2, hC'3_c]
  -- Final step: agent 0 swaps b ↔ a from pC' to pU, keeping φ · 0 2 unchanged: 1/3 = 1/4!
  have hC'U_sw := inv_ba_swap hsp pC' 0 rfl
  rw [huC'U] at hC'U_sw
  linarith only [hC'U_sw.1, hC'0_c, hU0_c_third]

/-- Embed a `4`-agent strict ordering `π : Equiv.Perm (Fin 4)` into `Equiv.Perm (Fin n)` for
`n ≥ 4`, fixing every dummy index `k ≥ 4`. -/
private def padPerm {n : ℕ} (hn : 4 ≤ n) (π : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin n) :=
  π.extendDomain (Fin.castLEquiv hn)

private lemma padPerm_apply_lt {n : ℕ} (hn : 4 ≤ n) (π : Equiv.Perm (Fin 4)) (r : Fin 4) :
    padPerm hn π ⟨r.val, by lia⟩ = ⟨(π r).val, by lia⟩ :=
  π.extendDomain_apply_image (Fin.castLEquiv hn) r

private lemma padPerm_symm_lt {n : ℕ} (hn : 4 ≤ n) (π : Equiv.Perm (Fin 4)) (o : Fin 4) :
    (padPerm hn π).symm ⟨o.val, by lia⟩ = ⟨(π.symm o).val, by lia⟩ :=
  padPerm_apply_lt hn π.symm o

private lemma padPerm_symm_ge {n : ℕ} (hn : 4 ≤ n) (π : Equiv.Perm (Fin 4))
    (o : Fin n) (ho : 4 ≤ o.val) : (padPerm hn π).symm o = o :=
  Equiv.Perm.extendDomain_apply_not_subtype π.symm (Fin.castLEquiv hn) ho.not_gt

/-- Pad a 4-agent profile `p : Profile 4` into `Profile n` (`n ≥ 4`): agents `i < 4` use `padPerm`
(ranking `{0, 1, 2, 3}` strictly above `{4, …, n - 1}`), and dummy agents `k ≥ 4` rank object `k`
first. -/
private def padProfile {n : ℕ} (hn : 4 ≤ n) (p : Profile 4) : Profile n := fun i =>
  if h : i.val < 4 then padPerm hn (p ⟨i.val, h⟩)
  else Equiv.swap ⟨0, by omega⟩ i

private lemma padProfile_update {n : ℕ} (hn : 4 ≤ n) (p : Profile 4) (i : Fin 4)
    (π' : Equiv.Perm (Fin 4)) :
    padProfile hn (Function.update p i π') =
      Function.update (padProfile hn p) ⟨i.val, by omega⟩ (padPerm hn π') := by
  funext j
  by_cases hj : j.val < 4
  · by_cases heq : j = ⟨i.val, by omega⟩
    · rw [heq]
      simp only [padProfile, i.isLt, ↓reduceDIte, Function.update_self]
    · have hne : (⟨j.val, hj⟩ : Fin 4) ≠ i := fun h => by
        have hv : j.val = i.val := congrArg Fin.val h
        exact heq (Fin.ext hv)
      rw [Function.update_of_ne heq]
      simp only [padProfile, hj, ↓reduceDIte, Function.update_of_ne hne]
  · have hne : j ≠ ⟨i.val, by omega⟩ := fun h => hj (by rw [h]; exact i.isLt)
    simp only [padProfile, hj, ↓reduceDIte, Function.update_of_ne hne]

/-- Under any `sd`-efficient assignment `M` for `padProfile hn p`, every dummy agent `k ≥ 4`
receives object `k` with probability `1` (so the top-left `4 × 4` block decouples completely). -/
private lemma dummy_fixed_of_isSDEfficient {n : ℕ} (hn : 4 ≤ n) (p : Profile 4)
    {M : Matrix (Fin n) (Fin n) ℝ} (heff : IsSDEfficient (padProfile hn p) M)
    (k : Fin n) (hk : 4 ≤ k.val) : M k k = 1 := by
  have hMds := mem_doublyStochastic_iff_sum.mp heff.1
  have hacyc := ((isSDEfficient_iff_isAcyclicTrade _ M).mp heff).2
  by_contra hneq
  have hle1 : M k k ≤ 1 := le_one_of_mem_doublyStochastic heff.1
  have hlt1 : M k k < 1 := lt_of_le_of_ne hle1 hneq
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun x =>
    (x.val < 4 ∧ ∃ j : Fin n, 4 ≤ j.val ∧ 0 < M j x) ∨ (4 ≤ x.val ∧ M x x < 1)
  have hSne : S.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hk, hlt1⟩⟩⟩
  obtain ⟨rank, -, hrank⟩ :=
    hacyc.exists_rank Finset.univ fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  obtain ⟨v, hvS, hmin⟩ := Finset.exists_min_image S rank hSne
  have hsrc : ∀ b ∈ S, ¬ tradeRel (padProfile hn p) M b v := fun b hb hbv =>
    (hrank b v hbv).not_ge (hmin b hb)
  have hrank_dummy : ∀ (j y : Fin n), 4 ≤ j.val → j ≠ y →
      (padProfile hn p j).symm j < (padProfile hn p j).symm y := by
    intro j y hj hne
    have hp : padProfile hn p j = Equiv.swap ⟨0, by omega⟩ j := by
      simp [padProfile, show ¬ j.val < 4 by omega]
    rw [hp, Equiv.symm_swap, Equiv.swap_apply_right, Fin.lt_def]
    refine Nat.pos_of_ne_zero fun hv => hne ?_
    have h0 : Equiv.swap (⟨0, by omega⟩ : Fin n) j y = ⟨0, by omega⟩ := Fin.ext hv
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
    exact h0.symm
  -- A dummy row `j` with positive off-diagonal mass on `v` would be a trade source into `v`.
  have hdummy_src : ∀ j : Fin n, 4 ≤ j.val → j ≠ v → 0 < M j v → False := by
    intro j hj4 hjne hpos
    have hle := Finset.add_le_sum (fun o _ => hMds.1 j o) (Finset.mem_univ j)
      (Finset.mem_univ v) hjne
    refine hsrc j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hj4, ?_⟩⟩)
      ⟨j, hpos, hrank_dummy j v hj4 hjne⟩
    linarith [hMds.2.1 j]
  rcases (Finset.mem_filter.mp hvS).2 with ⟨hv4, j, hj4, hpos⟩ | ⟨hv4, hltv⟩
  · exact hdummy_src j hj4 (fun h => by subst h; omega) hpos
  · -- Since `M v v < 1` and column sum `v` is `1`, some `j ≠ v` satisfies `0 < M j v`.
    have hex_j : ∃ j : Fin n, j ≠ v ∧ 0 < M j v := by
      by_contra! hle0
      have hcol : ∑ j : Fin n, M j v = M v v :=
        Fintype.sum_eq_single v fun j hj => le_antisymm (hle0 j hj) (hMds.1 j v)
      linarith [hMds.2.2 v]
    obtain ⟨j, hjne, hpos⟩ := hex_j
    by_cases hj4 : 4 ≤ j.val
    · exact hdummy_src j hj4 hjne hpos
    · -- `j.val < 4` gets positive mass of `v ≥ 4`; balance of block `{0..3}` implies some
      -- `k' ≥ 4` gets positive mass of some `o < 4`.
      let lo : Finset (Fin n) := Finset.univ.filter fun x => x.val < 4
      let hi : Finset (Fin n) := Finset.univ.filter fun x => ¬ x.val < 4
      have hpart : ∀ (f : Fin n → ℝ),
          ∑ x : Fin n, f x = ∑ x ∈ lo, f x + ∑ x ∈ hi, f x := fun f =>
        (Finset.sum_filter_add_sum_filter_not _ _ f).symm
      have hsplit (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ a, ∑ o : Fin n, W a o = 1) :
          ∑ a ∈ lo, ∑ o ∈ hi, W a o = (lo.card : ℝ) - ∑ a ∈ lo, ∑ o ∈ lo, W a o := by
        apply eq_sub_of_add_eq
        rw [add_comm, ← Finset.sum_add_distrib]
        simp [← hpart, hrow]
      have hsplit_r := hsplit M hMds.2.1
      have hsplit_c := hsplit M.transpose hMds.2.2
      simp only [Matrix.transpose_apply] at hsplit_c
      rw [Finset.sum_comm (s := lo) (t := hi), Finset.sum_comm (s := lo) (t := lo)] at hsplit_c
      have hpos_lo_hi : 0 < ∑ a ∈ lo, ∑ o ∈ hi, M a o := by
        have hjlo : j ∈ lo := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hvhi : v ∈ hi := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have h1 : M j v ≤ ∑ o ∈ hi, M j o :=
          Finset.single_le_sum (fun o _ => hMds.1 j o) hvhi
        have h2 : ∑ o ∈ hi, M j o ≤ ∑ a ∈ lo, ∑ o ∈ hi, M a o :=
          Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun o _ => hMds.1 a o) hjlo
        linarith
      have hpos_hi_lo : 0 < ∑ a ∈ hi, ∑ o ∈ lo, M a o := by linarith
      obtain ⟨a, ha_hi, hrow_pos⟩ :=
        (Finset.sum_pos_iff_of_nonneg fun a _ => Finset.sum_nonneg fun o _ => hMds.1 a o).mp
          hpos_hi_lo
      obtain ⟨o, ho_lo, hMao⟩ := (Finset.sum_pos_iff_of_nonneg fun o _ => hMds.1 a o).mp hrow_pos
      have ha4 : 4 ≤ a.val := not_lt.mp (Finset.mem_filter.mp ha_hi).2
      have ho4 : o.val < 4 := (Finset.mem_filter.mp ho_lo).2
      have hoS : o ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨ho4, a, ha4, hMao⟩⟩
      have hjpref : (padProfile hn p j).symm o < (padProfile hn p j).symm v := by
        have hpj : padProfile hn p j = padPerm hn (p ⟨j.val, by omega⟩) := by
          simp [padProfile, show j.val < 4 by omega]
        rw [hpj]
        have ho_rk := padPerm_symm_lt hn (p ⟨j.val, by omega⟩) ⟨o.val, ho4⟩
        have hv_rk := padPerm_symm_ge hn (p ⟨j.val, by omega⟩) v hv4
        change ((padPerm hn (p ⟨j.val, by omega⟩)).symm o).val <
          ((padPerm hn (p ⟨j.val, by omega⟩)).symm v).val
        have hfin : (⟨o.val, by omega⟩ : Fin n) = o := rfl
        rw [hfin] at ho_rk
        rw [ho_rk, hv_rk]
        exact lt_of_lt_of_le ((p ⟨j.val, by omega⟩).symm ⟨o.val, ho4⟩).isLt hv4
      exact hsrc o hoS ⟨j, hpos, hjpref⟩

private lemma dummy_block_zero {n : ℕ} (hn : 4 ≤ n) (p : Profile 4)
    {M : Matrix (Fin n) (Fin n) ℝ} (heff : IsSDEfficient (padProfile hn p) M) :
    (∀ i k : Fin n, i.val < 4 → 4 ≤ k.val → M i k = 0) ∧
    (∀ k o : Fin n, 4 ≤ k.val → o.val < 4 → M k o = 0) := by
  have hMds := mem_doublyStochastic_iff_sum.mp heff.1
  have hother_zero : ∀ (f : Fin n → ℝ) (k x : Fin n),
      (∀ y, 0 ≤ f y) → ∑ y : Fin n, f y = 1 → f k = 1 → x ≠ k → f x = 0 := by
    intro f k x hnn hsum hfk hne
    have hrest : ∑ y ∈ Finset.univ.erase k, f y = 0 := by
      have hadd := Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).mp hrest x
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
  exact ⟨fun i k hi hk =>
      hother_zero (fun j => M j k) k i (fun j => hMds.1 j k) (hMds.2.2 k)
        (dummy_fixed_of_isSDEfficient hn p heff k hk) (fun h => by subst h; omega),
    fun k o hk ho =>
      hother_zero (fun y => M k y) k o (fun y => hMds.1 k y) (hMds.2.1 k)
        (dummy_fixed_of_isSDEfficient hn p heff k hk) (fun h => by subst h; omega)⟩

/-- **Bogomolnaia–Moulin impossibility theorem** ([BogomolnaiaMoulin2001], locator unverified):
for every `n ≥ 4`, there is **no** feasible random assignment rule `φ : AssignmentRule n`
satisfying `sd`-efficiency (`IsSDEfficient`), equal treatment of equals
(`IsEqualTreatmentOfEquals`), and strong `sd`-strategy-proofness (`IsSDStrategyProof`). -/
theorem bogomolnaiaMoulin_impossibility {n : ℕ} (hn : 4 ≤ n) (φ : AssignmentRule n)
    (hfeas : IsFeasible φ)
    (heff : ∀ p : Profile n, IsSDEfficient p (φ p))
    (hete : ∀ p : Profile n, IsEqualTreatmentOfEquals p (φ p))
    (hsp : IsSDStrategyProof φ) : False := by
  let ψ : AssignmentRule 4 := fun p =>
    Matrix.of fun i o => φ (padProfile hn p) ⟨i.val, by omega⟩ ⟨o.val, by omega⟩
  have hsum4 : ∀ (p : Profile 4) (f : Fin n → ℝ),
      (∀ k : Fin n, 4 ≤ k.val → f k = 0) →
      ∑ j : Fin 4, f ⟨j.val, by omega⟩ = ∑ j : Fin n, f j := by
    intro p f hzero
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hn)))
      fun j _ hj => hzero j (not_lt.mp fun h =>
        hj (Finset.mem_map.mpr ⟨⟨j.val, h⟩, Finset.mem_univ _, rfl⟩)), Finset.sum_map]
    rfl
  have hψ_feas : IsFeasible ψ := by
    intro p
    rw [mem_doublyStochastic_iff_sum]
    have hM := mem_doublyStochastic_iff_sum.mp (hfeas (padProfile hn p))
    obtain ⟨hrow0, hcol0⟩ := dummy_block_zero hn p (heff (padProfile hn p))
    refine ⟨fun i o => hM.1 _ _, fun i => ?_, fun o => ?_⟩
    · simp only [ψ, Matrix.of_apply]
      rw [hsum4 p (fun o => φ (padProfile hn p) ⟨i.val, by omega⟩ o)
        (fun k hk => hrow0 ⟨i.val, by omega⟩ k i.isLt hk)]
      exact hM.2.1 ⟨i.val, by omega⟩
    · simp only [ψ, Matrix.of_apply]
      rw [hsum4 p (fun i => φ (padProfile hn p) i ⟨o.val, by omega⟩)
        (fun k hk => hcol0 k ⟨o.val, by omega⟩ hk o.isLt)]
      exact hM.2.2 ⟨o.val, by omega⟩
  have hψ_ntc : ∀ p : Profile 4, NoTwoCycle p (ψ p) := by
    intro p i j a b hib hij hja hji
    have hp_rank : ∀ (u x y : Fin 4), (p u).symm x < (p u).symm y →
        (padProfile hn p ⟨u.val, by omega⟩).symm ⟨x.val, by omega⟩ <
          (padProfile hn p ⟨u.val, by omega⟩).symm ⟨y.val, by omega⟩ := by
      intro u x y hxy
      simp only [padProfile, u.isLt, ↓reduceDIte]
      rw [padPerm_symm_lt hn (p u) x, padPerm_symm_lt hn (p u) y]
      exact hxy
    exact (heff (padProfile hn p)).not_twoCycle hib (hp_rank i a b hij) hja (hp_rank j b a hji)
  have hψ_ete : ∀ p : Profile 4, IsEqualTreatmentOfEquals p (ψ p) := by
    intro p i j hij
    funext o
    have hpad : padProfile hn p ⟨i.val, by omega⟩ = padProfile hn p ⟨j.val, by omega⟩ := by
      simp only [padProfile, i.isLt, j.isLt, ↓reduceDIte, hij]
    exact congrFun (hete (padProfile hn p) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hpad)
      ⟨o.val, by omega⟩
  have hψ_sp : IsSDStrategyProof ψ := by
    intro p i π' k
    have hdom := hsp (padProfile hn p) ⟨i.val, by omega⟩ (padPerm hn π') ⟨k.val, by omega⟩
    rw [← padProfile_update hn p i π'] at hdom
    have huc_eq : ∀ q : Profile 4,
        upperContourSum (p i) (ψ q i) k =
          upperContourSum (padProfile hn p ⟨i.val, by omega⟩)
            (φ (padProfile hn q) ⟨i.val, by omega⟩) ⟨k.val, by omega⟩ := by
      intro q
      unfold upperContourSum
      refine Finset.sum_nbij (fun r : Fin 4 => (⟨r.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_Iic] at hr ⊢
        exact hr
      · intro a _ b _ hab
        exact Fin.ext (Fin.mk.injEq .. ▸ hab)
      · intro r hr
        rw [Finset.mem_coe, Finset.mem_Iic] at hr
        exact ⟨⟨r.val, by have : r.val ≤ k.val := hr; omega⟩,
          Finset.mem_coe.mpr (Finset.mem_Iic.mpr hr), rfl⟩
      · intro r _
        simp only [ψ, Matrix.of_apply, padProfile, i.isLt, ↓reduceDIte, padPerm_apply_lt]
    rw [huc_eq (Function.update p i π'), huc_eq p]
    exact hdom
  exact bogomolnaiaMoulin_impossibility_four ψ hψ_feas hψ_ntc hψ_ete hψ_sp

/-- Corollary of `bogomolnaiaMoulin_impossibility`: for every `n ≥ 4`, no feasible random
assignment rule satisfies `sd`-efficiency, **`sd`-envy-freeness**, and strong
`sd`-strategy-proofness simultaneously. -/
theorem bogomolnaiaMoulin_impossibility_envyFree {n : ℕ} (hn : 4 ≤ n) (φ : AssignmentRule n)
    (hfeas : IsFeasible φ)
    (heff : ∀ p : Profile n, IsSDEfficient p (φ p))
    (hef : ∀ p : Profile n, IsSDEnvyFree p (φ p))
    (hsp : IsSDStrategyProof φ) : False :=
  bogomolnaiaMoulin_impossibility hn φ hfeas heff (fun p => (hef p).equalTreatmentOfEquals) hsp

/-- **Sharp characterization (`n ≤ 3` vs `n ≥ 4`):** a feasible random assignment rule satisfying
`sd`-efficiency, equal treatment of equals (`ETE`), and strong `sd`-strategy-proofness exists if
and only if `n ≤ 3`. For `n ≤ 3`, Random Serial Dictatorship (`rsd`) witnesses existence. -/
theorem exists_sdEfficient_ete_sdStrategyProof_iff (n : ℕ) :
    (∃ φ : AssignmentRule n,
      IsFeasible φ ∧
      (∀ p : Profile n, IsSDEfficient p (φ p)) ∧
      (∀ p : Profile n, IsEqualTreatmentOfEquals p (φ p)) ∧
      IsSDStrategyProof φ) ↔ n ≤ 3 := by
  constructor
  · rintro ⟨φ, hfeas, heff, hete, hsp⟩
    by_contra! hgt
    exact bogomolnaiaMoulin_impossibility (by omega) φ hfeas heff hete hsp
  · intro hn
    exact ⟨rsd, fun p => rsd_mem_doublyStochastic p, fun p => rsd_isSDEfficient_of_le_three hn p,
      rsd_isEqualTreatmentOfEquals, rsd_isSDStrategyProof⟩

end Cslib.GameTheory.RandomAssignment
