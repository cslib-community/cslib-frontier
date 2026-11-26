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
  simpa [Fin.sum_univ_four, add_assoc] using sum_col_of_mem_doublyStochastic hM o

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
  have heq (j : Fin 4) : φ (fun _ => π) j o = φ (fun _ => π) i o :=
    congrFun (hete (fun _ => π) j i rfl) o
  linarith [col_sum_four (hfeas (fun _ => π)) o, heq 0, heq 1, heq 2, heq 3]

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
  have ab_step (p q : Profile 4) (i : Fin 4) (hi : p i = prefABCD)
      (hq : List.ofFn (Function.update p i prefBACD) = List.ofFn q) :
      φ q i 2 = φ p i 2 ∧ φ q i 3 = φ p i 3 ∧ φ q i 0 + φ q i 1 = φ p i 0 + φ p i 1 :=
    List.ofFn_inj.mp hq ▸ inv_ab_swap hsp p i hi
  have bc_step (p q : Profile 4) (i : Fin 4) (hi : p i = prefABCD)
      (hq : List.ofFn (Function.update p i prefACBD) = List.ofFn q) :
      φ q i 0 = φ p i 0 ∧ φ q i 3 = φ p i 3 ∧ φ q i 1 + φ q i 2 = φ p i 1 + φ p i 2 :=
    List.ofFn_inj.mp hq ▸ inv_bc_swap hsp p i hi
  have ba_step (p q : Profile 4) (i : Fin 4) (hi : p i = prefBACD)
      (hq : List.ofFn (Function.update p i prefABCD) = List.ofFn q) :
      φ q i 2 = φ p i 2 ∧ φ q i 3 = φ p i 3 ∧ φ q i 1 + φ q i 0 = φ p i 1 + φ p i 0 :=
    List.ofFn_inj.mp hq ▸ inv_ba_swap hsp p i hi
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
  have hA : ∀ i o : Fin 4, φ pA i o = 1 / 4 :=
    (List.ofFn_inj.mp rfl : pA = fun _ => prefABCD) ▸ uniform_of_ete hfeas hete prefABCD
  -- 2. Profile pB = (abcd, abcd, bacd, abcd): row 2 = (0, 1/2, 1/4, 1/4).
  obtain ⟨hB2_c, -, hB2_ab⟩ := ab_step pA pB 2 rfl rfl
  simp only [hA] at hB2_c hB2_ab
  have hB2_a0 : φ pB 2 0 = 0 :=
    zero_of_noTwoCycle_col (hfeas pB) (hntc pB) 2 0 1 (by linarith only [hB2_ab])
      hlt_bacd_10 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hB2_b : φ pB 2 1 = 1 / 2 := by linarith only [hB2_ab, hB2_a0]
  have hBcol := hclass (p := pB) 0 2 fun k hk => by
    fin_cases k <;> first | exact absurd rfl hk | rfl
  have hB0_a : φ pB 0 0 = 1 / 3 := by linarith only [hBcol 0, hB2_a0]
  have hB0_b : φ pB 0 1 = 1 / 6 := by linarith only [hBcol 1, hB2_b]
  have hB0_c : φ pB 0 2 = 1 / 4 := by linarith only [hBcol 2, hB2_c]
  -- 3. Profile pC = (abcd, abcd, abcd, acbd): row 3 = (1/4, 0, 1/2, 1/4).
  obtain ⟨hC3_a, -, hC3_bc⟩ := bc_step pA pC 3 rfl rfl
  rw [hA] at hC3_a
  rw [hA, hA] at hC3_bc
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
  obtain ⟨hR3_a, -, hR3_bc⟩ := bc_step pB pR 3 rfl rfl
  obtain ⟨hR2_c, -, hR2_ab⟩ := ab_step pC pR 2 rfl rfl
  simp only [hete pB 3 0 rfl, hB0_a, hB0_b, hB0_c] at hR3_a hR3_bc
  simp only [hC2_a, hC2_b, hC2_c] at hR2_ab hR2_c
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
  obtain ⟨hP2_1c, -, hP2_1ab⟩ := ab_step pB pP2 1 rfl rfl
  simp only [hete pB 1 0 rfl, hB0_a, hB0_b, hB0_c] at hP2_1c hP2_1ab
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
  obtain ⟨hU1_c, -, hU1_ab⟩ := ab_step pR pU 1 rfl rfl
  simp only [hR1_a, hR1_b, hR1_c] at hU1_c hU1_ab
  have hU_ete12 : φ pU 1 = φ pU 2 := hete pU 1 2 rfl
  have hU3_b0 : φ pU 3 1 = 0 := hz pU 3 1 fun h => hntc pU 3 1 0 1 h hlt_acbd_01
    (by linarith only [hcol pU 1, congrFun hU_ete12 1, hnn pU 0 1, hnn pU 3 1, hU1_ab])
    hlt_bacd_10
  have hU3_c : φ pU 3 2 = 1 / 4 := by
    linarith only [(bc_step pP2 pU 3 rfl rfl).2.2, hP2_3b, hP2_3c, hU3_b0]
  have hU0_c_third : φ pU 0 2 = 1 / 3 := by
    linarith only [hcol pU 2, congrFun hU_ete12 2, hU1_c, hU3_c]
  -- 7. Profile pA' = (bacd, bacd, bacd, bacd): all entries = 1/4.
  have hA' : ∀ i o : Fin 4, φ pA' i o = 1 / 4 :=
    (List.ofFn_inj.mp rfl : pA' = fun _ => prefBACD) ▸ uniform_of_ete hfeas hete prefBACD
  -- 8. Profile pB' = (bacd, bacd, bacd, abcd): row 3 = (1/2, 0, 1/4, 1/4).
  obtain ⟨hB'3_c, -, hB'3_ba⟩ := ba_step pA' pB' 3 rfl rfl
  rw [hA'] at hB'3_c
  rw [hA', hA'] at hB'3_ba
  have hB'3_b0 : φ pB' 3 1 = 0 :=
    zero_of_noTwoCycle_col (hfeas pB') (hntc pB') 3 1 0 (by linarith only [hB'3_ba])
      hlt_abcd_01 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  -- 9. Profile pC' = (bacd, bacd, bacd, acbd): row 0 gets c = 1/4.
  have hC'3_bc : φ pC' 3 1 + φ pC' 3 2 = 1 / 4 := by
    linarith only [(bc_step pB' pC' 3 rfl rfl).2.2, hB'3_b0, hB'3_c]
  have hC'3_b0 : φ pC' 3 1 = 0 :=
    zero_of_noTwoCycle_col (hfeas pC') (hntc pC') 3 1 2 (by linarith only [hC'3_bc])
      hlt_acbd_21 fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption
  have hC'3_c : φ pC' 3 2 = 1 / 4 := by linarith only [hC'3_bc, hC'3_b0]
  have hC'col := hclass (p := pC') 0 3 fun k hk => by
    fin_cases k <;> first | exact absurd rfl hk | rfl
  have hC'0_c : φ pC' 0 2 = 1 / 4 := by linarith only [hC'col 2, hC'3_c]
  -- Final step: agent 0 swaps b ↔ a from pC' to pU, keeping φ · 0 2 unchanged: 1/3 = 1/4!
  linarith only [(ba_step pC' pU 0 rfl rfl).1, hC'0_c, hU0_c_third]

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
  rcases Decidable.eq_or_ne j ⟨i.val, i.isLt.trans_le hn⟩ with rfl | heq
  · simp [padProfile, i.isLt]
  · have hne (h : j.val < 4) : (⟨j.val, h⟩ : Fin 4) ≠ i :=
      fun hi => heq (Fin.ext (congrArg (·.val) hi))
    by_cases hj : j.val < 4 <;> simp [padProfile, hj, heq, hne]

/-- Under any `sd`-efficient assignment `M` for `padProfile hn p`, every dummy agent `k ≥ 4`
receives object `k` with probability `1` (so the top-left `4 × 4` block decouples completely). -/
private lemma dummy_fixed_of_isSDEfficient {n : ℕ} (hn : 4 ≤ n) (p : Profile 4)
    {M : Matrix (Fin n) (Fin n) ℝ} (heff : IsSDEfficient (padProfile hn p) M)
    (k : Fin n) (hk : 4 ≤ k.val) : M k k = 1 := by
  have hMds := mem_doublyStochastic_iff_sum.mp heff.1
  have hacyc := ((isSDEfficient_iff_isAcyclicTrade _ M).mp heff).2
  by_contra hneq
  have hlt1 : M k k < 1 := lt_of_le_of_ne (le_one_of_mem_doublyStochastic heff.1) hneq
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
    simp only [padProfile, hj.not_gt, ↓reduceDIte, Equiv.symm_swap, Equiv.swap_apply_right,
      Fin.lt_def]
    refine Nat.pos_of_ne_zero fun hv => hne (Eq.symm ?_)
    simpa only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] using
      (Fin.ext hv : Equiv.swap (⟨0, by omega⟩ : Fin n) j y = ⟨0, by omega⟩)
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
    obtain ⟨j, hjne, hpos⟩ : ∃ j : Fin n, j ≠ v ∧ 0 < M j v := by
      by_contra! hle0
      linarith [hMds.2.2 v,
        Fintype.sum_eq_single v fun j hj => le_antisymm (hle0 j hj) (hMds.1 j v)]
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
      have hpos_lo_hi : 0 < ∑ a ∈ lo, ∑ o ∈ hi, M a o :=
        hpos.trans_le <| (Finset.single_le_sum (fun o _ => hMds.1 j o)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mpr hv4⟩)).trans <|
          Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun o _ => hMds.1 a o)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hj4⟩)
      have hpos_hi_lo : 0 < ∑ a ∈ hi, ∑ o ∈ lo, M a o := by linarith
      obtain ⟨a, ha_hi, hrow_pos⟩ :=
        (Finset.sum_pos_iff_of_nonneg fun a _ => Finset.sum_nonneg fun o _ => hMds.1 a o).mp
          hpos_hi_lo
      obtain ⟨o, ho_lo, hMao⟩ := (Finset.sum_pos_iff_of_nonneg fun o _ => hMds.1 a o).mp hrow_pos
      have ha4 : 4 ≤ a.val := not_lt.mp (Finset.mem_filter.mp ha_hi).2
      have ho4 : o.val < 4 := (Finset.mem_filter.mp ho_lo).2
      have hoS : o ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨ho4, a, ha4, hMao⟩⟩
      have ho_eq : o = ⟨(⟨o.val, ho4⟩ : Fin 4).val, ho4.trans_le hn⟩ := rfl
      have hjpref : (padProfile hn p j).symm o < (padProfile hn p j).symm v := by
        simp only [padProfile, not_le.mp hj4, ↓reduceDIte, Fin.lt_def]
        rw [ho_eq, padPerm_symm_lt hn _ ⟨o.val, ho4⟩, padPerm_symm_ge hn _ v hv4]
        exact ((p _).symm ⟨o.val, ho4⟩).isLt.trans_le hv4
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
      linarith [Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)]
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
  have hsum4 (f : Fin n → ℝ) (hzero : ∀ k : Fin n, 4 ≤ k.val → f k = 0) :
      ∑ j : Fin 4, f ⟨j.val, by omega⟩ = ∑ j : Fin n, f j := by
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
    · simpa only [ψ, Matrix.of_apply,
        hsum4 (fun o => φ (padProfile hn p) ⟨i.val, by omega⟩ o)
          (fun k hk => hrow0 ⟨i.val, by omega⟩ k i.isLt hk)] using hM.2.1 ⟨i.val, by omega⟩
    · simpa only [ψ, Matrix.of_apply,
        hsum4 (fun i => φ (padProfile hn p) i ⟨o.val, by omega⟩)
          (fun k hk => hcol0 k ⟨o.val, by omega⟩ hk o.isLt)] using hM.2.2 ⟨o.val, by omega⟩
  have hψ_ntc : ∀ p : Profile 4, NoTwoCycle p (ψ p) := fun p i j a b hib hij hja hji =>
    have hp_rank (u x y : Fin 4) (hxy : (p u).symm x < (p u).symm y) :
        (padProfile hn p ⟨u.val, by omega⟩).symm ⟨x.val, by omega⟩ <
          (padProfile hn p ⟨u.val, by omega⟩).symm ⟨y.val, by omega⟩ := by
      simpa only [padProfile, u.isLt, ↓reduceDIte, padPerm_symm_lt, Fin.eta, Fin.lt_def] using hxy
    (heff (padProfile hn p)).not_twoCycle hib (hp_rank i a b hij) hja (hp_rank j b a hji)
  have hψ_ete : ∀ p : Profile 4, IsEqualTreatmentOfEquals p (ψ p) := fun p i j hij =>
    funext fun o => congrFun (hete (padProfile hn p) ⟨i.val, i.isLt.trans_le hn⟩
      ⟨j.val, j.isLt.trans_le hn⟩ (by simp only [padProfile, i.isLt, j.isLt, ↓reduceDIte, hij]))
      ⟨o.val, o.isLt.trans_le hn⟩
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
      refine Finset.sum_nbij (Fin.castLE hn) (fun r hr => ?_)
        (fun _ _ _ _ h => Fin.castLE_injective hn h) (fun r hr => ?_) (fun r _ => ?_)
      · simpa only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE] using hr
      · rw [Finset.mem_coe, Finset.mem_Iic] at hr
        exact ⟨⟨r.val, (Fin.le_def.mp hr).trans_lt k.isLt⟩,
          Finset.mem_coe.mpr (Finset.mem_Iic.mpr hr), rfl⟩
      · simp only [ψ, Matrix.of_apply, padProfile, i.isLt, ↓reduceDIte, Fin.castLE,
          padPerm_apply_lt]
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
