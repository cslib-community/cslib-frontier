/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.Scheduling.UnrelatedMachines
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Truthful Makespan Scheduling on Unrelated Machines

Concrete finite witnesses and boundary checks for `Cslib.GameTheory.Scheduling`:

1. Concrete `3`-machine, `4`-job asymmetric processing-time profile `sample3x4` (`Fin 3 → Fin 4 →
   ℝ`), verifying smallest-index tie-breaking in `minWorkAlloc`, per-job Vickrey payments
   `secondLowestTime`, `makespan = 6`, `IsDSIC`, `IsIR`, and the `GameTheory.Mechanism.groves`
   equivalence `exists_groves_eq_minWorkMechanism`.
2. Tightness witness on `Fin 3` machines and `Fin 3` jobs (`tight3x3`: machine `0` takes `1` on all
   jobs while machines `1, 2` take `5 / 4`): `minWorkAlloc` assigns all three jobs to machine `0`
   (`makespan = 3`) while `id` achieves `5 / 4` (`optMakespan ≤ 5 / 4`), plus refutation of
   `HasApproxRatioOn IsPositiveProfile (5 / 2)` for `minWorkMechanism`.
3. Exact minimax approximation ratio `2` for deterministic truthful scheduling on `2` machines and
   `3` jobs (`Fin 2`, `Fin 3`): `minWorkMechanism` achieves ratio `2` on all nonnegative profiles,
   and no DSIC mechanism achieves `199 / 100 < 2` even on strictly positive profiles (nor on `Fin 5`
   machines and `Fin 4` jobs at ratio `7 / 4 < 2`).
4. Sharpness of both cardinality hypotheses (`2 ≤ |Machine|` and `|Job| > 1`): `minWorkMechanism` is
   DSIC and achieves exact `1`-approximation (`c = 1 < 2`) on `Fin 1` machine (`Fin 4` jobs) and on
   `Fin 3` machines with `Fin 1` / `Fin 0` jobs, while `[Nontrivial Machine]` is needed for `IsIR`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.UnrelatedScheduling

open Cslib.GameTheory
open Cslib.GameTheory.Scheduling

/-! ### 1. Concrete `3 × 4` unrelated-machine instance and `MinWork` evaluation -/

/-- Asymmetric `3`-machine, `4`-job matrix with a tie on job `0` (`t 0 0 = t 2 0 = 2`). -/
def sample3x4 : Fin 3 → Fin 4 → ℝ :=
  ![![2, 2, 2, 10],
    ![3, 5, 6, 4],
    ![2, 8, 3, 7]]

example : IsPositiveProfile sample3x4 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sample3x4]

/-- `minWorkAlloc` assigns jobs `0, 1, 2` to machine `0` (breaking the job-`0` tie `2 = 2` in favor
of index `0 < 2`) and job `3` to machine `1`. -/
example : minWorkAlloc sample3x4 = ![0, 0, 0, 1] := by
  funext j
  rw [minWorkAlloc_eq_iff]
  fin_cases j <;>
    · intro k hne
      fin_cases k <;> simp_all [sample3x4] <;> norm_num

/-- Under `minWorkMechanism` on `sample3x4`, machine `0` has load `6`, receives second-price
compensation `2 + 5 + 3 = 10`, and earns positive utility `4`; machine `1` has load `4`, receives
`7`, and earns utility `3`; and the resulting makespan is `6 ≤ 3 * optMakespan sample3x4`. -/
example :
    let M := minWorkMechanism (Machine := Fin 3) (Job := Fin 4)
    load sample3x4 (M.alloc sample3x4) 0 = 6 ∧
      M.pay sample3x4 0 = 10 ∧
      M.utility 0 (sample3x4 0) sample3x4 = 4 ∧
      M.pay sample3x4 1 = 7 ∧
      makespan sample3x4 (M.alloc sample3x4) = 6 ∧
      makespan sample3x4 (M.alloc sample3x4) ≤ 3 * optMakespan sample3x4 := by
  have halloc : minWorkAlloc sample3x4 = ![0, 0, 0, 1] := by
    funext j
    rw [minWorkAlloc_eq_iff]
    fin_cases j <;>
      · intro k hne
        fin_cases k <;> simp_all [sample3x4] <;> norm_num
  have hslt00 : secondLowestTime sample3x4 0 0 = 2 := by
    refine le_antisymm ?_ (le_secondLowestTime_iff.mpr fun k hk => ?_)
    · exact (secondLowestTime_le_of_ne sample3x4 (k := 2) (by decide) 0).trans
        (by norm_num [sample3x4])
    · (fin_cases k <;> simp_all [sample3x4]); norm_num
  have hslt01 : secondLowestTime sample3x4 0 1 = 5 := by
    refine le_antisymm ?_ (le_secondLowestTime_iff.mpr fun k hk => ?_)
    · exact (secondLowestTime_le_of_ne sample3x4 (k := 1) (by decide) 1).trans
        (by norm_num [sample3x4])
    · (fin_cases k <;> simp_all [sample3x4]); norm_num
  have hslt02 : secondLowestTime sample3x4 0 2 = 3 := by
    refine le_antisymm ?_ (le_secondLowestTime_iff.mpr fun k hk => ?_)
    · exact (secondLowestTime_le_of_ne sample3x4 (k := 2) (by decide) 2).trans
        (by norm_num [sample3x4])
    · (fin_cases k <;> simp_all [sample3x4]); norm_num
  have hslt13 : secondLowestTime sample3x4 1 3 = 7 := by
    refine le_antisymm ?_ (le_secondLowestTime_iff.mpr fun k hk => ?_)
    · exact (secondLowestTime_le_of_ne sample3x4 (k := 2) (by decide) 3).trans
        (by norm_num [sample3x4])
    · (fin_cases k <;> simp_all [sample3x4]); norm_num
  have hload0 : load sample3x4 (minWorkAlloc sample3x4) 0 = 6 := by
    rw [halloc]
    simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_four]
    norm_num [sample3x4]
  have hload1 : load sample3x4 (minWorkAlloc sample3x4) 1 = 4 := by
    rw [halloc]
    simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_four]
    norm_num [sample3x4]
  have hload2 : load sample3x4 (minWorkAlloc sample3x4) 2 = 0 := by
    rw [halloc]
    simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_four]
    norm_num [sample3x4]
  have hpay0 : (minWorkMechanism (Machine := Fin 3) (Job := Fin 4)).pay sample3x4 0 = 10 := by
    simp only [minWorkMechanism, halloc, Finset.sum_filter, Fin.sum_univ_four]
    rw [hslt00, hslt01, hslt02]
    norm_num
  have hpay1 : (minWorkMechanism (Machine := Fin 3) (Job := Fin 4)).pay sample3x4 1 = 7 := by
    simp only [minWorkMechanism, halloc, Finset.sum_filter, Fin.sum_univ_four]
    rw [hslt13]
    norm_num
  have hmake : makespan sample3x4 (minWorkAlloc sample3x4) = 6 := by
    refine le_antisymm (makespan_le_iff.mpr fun i => ?_) ?_
    · fin_cases i
      · exact hload0.le
      · dsimp; linarith
      · dsimp; linarith
    · exact hload0.symm.le.trans (load_le_makespan sample3x4 _ 0)
  have hnn : IsNonnegProfile sample3x4 := fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [sample3x4]
  have happrox := makespan_minWorkAlloc_le_card_mul_optMakespan hnn
  simp only [Fintype.card_fin, Nat.cast_ofNat] at happrox
  refine ⟨hload0, hpay0, ?_, hpay1, hmake, happrox⟩
  simp only [Scheduling.Mechanism.utility]
  change (minWorkMechanism (Machine := Fin 3) (Job := Fin 4)).pay sample3x4 0 -
    load sample3x4 (minWorkAlloc sample3x4) 0 = 4
  linarith

/-- `minWorkMechanism` on `(Fin 3, Fin 4)` is DSIC, IR, and realized as a `Mechanism.groves` VCG
mechanism. -/
example :
    let M := minWorkMechanism (Machine := Fin 3) (Job := Fin 4)
    M.IsDSIC ∧ M.IsIR ∧
      ∃ f h, Cslib.GameTheory.Mechanism.IsWelfareMaximizing f ∧
        (∀ m B v, h m (Function.update B m v) = h m B) ∧
        ofGeneralMechanism (Cslib.GameTheory.Mechanism.groves f h) = M :=
  ⟨minWorkMechanism_isDSIC, minWorkMechanism_isIR, exists_groves_eq_minWorkMechanism⟩

/-! ### 2. Concrete `n`-approximation tightness witness for `MinWork` -/

/-- `3 × 3` tightness witness: machine `0` takes `1` on all jobs, machines `1` and `2` take `5 / 4`
on all jobs. `minWorkAlloc` gives makespan `3`, whereas `id` achieves makespan `5 / 4`. -/
noncomputable def tight3x3 : Fin 3 → Fin 3 → ℝ :=
  fun i _ => if i = 0 then 1 else 5 / 4

example :
    makespan tight3x3 (minWorkAlloc tight3x3) = 3 ∧
      optMakespan tight3x3 ≤ 5 / 4 ∧
      ¬ (minWorkMechanism (Machine := Fin 3) (Job := Fin 3)).HasApproxRatioOn
        IsPositiveProfile (5 / 2) := by
  have hall0 : minWorkAlloc tight3x3 = fun _ => 0 := by
    funext j
    rw [minWorkAlloc_eq_iff]
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · simp [tight3x3]; norm_num
    · simp [tight3x3]; norm_num
  have hmake3 : makespan tight3x3 (minWorkAlloc tight3x3) = 3 := by
    rw [hall0]
    refine le_antisymm (makespan_le_iff.mpr fun i => ?_) ?_
    · fin_cases i <;>
        · simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_three, tight3x3]
          norm_num
    · have hl0 : load tight3x3 (fun _ => 0) 0 = 3 := by
        simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_three, tight3x3]
        norm_num
      exact hl0.symm.le.trans (load_le_makespan tight3x3 _ 0)
  have hopt : optMakespan tight3x3 ≤ 5 / 4 := by
    refine (optMakespan_le_makespan tight3x3 id).trans (makespan_le_iff.mpr fun i => ?_)
    fin_cases i <;>
      · simp only [load, rowLoad, Finset.sum_filter, Fin.sum_univ_three, tight3x3, id]
        norm_num
  exact ⟨hmake3, hopt, fun happrox =>
    (card_le_of_minWorkMechanism_hasApproxRatioOn (by decide) happrox).not_gt (by norm_num)⟩

/-! ### 3. Nisan–Ronen `2` lower bound and exact `2`-machine minimax ratio -/

/-- For `2` unrelated machines and `3` jobs (`Fin 2`, `Fin 3`), `2` is the **exact** minimax
deterministic truthful approximation ratio: `minWorkMechanism` is DSIC and `2`-approximate on all
nonnegative profiles, while no DSIC mechanism achieves `199 / 100 < 2` even on positive profiles. -/
example :
    (minWorkMechanism (Machine := Fin 2) (Job := Fin 3)).IsDSIC ∧
      (minWorkMechanism (Machine := Fin 2) (Job := Fin 3)).HasApproxRatioOn IsNonnegProfile 2 ∧
      ¬ ∃ M : Scheduling.Mechanism (Fin 2) (Fin 3),
        M.IsDSIC ∧ M.HasApproxRatioOn IsPositiveProfile (199 / 100) := by
  refine ⟨minWorkMechanism_isDSIC, ?_, fun ⟨M, hdsic, happrox⟩ =>
    (two_le_of_isDSICOn_positive_of_hasApproxRatioOn (by decide) (by decide) M
      (hdsic.isDSICOn _) happrox).not_gt (by norm_num)⟩
  simpa using minWorkMechanism_hasApproxRatioOn_nonneg (Machine := Fin 2) (Job := Fin 3)

/-- General multi-machine instance: on `5` machines and `4` jobs (`Fin 5`, `Fin 4`), no mechanism
that is DSIC on positive rows achieves ratio `7 / 4 < 2`. -/
example (M : Scheduling.Mechanism (Fin 5) (Fin 4))
    (hdsic : M.IsDSICOn (fun _ => { r : Fin 4 → ℝ | ∀ j, 0 < r j })) :
    ¬ M.HasApproxRatioOn IsPositiveProfile (7 / 4) := fun happrox =>
  (two_le_of_isDSICOn_positive_of_hasApproxRatioOn (by decide) (by decide) M hdsic happrox).not_gt
    (by norm_num)

/-! ### 4. Boundary sharpness (`|Machine| = 1` and `|Job| = 1`) -/

/-- Single-machine boundary (`Fin 1`, `Fin 4`): `minWorkMechanism` is DSIC and achieves exact
`1`-approximation (`c = 1 < 2`) on all profiles. -/
example :
    (minWorkMechanism (Machine := Fin 1) (Job := Fin 4)).IsDSIC ∧
      (minWorkMechanism (Machine := Fin 1) (Job := Fin 4)).HasApproxRatioOn (fun _ => True) 1 := by
  refine ⟨minWorkMechanism_isDSIC, fun t _ => ?_⟩
  rw [one_mul, makespan_eq_optMakespan_of_subsingleton_machine]

/-- Identical-machine compatibility (`load_const_eq`), `minWorkMechanism_pay_nonneg`, and
`ofGeneralMechanism_isDSIC` on `sample3x4` / VCG pullback. -/
example :
    load (fun _ => (![2, 5, 3, 7] : Fin 4 → ℝ)) (![0, 0, 0, 1] : Fin 4 → Fin 3) 0 =
      Cslib.Algorithms.Lean.Scheduling.load (![2, 5, 3, 7] : Fin 4 → ℝ)
        (![0, 0, 0, 1] : Fin 4 → Fin 3) 0 ∧
    (∀ i : Fin 3, 0 ≤ (minWorkMechanism (Machine := Fin 3) (Job := Fin 4)).pay sample3x4 i) ∧
    (∀ (G : Cslib.GameTheory.Mechanism (Fin 3) (Fin 4 → Fin 3)),
      G.IsDSIC → (ofGeneralMechanism G).IsDSIC) := by
  have hnn : IsNonnegProfile sample3x4 := fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [sample3x4]
  exact ⟨load_const_eq _ _ _, fun i => minWorkMechanism_pay_nonneg hnn i,
    fun _ hG => ofGeneralMechanism_isDSIC hG⟩

/-- Single-job boundary (`Fin 3`, `Fin 1`): `minWorkMechanism` is DSIC, IR, and achieves exact
`1`-approximation (`c = 1 < 2`) on all nonnegative profiles. -/
example :
    (minWorkMechanism (Machine := Fin 3) (Job := Fin 1)).IsDSIC ∧
      (minWorkMechanism (Machine := Fin 3) (Job := Fin 1)).IsIR ∧
      (minWorkMechanism (Machine := Fin 3) (Job := Fin 1)).HasApproxRatioOn IsNonnegProfile 1 := by
  refine ⟨minWorkMechanism_isDSIC, minWorkMechanism_isIR, fun t ht => ?_⟩
  rw [one_mul]
  exact (makespan_minWorkAlloc_eq_optMakespan_of_subsingleton_job ht).le

/-- Empty-job boundary (`Fin 3`, `Fin 0`): zero makespan, zero payment, and exact `1`-approx. -/
example (t : Fin 3 → Fin 0 → ℝ) :
    makespan t (minWorkAlloc t) = optMakespan t ∧
      (∀ i : Fin 3, (minWorkMechanism (Machine := Fin 3) (Job := Fin 0)).pay t i = 0) := by
  have hnn : IsNonnegProfile t := fun _ j => j.elim0
  exact ⟨makespan_minWorkAlloc_eq_optMakespan_of_subsingleton_job hnn,
    fun i => by simp [minWorkMechanism]⟩

/-- With a single machine (`[Subsingleton (Fin 1)]`), `minWorkMechanism` pays `0` and violates IR
on strictly positive processing times, showing `[Nontrivial Machine]` is necessary in
`minWorkMechanism_isIR`. -/
example :
    let t : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    (minWorkMechanism (Machine := Fin 1) (Job := Fin 1)).utility 0 (t 0) t = -1 ∧
      ¬ (minWorkMechanism (Machine := Fin 1) (Job := Fin 1)).IsIR := by
  dsimp only
  let t : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  have hpay : (minWorkMechanism (Machine := Fin 1) (Job := Fin 1)).pay t 0 = 0 := by
    simp [minWorkMechanism, secondLowestTime]
  have hload : rowLoad (0 : Fin 1) (t 0) (minWorkAlloc t) = 1 := by
    have hflt : (Finset.univ.filter fun j : Fin 1 => minWorkAlloc t j = 0) = {0} := by
      ext j
      fin_cases j
      simp [Subsingleton.elim (minWorkAlloc t 0) 0]
    rw [rowLoad, hflt, Finset.sum_singleton]
  have hut : (minWorkMechanism (Machine := Fin 1) (Job := Fin 1)).utility 0 (t 0) t = -1 := by
    rw [Scheduling.Mechanism.utility, hpay]
    change 0 - rowLoad 0 (t 0) (minWorkAlloc t) = -1
    rw [hload]
    ring
  refine ⟨hut, fun hir => ?_⟩
  have hle := hir 0 t
  linarith

end CslibFrontierTests.GameTheory.UnrelatedScheduling
