/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.HousingMarket.Incentives
public import CslibFrontier.Algorithms.Lean.HousingMarket.SequentialCycles

/-!
# Coalitional incentives, group strategy-proofness, and non-bossiness in housing markets

This module extends the unilateral incentive theory of
`CslibFrontier.Algorithms.Lean.HousingMarket.Incentives` to coalitions and general direct housing
mechanisms (`HousingMechanism n`):

* **Coalitional preference reports** (`Instance.updatePrefs`): coalition `S` replaces its members'
  preference lists while agents outside `S` keep their true lists.
* **Mechanism axioms** (`HousingMechanism.IsIndividuallyRational`,
  `HousingMechanism.IsParetoEfficient`, `HousingMechanism.IsNonBossy`,
  `HousingMechanism.IsWeakGroupStrategyProof`, `HousingMechanism.IsGroupStrategyProof`): following
  `CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic`, `IsWeakGroupStrategyProof` rules out
  coalitional misreports making every member strictly better off ([Bird1984]), while
  `IsGroupStrategyProof` rules out coalitional misreports making every member weakly better off and
  at least one member strictly better off ([Svensson1999]; [Papai2000]).
* **Equivalence with strategy-proofness plus non-bossiness**
  (`HousingMechanism.isGroupStrategyProof_iff`): on strict complete housing preferences, an
  arbitrary mechanism is strongly group strategy-proof if and only if it is strategy-proof and
  non-bossy ([Svensson1999]; [Papai2000]).
* **Coalitional invariance, non-bossiness, and group strategy-proofness of TTC**
  (`Instance.eq_ttc_of_forall_rank_le`, `Instance.ttc_updatePref_eq_of_apply_eq`,
  `HousingMechanism.isNonBossy_topTradingCycles`,
  `HousingMechanism.isGroupStrategyProof_topTradingCycles`,
  `HousingMechanism.isWeakGroupStrategyProof_topTradingCycles`): if a coalition `S` misreports so
  that every member of `S` weakly prefers its new TTC house to its truthful TTC house, then the
  entire TTC allocation is unchanged across *all* agents (`J.ttc = I.ttc`). Consequently, Gale's
  top trading cycles mechanism is non-bossy and strongly (hence weakly) group strategy-proof
  ([Bird1984]; [Svensson1999]; [Papai2000]).

## Main definitions

* `Instance.updatePrefs`: coalitional preference update for `S : Finset (Fin n)`.
* `HousingMechanism.IsIndividuallyRational`, `HousingMechanism.IsParetoEfficient`,
  `HousingMechanism.IsNonBossy`: individual rationality, Pareto efficiency, and non-bossiness of a
  direct housing mechanism.
* `HousingMechanism.IsWeakGroupStrategyProof`, `HousingMechanism.IsGroupStrategyProof`: weak and
  strong coalitional strategy-proofness.

## Main results

* `HousingMechanism.IsGroupStrategyProof.isWeakGroupStrategyProof`,
  `HousingMechanism.IsWeakGroupStrategyProof.isStrategyProof`,
  `HousingMechanism.IsGroupStrategyProof.isNonBossy`: implication hierarchy among incentive axioms.
* `HousingMechanism.isGroupStrategyProof_iff`: `M.IsGroupStrategyProof ↔ M.IsStrategyProof ∧
  M.IsNonBossy` ([Svensson1999]; [Papai2000]).
* `Instance.eq_ttc_of_forall_rank_le`: a coalitional deviation under which no member of `S` is
  strictly hurt leaves `ttc` unchanged for every agent.
* `Instance.ttc_updatePref_eq_of_apply_eq`, `HousingMechanism.isNonBossy_topTradingCycles`: TTC is
  non-bossy.
* `HousingMechanism.isGroupStrategyProof_topTradingCycles`,
  `HousingMechanism.isWeakGroupStrategyProof_topTradingCycles`: TTC is strongly and weakly group
  strategy-proof ([Bird1984]; [Svensson1999]; [Papai2000]).

## References

* [Bird1984]
* [Svensson1999]
* [Papai2000]
* [SchummerVohra2007]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

open Function

namespace Instance

variable {n : ℕ}

@[ext]
theorem ext {I J : Instance n} (h : ∀ i, I.pref i = J.pref i) : I = J := by
  cases I
  cases J
  simpa using funext h

variable (I : Instance n)

/-- The market in which each member `j ∈ S` reports `π j` and every agent `j ∉ S` reports its list
in `I`. -/
@[expose] def updatePrefs (S : Finset (Fin n)) (π : Fin n → Equiv.Perm (Fin n)) : Instance n :=
  ⟨fun j => if j ∈ S then π j else I.pref j⟩

variable {I}

@[simp] theorem updatePrefs_empty (π : Fin n → Equiv.Perm (Fin n)) :
    I.updatePrefs ∅ π = I := by
  ext j
  simp [updatePrefs]

theorem updatePrefs_singleton (i : Fin n) (π : Fin n → Equiv.Perm (Fin n)) :
    I.updatePrefs {i} π = I.updatePref i (π i) := by
  ext j
  rcases eq_or_ne j i with rfl | hji <;> simp [updatePrefs, updatePref, *]

theorem updatePrefs_insert {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S)
    (π : Fin n → Equiv.Perm (Fin n)) :
    I.updatePrefs (insert i S) π = (I.updatePrefs S π).updatePref i (π i) := by
  ext j
  rcases eq_or_ne j i with rfl | hji <;> simp [updatePrefs, updatePref, *]

@[simp] theorem updatePrefs_pref_of_mem {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S)
    (π : Fin n → Equiv.Perm (Fin n)) : (I.updatePrefs S π).pref j = π j :=
  ite_eq_left hj

@[simp] theorem updatePrefs_pref_of_notMem {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (π : Fin n → Equiv.Perm (Fin n)) : (I.updatePrefs S π).pref j = I.pref j :=
  ite_eq_right hj

theorem updatePrefs_rank_of_notMem {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (π : Fin n → Equiv.Perm (Fin n)) : (I.updatePrefs S π).rank j = I.rank j := by
  funext h
  rw [rank, rank, updatePrefs_pref_of_notMem hj]

@[simp] theorem updatePref_self (i : Fin n) : I.updatePref i (I.pref i) = I := by
  ext j
  simp [updatePref]

@[simp] theorem updatePref_idem (i : Fin n) (π₁ π₂ : Equiv.Perm (Fin n)) :
    (I.updatePref i π₁).updatePref i π₂ = I.updatePref i π₂ := by
  ext j
  simp [updatePref]

@[simp] theorem updatePref_pref_self (i : Fin n) (π : Equiv.Perm (Fin n)) :
    (I.updatePref i π).pref i = π := by
  simp [updatePref]

@[simp] theorem updatePref_rank_self (i : Fin n) (π : Equiv.Perm (Fin n)) (h : Fin n) :
    (I.updatePref i π).rank i h = π.symm h := by
  rw [rank, updatePref_pref_self]

/-! ### Coalitional invariance of TTC -/

private theorem eq_ttcRounds_of_forall_rank_le {J : Instance n} {S : Finset (Fin n)}
    (hpref : ∀ j, j ∉ S → J.pref j = I.pref j)
    {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (hR : ∀ x ∈ R, J.ttc x ∈ R)
    (hle : ∀ i ∈ S, i ∈ R → I.rank i (J.ttc i) ≤ I.rank i (I.ttcRounds k R i)) :
    ∀ x ∈ R, J.ttc x = I.ttcRounds k R x := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    intro x hx
    set C := I.cycleAgents R
    have hCS (a : Fin n) (haC : a ∈ C) (haS : a ∈ S) : J.ttc a = I.topChoice R a := by
      have h1 := hle a haS (I.cycleAgents_subset R haC)
      rw [I.ttcRounds_succ_of_mem haC] at h1
      exact I.rank_injective a
        (le_antisymm h1 (I.rank_topChoice_le (hR a (I.cycleAgents_subset R haC)) a))
    let ν : Allocation n :=
      I.cyclePerm (R := R) (C := C) Finset.Subset.rfl fun _ ha => I.topChoice_mem_cycleAgents ha
    have hνC : ∀ b ∈ C, ν b = I.topChoice R b := fun _ hb => I.cyclePerm_apply_of_mem _ _ hb
    have hJle (b : Fin n) (hbC : b ∈ C) : J.rank b (I.topChoice R b) ≤ J.rank b (J.ttc b) := by
      by_cases hbS : b ∈ S
      · rw [hCS b hbC hbS]
      · simpa only [rank, hpref b hbS] using
          I.rank_topChoice_le (hR b (I.cycleAgents_subset R hbC)) b
    have hC_eq (b : Fin n) (hbC : b ∈ C) : J.ttc b = I.topChoice R b := by
      by_contra hne
      exact J.inStrictCore_ttc C ⟨ν, fun a ha => hνC a ha ▸ I.topChoice_mem_cycleAgents ha,
        fun a ha => hνC a ha ▸ hJle a ha, b, hbC,
        hνC b hbC ▸ lt_of_le_of_ne (hJle b hbC) fun h => hne (J.rank_injective b h).symm⟩
    by_cases hxC : x ∈ C
    · rw [hC_eq x hxC, I.ttcRounds_succ_of_mem hxC]
    rw [I.ttcRounds_succ_of_notMem hxC]
    have hmaps : ∀ b ∈ C, J.ttc b ∈ C := fun b hb => hC_eq b hb ▸ I.topChoice_mem_cycleAgents hb
    have hlt : (R \ C).card < R.card := I.card_sdiff_cycleAgents_lt ⟨x, hx⟩
    refine ih (by omega)
      (fun a ha => Finset.mem_sdiff.2 ⟨hR a (Finset.mem_sdiff.1 ha).1,
        fun hm => (Finset.mem_sdiff.1 ha).2 (mem_of_apply_mem J.ttc hmaps hm)⟩)
      (fun i hiS hiR' => by
        simpa only [I.ttcRounds_succ_of_notMem (Finset.mem_sdiff.1 hiR').2] using
          hle i hiS (Finset.mem_sdiff.1 hiR').1)
      x (Finset.mem_sdiff.2 ⟨hx, hxC⟩)

/-- **Coalitional invariance of TTC** ([Bird1984]; [Svensson1999]): if `J` agrees with `I` outside
coalition `S` and every member of `S` weakly prefers its house in `J.ttc` (according to `I`) to its
house in `I.ttc`, then `J.ttc = I.ttc` across all agents. -/
theorem eq_ttc_of_forall_rank_le {J : Instance n} {S : Finset (Fin n)}
    (hpref : ∀ j, j ∉ S → J.pref j = I.pref j)
    (hle : ∀ i ∈ S, I.rank i (J.ttc i) ≤ I.rank i (I.ttc i)) :
    J.ttc = I.ttc := by
  refine Equiv.ext fun x => ?_
  rw [I.ttc_apply]
  exact eq_ttcRounds_of_forall_rank_le hpref (k := n) (by simp)
    (fun _ _ => Finset.mem_univ _) (fun i hi _ => hle i hi) x (Finset.mem_univ x)

/-- **Non-bossiness of `Instance.ttc`**: if agent `i` receives the same house under `(I.updatePref
i π).ttc` as under `I.ttc`, then the entire TTC allocation is unchanged. -/
theorem ttc_updatePref_eq_of_apply_eq {i : Fin n} {π : Equiv.Perm (Fin n)}
    (h : (I.updatePref i π).ttc i = I.ttc i) :
    (I.updatePref i π).ttc = I.ttc := by
  refine I.eq_ttc_of_forall_rank_le (S := {i})
    (fun j hj => I.updatePref_pref_of_ne π (Finset.notMem_singleton.1 hj)) fun j hj => ?_
  rw [Finset.mem_singleton.1 hj, h]

end Instance

/-! ### Mechanism axioms and Pápai–Svensson equivalence -/

namespace HousingMechanism

variable {n : ℕ}

/-- A housing mechanism is **individually rational** if it outputs an individually rational
allocation on every market. -/
@[expose] def IsIndividuallyRational (M : HousingMechanism n) : Prop :=
  ∀ I : Instance n, I.IsIndividuallyRational (M I)

/-- A housing mechanism is **Pareto efficient** if it outputs a Pareto-efficient allocation on
every market. -/
@[expose] def IsParetoEfficient (M : HousingMechanism n) : Prop :=
  ∀ I : Instance n, I.IsParetoEfficient (M I)

/-- A housing mechanism is **non-bossy** ([Svensson1999]; [Papai2000]) if no single agent can
change the overall allocation by misreporting without changing its own assigned house. -/
@[expose] def IsNonBossy (M : HousingMechanism n) : Prop :=
  ∀ (I : Instance n) (i : Fin n) (π : Equiv.Perm (Fin n)),
    M (I.updatePref i π) i = M I i → M (I.updatePref i π) = M I

/-- A housing mechanism is **weakly group strategy-proof** ([Bird1984]) if no nonempty coalition
`S` can jointly misreport preferences so that *every* member of `S` receives a strictly preferred
house. -/
@[expose] def IsWeakGroupStrategyProof (M : HousingMechanism n) : Prop :=
  ∀ (I : Instance n) (S : Finset (Fin n)) (π : Fin n → Equiv.Perm (Fin n)),
    S.Nonempty → ¬ ∀ i ∈ S, I.rank i (M (I.updatePrefs S π) i) < I.rank i (M I i)

/-- A housing mechanism is **(strongly) group strategy-proof** ([Svensson1999]; [Papai2000]) if no
coalition `S` can jointly misreport preferences so that every member of `S` is weakly better off
and at least one member of `S` is strictly better off. -/
@[expose] def IsGroupStrategyProof (M : HousingMechanism n) : Prop :=
  ∀ (I : Instance n) (S : Finset (Fin n)) (π : Fin n → Equiv.Perm (Fin n)),
    ¬ ((∀ i ∈ S, I.rank i (M (I.updatePrefs S π) i) ≤ I.rank i (M I i)) ∧
      ∃ i ∈ S, I.rank i (M (I.updatePrefs S π) i) < I.rank i (M I i))

theorem IsGroupStrategyProof.isWeakGroupStrategyProof {M : HousingMechanism n}
    (h : M.IsGroupStrategyProof) : M.IsWeakGroupStrategyProof :=
  fun I S π ⟨i₀, hi₀⟩ hlt => h I S π ⟨fun i hi => (hlt i hi).le, i₀, hi₀, hlt i₀ hi₀⟩

theorem IsWeakGroupStrategyProof.isStrategyProof {M : HousingMechanism n}
    (h : M.IsWeakGroupStrategyProof) : M.IsStrategyProof := by
  intro I i π
  by_contra hlt
  exact h I {i} (fun _ => π) ⟨i, Finset.mem_singleton_self i⟩ fun j hj => by
    simpa only [Finset.mem_singleton.1 hj, I.updatePrefs_singleton] using not_le.1 hlt

theorem IsGroupStrategyProof.isStrategyProof {M : HousingMechanism n}
    (h : M.IsGroupStrategyProof) : M.IsStrategyProof :=
  h.isWeakGroupStrategyProof.isStrategyProof

theorem IsGroupStrategyProof.isNonBossy {M : HousingMechanism n}
    (h : M.IsGroupStrategyProof) : M.IsNonBossy := by
  intro I i π heq
  by_contra hne
  obtain ⟨j, hj_ne⟩ := not_forall.1 (mt Equiv.ext hne)
  have hji : j ≠ i := fun h0 => hj_ne (h0 ▸ heq)
  rcases lt_or_gt_of_ne fun hr => hj_ne (I.rank_injective j hr) with hlt | hgt
  · have hupd : I.updatePrefs {i, j} (fun k => if k = i then π else I.pref k) =
        I.updatePref i π := by
      ext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [Instance.updatePrefs, Instance.updatePref_pref_of_ne, *]
    exact h I {i, j} _ ⟨(Finset.forall_mem_insert _ _ _).2 ⟨by rw [hupd, heq],
      fun _ hk => by simpa only [Finset.mem_singleton.1 hk, hupd] using hlt.le⟩,
      j, by simp, hupd.symm ▸ hlt⟩
  · set I' := I.updatePref i π
    have hupd' : I'.updatePrefs {i, j} I.pref = I := by
      ext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [Instance.updatePrefs, I', Instance.updatePref_pref_of_ne, *]
    have hrj : I'.rank j = I.rank j := I.updatePref_rank_of_ne π hji
    have hj_lt : I'.rank j (M (I'.updatePrefs {i, j} I.pref) j) < I'.rank j (M I' j) := by
      rwa [hupd', hrj]
    exact h I' {i, j} I.pref ⟨(Finset.forall_mem_insert _ _ _).2 ⟨by rw [hupd', heq],
      fun _ hk => by simpa only [Finset.mem_singleton.1 hk] using hj_lt.le⟩,
      j, by simp, hj_lt⟩

/-! #### Two-slot masking permutation for `(SP ∧ NonBossy) → GSP` -/

private def topTwoPerm (a b : Fin n) : Equiv.Perm (Fin n) :=
  let z₀ : Fin n := ⟨0, a.pos⟩
  let σ₀ : Equiv.Perm (Fin n) := Equiv.swap z₀ a
  if h : a = b then
    σ₀
  else
    have hn2 : 2 ≤ n := by
      have hne : a.val ≠ b.val := Fin.val_ne_of_ne h
      omega
    let z₁ : Fin n := ⟨1, by omega⟩
    (Equiv.swap z₁ (σ₀.symm b)).trans σ₀

private theorem topTwoPerm_apply_zero (a b : Fin n) :
    topTwoPerm a b ⟨0, a.pos⟩ = a := by
  classical
  dsimp only [topTwoPerm]
  set z₀ : Fin n := ⟨0, a.pos⟩
  set σ₀ : Equiv.Perm (Fin n) := Equiv.swap z₀ a
  split_ifs with h
  · exact Equiv.swap_apply_left z₀ a
  · have hz01 : z₀ ≠ ⟨1, by have := Fin.val_ne_of_ne h; omega⟩ :=
      fun heq => by simpa [z₀] using congrArg Fin.val heq
    have hz0k : z₀ ≠ σ₀.symm b := fun heq => h (by simpa [σ₀] using congrArg σ₀ heq)
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hz01 hz0k]
    exact Equiv.swap_apply_left z₀ a

private theorem topTwoPerm_symm_fst_val (a b : Fin n) :
    ((topTwoPerm a b).symm a).val = 0 := by
  simpa using congrArg (fun x => ((topTwoPerm a b).symm x).val) (topTwoPerm_apply_zero a b).symm

private theorem eq_or_eq_of_topTwoPerm_symm_le {a b x : Fin n}
    (hle : (topTwoPerm a b).symm x ≤ (topTwoPerm a b).symm b) :
    x = a ∨ x = b := by
  classical
  have ha0 : (topTwoPerm a b).symm a = ⟨0, a.pos⟩ := Fin.ext (topTwoPerm_symm_fst_val a b)
  by_cases hab : a = b
  · subst hab
    have hx0 : ((topTwoPerm a a).symm x).val = 0 :=
      Nat.eq_zero_of_le_zero (by simpa only [Fin.le_def, ha0] using hle)
    exact Or.inl ((topTwoPerm a a).symm.injective ((Fin.ext hx0).trans ha0.symm))
  · have hn2 : 2 ≤ n := by have := Fin.val_ne_of_ne hab; omega
    have hb1 : (topTwoPerm a b).symm b = ⟨1, hn2⟩ :=
      (topTwoPerm a b).injective (by simp [topTwoPerm, hab, Equiv.trans_apply])
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa only [Fin.le_def, hb1] using hle) with
      hx0 | hx1
    · exact Or.inl ((topTwoPerm a b).symm.injective ((Fin.ext hx0).trans ha0.symm))
    · exact Or.inr ((topTwoPerm a b).symm.injective ((Fin.ext hx1).trans hb1.symm))

/-- **Equivalence of group strategy-proofness with strategy-proofness and non-bossiness**
([Svensson1999]; [Papai2000]): on strict complete housing preferences, a direct mechanism `M` is
strongly group strategy-proof if and only if it is strategy-proof and non-bossy. -/
theorem isGroupStrategyProof_iff {M : HousingMechanism n} :
    M.IsGroupStrategyProof ↔ M.IsStrategyProof ∧ M.IsNonBossy := by
  refine ⟨fun h => ⟨h.isStrategyProof, h.isNonBossy⟩, ?_⟩
  rintro ⟨hSP, hNB⟩ I S π ⟨hle, i₀, hi₀, hlt⟩
  classical
  set J := I.updatePrefs S π
  let πStar : Fin n → Equiv.Perm (Fin n) := fun i => topTwoPerm (M J i) (M I i)
  -- Step 1: moving `T ⊆ S` from `J` to `πStar` preserves `M _ = M J`.
  have hJ_inv (T : Finset (Fin n)) : T ⊆ S → M (J.updatePrefs T πStar) = M J := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hiT ih =>
      intro hTS
      have hT := ih ((Finset.subset_insert i T).trans hTS)
      set JT := J.updatePrefs T πStar
      rw [J.updatePrefs_insert hiT]
      set J' := JT.updatePref i (πStar i)
      have hsp : ((πStar i).symm (M J' i)).val = 0 := by
        simpa [J', hT, Fin.le_def, πStar, topTwoPerm_symm_fst_val] using hSP J' i (JT.pref i)
      have heq_house : M J' i = M JT i := hT ▸ (πStar i).symm.injective
        (Fin.ext (hsp.trans (topTwoPerm_symm_fst_val (M J i) (M I i)).symm))
      exact (hNB JT i (πStar i) heq_house).trans hT
  -- Step 2: moving `T ⊆ S` from `I` to `πStar` preserves `M _ = M I`.
  have hI_inv (T : Finset (Fin n)) : T ⊆ S → M (I.updatePrefs T πStar) = M I := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hiT ih =>
      intro hTS
      have hT := ih ((Finset.subset_insert i T).trans hTS)
      set IT := I.updatePrefs T πStar
      rw [I.updatePrefs_insert hiT]
      set I' := IT.updatePref i (πStar i)
      have hsp_back : (πStar i).symm (M I' i) ≤ (πStar i).symm (M I i) := by
        simpa [I', hT] using hSP I' i (IT.pref i)
      have heq_house : M I' i = M IT i := by
        rw [hT]
        rcases eq_or_eq_of_topTwoPerm_symm_le hsp_back with hMJ | hMI
        · have hsp_fwd : I.rank i (M I i) ≤ I.rank i (M I' i) := by
            simpa only [IT, I', I.updatePrefs_rank_of_notMem hiT πStar, hT] using
              hSP IT i (πStar i)
          exact hMJ.trans (I.rank_injective i
            (le_antisymm (hle i (hTS (Finset.mem_insert_self i T))) (hMJ ▸ hsp_fwd)))
        · exact hMI
      exact (hNB IT i (πStar i) heq_house).trans hT
  -- Step 3: `J.updatePrefs S πStar = I.updatePrefs S πStar`, hence `M J = M I`.
  have hsame : J.updatePrefs S πStar = I.updatePrefs S πStar := by
    ext k
    by_cases hkS : k ∈ S <;> simp [Instance.updatePrefs, J, hkS]
  rw [← hJ_inv S Finset.Subset.rfl, hsame, hI_inv S Finset.Subset.rfl] at hlt
  exact lt_irrefl _ hlt

/-! ### Top trading cycles properties -/

theorem isIndividuallyRational_topTradingCycles :
    (topTradingCycles (n := n)).IsIndividuallyRational :=
  fun I => I.isIndividuallyRational_ttc

theorem isParetoEfficient_topTradingCycles :
    (topTradingCycles (n := n)).IsParetoEfficient :=
  fun I => I.isParetoEfficient_ttc

/-- Gale's top trading cycles mechanism is non-bossy ([Svensson1999]; [Papai2000]). -/
theorem isNonBossy_topTradingCycles : (topTradingCycles (n := n)).IsNonBossy :=
  fun I _ _ h => I.ttc_updatePref_eq_of_apply_eq h

/-- **Strong group strategy-proofness of top trading cycles** ([Bird1984]; [Svensson1999];
[Papai2000]): no coalition can jointly misreport preferences so that all members are weakly better
off and at least one member is strictly better off. -/
theorem isGroupStrategyProof_topTradingCycles :
    (topTradingCycles (n := n)).IsGroupStrategyProof :=
  isGroupStrategyProof_iff.2 ⟨isStrategyProof_topTradingCycles, isNonBossy_topTradingCycles⟩

/-- **Weak group strategy-proofness of top trading cycles** ([Bird1984]): no nonempty coalition can
jointly misreport preferences so that every member is strictly better off. -/
theorem isWeakGroupStrategyProof_topTradingCycles :
    (topTradingCycles (n := n)).IsWeakGroupStrategyProof :=
  isGroupStrategyProof_topTradingCycles.isWeakGroupStrategyProof

end HousingMechanism

end Cslib.Algorithms.Lean.HousingMarket
