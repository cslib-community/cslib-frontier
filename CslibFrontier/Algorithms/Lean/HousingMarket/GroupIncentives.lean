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
  by_cases hji : j = i
  · subst hji
    simp [updatePrefs, updatePref]
  · simp [updatePrefs, updatePref, hji]

theorem updatePrefs_insert {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S)
    (π : Fin n → Equiv.Perm (Fin n)) :
    I.updatePrefs (insert i S) π = (I.updatePrefs S π).updatePref i (π i) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [updatePrefs, updatePref]
  · simp [updatePrefs, updatePref, hji]

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
  | zero =>
    intro x hx
    simp_all
  | succ k ih =>
    intro x hx
    have hRne : R.Nonempty := ⟨x, hx⟩
    have hk' : (R \ I.cycleAgents R).card ≤ k := by
      have := I.card_sdiff_cycleAgents_lt hRne
      omega
    set C := I.cycleAgents R
    have hCS : ∀ a ∈ C, a ∈ S → J.ttc a = I.topChoice R a := by
      intro a haC haS
      have h1 := hle a haS (I.cycleAgents_subset R haC)
      rw [I.ttcRounds_succ_of_mem haC] at h1
      exact I.rank_injective a
        (le_antisymm h1 (I.rank_topChoice_le (hR a (I.cycleAgents_subset R haC)) a))
    let ν : Allocation n :=
      I.cyclePerm (R := R) (C := C) Finset.Subset.rfl fun _ ha => I.topChoice_mem_cycleAgents ha
    have hνC : ∀ b ∈ C, ν b = I.topChoice R b :=
      fun _ hb => I.cyclePerm_apply_of_mem _ _ hb
    have hJle : ∀ b ∈ C, J.rank b (I.topChoice R b) ≤ J.rank b (J.ttc b) := by
      intro b hbC
      by_cases hbS : b ∈ S
      · rw [hCS b hbC hbS]
      · have hrank : J.rank b = I.rank b := by
          funext h
          rw [rank, rank, hpref b hbS]
        rw [hrank]
        exact I.rank_topChoice_le (hR b (I.cycleAgents_subset R hbC)) b
    have hC_eq : ∀ b ∈ C, J.ttc b = I.topChoice R b := by
      intro b hbC
      by_contra hne
      refine J.inStrictCore_ttc C ⟨ν, fun a ha => ?_, fun a ha => ?_, b, hbC, ?_⟩
      · rw [hνC a ha]
        exact I.topChoice_mem_cycleAgents ha
      · rw [hνC a ha]
        exact hJle a ha
      · rw [hνC b hbC]
        exact lt_of_le_of_ne (hJle b hbC) fun h => hne (J.rank_injective b h).symm
    by_cases hxC : x ∈ C
    · rw [hC_eq x hxC, I.ttcRounds_succ_of_mem hxC]
    rw [I.ttcRounds_succ_of_notMem hxC]
    have hmaps : ∀ b ∈ C, J.ttc b ∈ C := fun b hb => hC_eq b hb ▸ I.topChoice_mem_cycleAgents hb
    refine ih hk' (fun a ha => ?_) (fun i hiS hiR' => ?_) x (Finset.mem_sdiff.2 ⟨hx, hxC⟩)
    · obtain ⟨haR, haC⟩ := Finset.mem_sdiff.1 ha
      exact Finset.mem_sdiff.2 ⟨hR a haR, fun hmem => haC (mem_of_apply_mem J.ttc hmaps hmem)⟩
    · obtain ⟨hiR, hiC⟩ := Finset.mem_sdiff.1 hiR'
      have h1 := hle i hiS hiR
      rwa [I.ttcRounds_succ_of_notMem hiC] at h1

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
    (fun j hj => I.updatePref_pref_of_ne π (Finset.notMem_singleton.1 hj)) ?_
  intro j hj
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
    (h : M.IsGroupStrategyProof) : M.IsWeakGroupStrategyProof := by
  intro I S π ⟨i₀, hi₀⟩ hlt
  exact h I S π ⟨fun i hi => (hlt i hi).le, i₀, hi₀, hlt i₀ hi₀⟩

theorem IsWeakGroupStrategyProof.isStrategyProof {M : HousingMechanism n}
    (h : M.IsWeakGroupStrategyProof) : M.IsStrategyProof := by
  intro I i π
  by_contra hlt
  have h1 : ∀ j ∈ ({i} : Finset (Fin n)),
      I.rank j (M (I.updatePrefs {i} (fun _ => π)) j) < I.rank j (M I j) := by
    intro j hj
    rw [Finset.mem_singleton.1 hj, I.updatePrefs_singleton]
    exact not_le.1 hlt
  exact h I {i} (fun _ => π) (Finset.singleton_nonempty i) h1

theorem IsGroupStrategyProof.isStrategyProof {M : HousingMechanism n}
    (h : M.IsGroupStrategyProof) : M.IsStrategyProof :=
  h.isWeakGroupStrategyProof.isStrategyProof

theorem IsGroupStrategyProof.isNonBossy {M : HousingMechanism n}
    (h : M.IsGroupStrategyProof) : M.IsNonBossy := by
  intro I i π heq
  by_contra hne
  have hex : ∃ j : Fin n, M (I.updatePref i π) j ≠ M I j := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  obtain ⟨j, hj_ne⟩ := hex
  have hji : j ≠ i := fun h0 => hj_ne (h0 ▸ heq)
  rcases lt_or_gt_of_ne fun hr => hj_ne (I.rank_injective j hr) with hlt | hgt
  · let πS : Fin n → Equiv.Perm (Fin n) := fun k => if k = i then π else I.pref k
    have hupd : I.updatePrefs {i, j} πS = I.updatePref i π := by
      ext k
      by_cases hki : k = i
      · subst hki
        simp [Instance.updatePrefs, πS]
      · by_cases hkj : k = j
        · subst hkj
          simp [Instance.updatePrefs, Instance.updatePref_pref_of_ne _ hji, πS, hji]
        · simp [Instance.updatePrefs, Instance.updatePref_pref_of_ne _ hki, hki, hkj]
    refine h I {i, j} πS ⟨fun k hk => ?_, j, by simp, ?_⟩
    · rw [hupd]
      rcases Finset.mem_insert.1 hk with rfl | hkj
      · rw [heq]
      · rw [Finset.mem_singleton.1 hkj]
        exact hlt.le
    · rwa [hupd]
  · set I' := I.updatePref i π
    let πS' : Fin n → Equiv.Perm (Fin n) := fun k => I.pref k
    have hupd' : I'.updatePrefs {i, j} πS' = I := by
      ext k
      by_cases hki : k = i
      · subst hki
        simp [Instance.updatePrefs, πS']
      · by_cases hkj : k = j
        · subst hkj
          simp [Instance.updatePrefs, πS']
        · simp [Instance.updatePrefs, I', Instance.updatePref_pref_of_ne _ hki, hki, hkj]
    have hrank_j : I'.rank j = I.rank j := I.updatePref_rank_of_ne π hji
    refine h I' {i, j} πS' ⟨fun k hk => ?_, j, by simp, ?_⟩
    · rw [hupd']
      rcases Finset.mem_insert.1 hk with rfl | hkj
      · rw [heq]
      · rw [Finset.mem_singleton.1 hkj, hrank_j]
        exact hgt.le
    · rw [hupd', hrank_j]
      exact hgt

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
  · have hn2 : 2 ≤ n := by
      have hne : a.val ≠ b.val := Fin.val_ne_of_ne h
      omega
    have hz01 : z₀ ≠ ⟨1, by omega⟩ := by
      intro heq
      exact absurd (congrArg Fin.val heq) (by simp [z₀])
    have hz0k : z₀ ≠ σ₀.symm b := by
      intro heq
      apply h
      have := congrArg σ₀ heq
      simpa [σ₀] using this
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hz01 hz0k]
    exact Equiv.swap_apply_left z₀ a

private theorem topTwoPerm_symm_fst_val (a b : Fin n) :
    ((topTwoPerm a b).symm a).val = 0 := by
  have := congrArg (topTwoPerm a b).symm (topTwoPerm_apply_zero a b)
  rw [Equiv.symm_apply_apply] at this
  exact congrArg Fin.val this.symm

private theorem eq_or_eq_of_topTwoPerm_symm_le {a b x : Fin n}
    (hle : (topTwoPerm a b).symm x ≤ (topTwoPerm a b).symm b) :
    x = a ∨ x = b := by
  classical
  by_cases hab : a = b
  · subst hab
    have h0 : ((topTwoPerm a a).symm a).val = 0 := topTwoPerm_symm_fst_val a a
    have hx0 : ((topTwoPerm a a).symm x).val = 0 := by
      have : ((topTwoPerm a a).symm x).val ≤ ((topTwoPerm a a).symm a).val := hle
      omega
    have hsymm : (topTwoPerm a a).symm x = (topTwoPerm a a).symm a :=
      Fin.ext (hx0.trans h0.symm)
    exact Or.inl ((topTwoPerm a a).symm.injective hsymm)
  · have hn2 : 2 ≤ n := by
      have hne : a.val ≠ b.val := Fin.val_ne_of_ne hab
      omega
    have h1 : (topTwoPerm a b) ⟨1, by omega⟩ = b := by
      dsimp only [topTwoPerm]
      rw [dite_eq_right hab]
      simp [Equiv.trans_apply]
    have hb1 : (topTwoPerm a b).symm b = ⟨1, by omega⟩ := by
      have hsymm := congrArg (topTwoPerm a b).symm h1
      rw [Equiv.symm_apply_apply] at hsymm
      exact hsymm.symm
    have hx_le : ((topTwoPerm a b).symm x).val ≤ 1 := by
      rw [hb1] at hle
      exact hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx_le with hx0 | hx1
    · left
      have ha0 : (topTwoPerm a b).symm a = ⟨0, a.pos⟩ :=
        Fin.ext (topTwoPerm_symm_fst_val a b)
      have hx0' : (topTwoPerm a b).symm x = ⟨0, a.pos⟩ := Fin.ext hx0
      exact (topTwoPerm a b).symm.injective (hx0'.trans ha0.symm)
    · right
      have hx1' : (topTwoPerm a b).symm x = ⟨1, by omega⟩ := Fin.ext hx1
      exact (topTwoPerm a b).symm.injective (hx1'.trans hb1.symm)

/-- **Equivalence of group strategy-proofness with strategy-proofness and non-bossiness**
([Svensson1999]; [Papai2000]): on strict complete housing preferences, a direct mechanism `M` is
strongly group strategy-proof if and only if it is strategy-proof and non-bossy. -/
theorem isGroupStrategyProof_iff {M : HousingMechanism n} :
    M.IsGroupStrategyProof ↔ M.IsStrategyProof ∧ M.IsNonBossy := by
  constructor
  · exact fun h => ⟨h.isStrategyProof, h.isNonBossy⟩
  · rintro ⟨hSP, hNB⟩ I S π ⟨hle, i₀, hi₀, hlt⟩
    classical
    set J := I.updatePrefs S π
    let πStar : Fin n → Equiv.Perm (Fin n) := fun i => topTwoPerm (M J i) (M I i)
    -- Step 1: moving `T ⊆ S` from `J` to `πStar` preserves `M _ = M J`.
    have hJ_inv : ∀ T : Finset (Fin n), T ⊆ S → M (J.updatePrefs T πStar) = M J := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        rw [J.updatePrefs_empty]
      | @insert i T hiT ih =>
        intro hTS
        have hT : T ⊆ S := (Finset.subset_insert i T).trans hTS
        set JT := J.updatePrefs T πStar
        rw [J.updatePrefs_insert hiT]
        set J' := JT.updatePref i (πStar i)
        have hback : J'.updatePref i (JT.pref i) = JT := by
          simp [J']
        have hsp_step := hSP J' i (JT.pref i)
        rw [hback, ih hT] at hsp_step
        have hzero : (J'.rank i (M J i)).val = 0 := by
          rw [JT.updatePref_rank_self]
          exact topTwoPerm_symm_fst_val (M J i) (M I i)
        have heq_rank : J'.rank i (M J' i) = J'.rank i (M J i) := by
          apply Fin.ext
          have : (J'.rank i (M J' i)).val ≤ (J'.rank i (M J i)).val := hsp_step
          omega
        have heq_house : M J' i = M JT i := by
          rw [ih hT]
          exact J'.rank_injective i heq_rank
        exact (hNB JT i (πStar i) heq_house).trans (ih hT)
    -- Step 2: moving `T ⊆ S` from `I` to `πStar` preserves `M _ = M I`.
    have hI_inv : ∀ T : Finset (Fin n), T ⊆ S → M (I.updatePrefs T πStar) = M I := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        rw [I.updatePrefs_empty]
      | @insert i T hiT ih =>
        intro hTS
        have hiS : i ∈ S := hTS (Finset.mem_insert_self i T)
        have hT : T ⊆ S := (Finset.subset_insert i T).trans hTS
        set IT := I.updatePrefs T πStar
        rw [I.updatePrefs_insert hiT]
        set I' := IT.updatePref i (πStar i)
        have hback : I'.updatePref i (IT.pref i) = IT := by
          simp [I']
        have hsp_back := hSP I' i (IT.pref i)
        rw [hback, ih hT, IT.updatePref_rank_self, IT.updatePref_rank_self] at hsp_back
        have heq_house : M I' i = M IT i := by
          rw [ih hT]
          rcases eq_or_eq_of_topTwoPerm_symm_le hsp_back with hMJ | hMI
          · have hsp_fwd := hSP IT i (πStar i)
            have hrank_IT : IT.rank i = I.rank i := I.updatePrefs_rank_of_notMem hiT πStar
            rw [hrank_IT, ih hT] at hsp_fwd
            change I.rank i (M I i) ≤ I.rank i (M I' i) at hsp_fwd
            rw [hMJ] at hsp_fwd
            exact hMJ.trans (I.rank_injective i (le_antisymm (hle i hiS) hsp_fwd))
          · exact hMI
        exact (hNB IT i (πStar i) heq_house).trans (ih hT)
    -- Step 3: `J.updatePrefs S πStar = I.updatePrefs S πStar`, hence `M J = M I`.
    have hsame : J.updatePrefs S πStar = I.updatePrefs S πStar := by
      ext k
      by_cases hkS : k ∈ S
      · simp [Instance.updatePrefs, hkS]
      · simp [Instance.updatePrefs, J, hkS]
    have hMJ_eq_MI : M J = M I := by
      rw [← hJ_inv S Finset.Subset.rfl, hsame, hI_inv S Finset.Subset.rfl]
    rw [hMJ_eq_MI] at hlt
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
