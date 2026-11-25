/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.SectionPairing
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Decomposition
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.StageParts
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.BlockCols
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal stage-step synthesis for `{⊕, ∧, 1}` circuits

Internal stage sets (`xGroupSet`, `zhegPairIdx`, `zhegOddIdx`, `stageSet`) and inductive stage
synthesis (`synth_stage_step`) consumed privately by `UpperBound`; never re-exported through
`Zhegalkin`.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.xGroupSet`, `zhegPairIdx`, `zhegOddIdx`, `stageSet`:
  stage wire invariants and active index sets.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.synth_stage_step`: full-stage `CostSynthesis` step.
-/

public section

open Finset

namespace Cslib.Circuits.Boolean.Zhegalkin

section StageStep

variable {n M k : ℕ} {f : BooleanFunction n}

/-- Nonempty block sums of input wires over width-`s` blocks. -/
@[expose] def xGroupSet (n s : ℕ) : Set (BooleanFunction n) :=
  {g | ∃ (q : ℕ) (T : Finset (Fin n)),
    T.Nonempty ∧ (∀ j ∈ T, j.1 / s = q) ∧ g = fun x => ∑ j ∈ T, x j}

/-- Section-peer pairs `(u, (r₁, r₂))` having at least one paired `ZhegCol`. -/
@[expose] def zhegPairIdx (d : PaddedDecomp f M k) (s p : ℕ) :
    Finset (SectionPeer (2 * M)) :=
  ((range ((2 * M) ⌈/⌉ p)).product univ).filter fun up =>
    (pairedCols (hasZhegCol d s) p up.sec up.row₁ up.row₂).Nonempty

/-- Rows `r` having at least one odd-leftover `ZhegCol`. -/
@[expose] def zhegOddIdx (d : PaddedDecomp f M k) (s p : ℕ) : Finset (Fin (2 * M)) :=
  univ.filter fun r : Fin (2 * M) => (oddCols (hasZhegCol d s) p r).Nonempty

/-- Wires available before synthesizing conjunction-gate stage `q₀`. -/
@[expose] def stageSet (d : PaddedDecomp f M k) (s p q₀ : ℕ) : Set (BooleanFunction n) :=
  inputs n ∪ {constZero n, constOne n} ∪ xGroupSet n s ∪
    {g | ∃ i : Fin M, i.1 / s < q₀ ∧ g = d.gFn i} ∪
    {g | ∃ cg : Additive.FullCol M s, cg.block.1 < q₀ ∧ g = zhegColVal d (.inr cg)} ∪
    {g | ∃ up ∈ zhegPairIdx d s p, (up.row₁.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up}

/-- Stage wires augmented with stage-`q₀` paired and odd shared sums. -/
private def midSet (d : PaddedDecomp f M k) (s p q₀ : ℕ) : Set (BooleanFunction n) :=
  stageSet d s p q₀ ∪
    (⋃ up ∈ (zhegPairIdx d s p).filter (fun up => (up.row₁.1 / 2) / s = q₀),
      {zhegPairVal d s p up}) ∪
    (⋃ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
      {zhegOddVal d s p r})

/-- First `b` conjunction wires already synthesized within stage `q₀`. -/
private def intraSet (d : PaddedDecomp f M k) (s q₀ b : ℕ) : Set (BooleanFunction n) :=
  {g | ∃ i : Fin M, i.1 / s = q₀ ∧ i.1 % s < b ∧ g = d.gFn i}

/-- Indices of the first `b` gates within stage `q₀`. -/
private def stageGates (M s q₀ b : ℕ) : Finset (Fin M) :=
  univ.filter fun i : Fin M => i.1 / s = q₀ ∧ i.1 % s < b

private theorem synth_row_in_stage (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ b : ℕ) (r : Fin (2 * M)) (hr_stage : (r.1 / 2) / s = q₀) (hr_mod : (r.1 / 2) % s = b) :
    CostSynthesis interpretation andCost (midSet d s p q₀ ∪ intraSet d s q₀ b)
      {hFn d r} (p + s) 0 := by
  have hzero_mem : constZero n ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
    have h0 : constZero n ∈ ({constZero n, constOne n} : Set (BooleanFunction n)) := Or.inl rfl
    simp only [midSet, stageSet, Set.mem_union]
    tauto
  have hmem : ∀ idx ∈ zhegRowParts d s p r,
      zhegPartVal d s p r idx ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
    intro idx hidx
    unfold zhegRowParts at hidx
    rcases mem_union.mp hidx with h1234 | h5
    · rcases mem_union.mp h1234 with h123 | h4
      · rcases mem_union.mp h123 with h12 | h3
        · rcases mem_union.mp h12 with h1 | h2
          · split_ifs at h1 with hcH
            · rw [mem_singleton.mp h1]
              have h1' : zhegPartVal d s p r .constOne ∈
                  ({constZero n, constOne n} : Set (BooleanFunction n)) := Or.inr rfl
              simp only [midSet, stageSet, Set.mem_union]
              tauto
            · exact (notMem_empty _ h1).elim
          · obtain ⟨r', hr', rfl⟩ := mem_map.mp h2
            have hne := (mem_filter.mp hr').2
            let up : ℕ × (Fin (2 * M) × Fin (2 * M)) := (r.1 / p, (min r r', max r r'))
            have hup_mem : up ∈ zhegPairIdx d s p :=
              mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (div_lt_ceilDiv r.isLt hp),
                mem_univ _⟩, hne⟩
            have hmin_le : ((min r r').1 / 2) / s ≤ q₀ := by
              rw [← hr_stage]
              exact Nat.div_le_div_right (Nat.div_le_div_right (min_le_left r r'))
            rcases lt_or_eq_of_le hmin_le with hlt_q | heq_q
            · have hp_mem : zhegPartVal d s p r (peerEmb M r') ∈
                  {g | ∃ up ∈ zhegPairIdx d s p,
                    (up.2.1.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up} :=
                ⟨up, hup_mem, hlt_q, rfl⟩
              simp only [midSet, stageSet, Set.mem_union]
              tauto
            · have hp_mem : zhegPartVal d s p r (peerEmb M r') ∈
                  ⋃ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
                    {zhegPairVal d s p up} := by
                rw [Set.mem_iUnion₂]
                exact ⟨up, mem_filter.mpr ⟨hup_mem, heq_q⟩, rfl⟩
              simp only [midSet, Set.mem_union]
              tauto
        · split_ifs at h3 with hne
          · rw [mem_singleton.mp h3]
            have ho_mem : zhegPartVal d s p r .odd ∈
                ⋃ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
                  {zhegOddVal d s p r} := by
              rw [Set.mem_iUnion₂]
              exact ⟨r, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ r, hne⟩, hr_stage⟩, rfl⟩
            simp only [midSet, Set.mem_union]
            tauto
          · exact (notMem_empty _ h3).elim
      · split_ifs at h4 with hne
        · rw [mem_singleton.mp h4]
          have htail_mem : zhegPartVal d s p r .xTail ∈ xGroupSet n s :=
            ⟨n / s, Additive.matrixTailSet d.aX s r, hne,
              fun _ hj => Additive.div_eq_of_mem_matrixTailSet hj, rfl⟩
          simp only [midSet, stageSet, Set.mem_union]
          tauto
        · exact (notMem_empty _ h4).elim
    · obtain ⟨ℓ, hℓ, rfl⟩ := mem_map.mp h5
      obtain ⟨_, hdiv, hlt, _⟩ := mem_filter.mp hℓ
      have hmod_lt : ℓ.1 % s < b := by
        have h1 := Nat.div_add_mod ℓ.1 s
        have h2 := Nat.div_add_mod (r.1 / 2) s
        rw [hdiv, hr_stage] at h1
        rw [hr_stage, hr_mod] at h2
        omega
      exact Or.inr ⟨ℓ, hdiv.trans hr_stage, hmod_lt, rfl⟩
  have hsum := sum_of_mem_of_zero (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) rfl (fun _ => rfl) rfl hzero_mem (zhegRowParts d s p r)
    (zhegPartVal d s p r) hmem
  have hfun : (fun x => ∑ idx ∈ zhegRowParts d s p r, zhegPartVal d s p r idx x) = hFn d r :=
    funext (sum_zhegRowParts_eq d hs p r)
  rw [hfun] at hsum
  have hcard := card_zhegRowParts_le d hs hp r
  exact hsum.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl

private theorem synth_intra_loop (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ b : ℕ) :
    CostSynthesis interpretation andCost (midSet d s p q₀) (intraSet d s q₀ b)
      (∑ _ ∈ stageGates M s q₀ b, (2 * (p + s) + 1))
      (∑ i ∈ stageGates M s q₀ b, if i.1 < k then 1 else 0) := by
  induction b with
  | zero =>
    have hempty_gates : stageGates M s q₀ 0 = ∅ := by
      ext i
      simp [stageGates]
    have hempty_set : intraSet d s q₀ 0 = ∅ := by
      ext g
      simp [intraSet]
    rw [hempty_gates, hempty_set, sum_empty, sum_empty]
    exact CostSynthesis.of_subset (Set.empty_subset _)
  | succ b ih =>
    by_cases hvalid : b < s ∧ q₀ * s + b < M
    · obtain ⟨hbs, hiM⟩ := hvalid
      let i₀ : Fin M := ⟨q₀ * s + b, hiM⟩
      have hi₀_div : i₀.1 / s = q₀ := by
        dsimp only [i₀]
        rw [mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt hbs, add_zero]
      have hi₀_mod : i₀.1 % s = b := by
        dsimp only [i₀]
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hbs]
      let r₀ : Fin (2 * M) := ⟨2 * i₀.1, by omega⟩
      let r₁ : Fin (2 * M) := ⟨2 * i₀.1 + 1, by omega⟩
      have hr₀_half : r₀.1 / 2 = i₀.1 := by dsimp [r₀]; omega
      have hr₁_half : r₁.1 / 2 = i₀.1 := by dsimp [r₁]; omega
      have hh0 := synth_row_in_stage d hs hp q₀ b r₀ (hr₀_half ▸ hi₀_div) (hr₀_half ▸ hi₀_mod)
      have hh1 := synth_row_in_stage d hs hp q₀ b r₁ (hr₁_half ▸ hi₀_div) (hr₁_half ▸ hi₀_mod)
      have hg_step : CostSynthesis interpretation andCost
          (midSet d s p q₀ ∪ intraSet d s q₀ b) {d.gFn i₀}
          (2 * (p + s) + 1) (if i₀.1 < k then 1 else 0) := by
        by_cases hik : i₀.1 < k
        · let args : Fin 2 → BooleanFunction n := fun t => if t.1 = 0 then hFn d r₀ else hFn d r₁
          have hand_raw := CostSynthesis.gate (I := interpretation) (w := andCost)
            (s := (midSet d s p q₀ ∪ intraSet d s q₀ b) ∪ ({hFn d r₀} ∪ {hFn d r₁}))
            Op.and args fun t => by
              dsimp only [args]
              split_ifs
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          have hfun_eq : (fun x => interpretation Op.and (fun t => args t x)) = d.gFn i₀ := by
            funext x
            rw [d.gFn_lt i₀ hik x]
            rfl
          rw [hfun_eq] at hand_raw
          have hcomb := (hh0.union hh1).trans hand_raw
          exact hcomb.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by simp [hik])
        · have hge : k ≤ i₀.1 := Nat.le_of_not_lt hik
          have h0_mem : d.gFn i₀ ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
            rw [d.gFn_ge i₀ hge]
            have h0 : constZero n ∈ ({constZero n, constOne n} : Set (BooleanFunction n)) :=
              Or.inl rfl
            simp only [midSet, stageSet, Set.mem_union]
            tauto
          exact (CostSynthesis.of_mem h0_mem).mono Set.Subset.rfl Set.Subset.rfl
            (by omega) (by simp [hik])
      have htot := ih.comp hg_step
      have hset_eq : intraSet d s q₀ b ∪ {d.gFn i₀} = intraSet d s q₀ (b + 1) := by
        ext g
        simp only [intraSet, Set.mem_union, Set.mem_ofPred, Set.mem_singleton_iff]
        constructor
        · rintro (⟨i, hd, hm, rfl⟩ | rfl)
          · exact ⟨i, hd, Nat.lt_succ_of_lt hm, rfl⟩
          · exact ⟨i₀, hi₀_div, by omega, rfl⟩
        · rintro ⟨i, hd, hm, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact Or.inl ⟨i, hd, hlt, rfl⟩
          · refine Or.inr (congrArg d.gFn (Fin.ext ?_))
            rw [← Nat.div_add_mod i.1 s, hd, heq]
            dsimp only [i₀]
            ring
      have hgates_eq : stageGates M s q₀ (b + 1) = insert i₀ (stageGates M s q₀ b) := by
        ext i
        simp only [stageGates, mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨hd, hm⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact Or.inr ⟨hd, hlt⟩
          · refine Or.inl (Fin.ext ?_)
            rw [← Nat.div_add_mod i.1 s, hd, heq]
            dsimp only [i₀]
            ring
        · rintro (rfl | ⟨hd, hlt⟩)
          · exact ⟨hi₀_div, by omega⟩
          · exact ⟨hd, Nat.lt_succ_of_lt hlt⟩
      have hi₀_notMem : i₀ ∉ stageGates M s q₀ b := by
        simp [stageGates, hi₀_mod]
      rw [hset_eq] at htot
      rw [hgates_eq, sum_insert hi₀_notMem, sum_insert hi₀_notMem]
      exact htot.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    · have hsame_gates : stageGates M s q₀ (b + 1) = stageGates M s q₀ b := by
        ext i
        simp only [stageGates, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hd, hm⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact ⟨hd, hlt⟩
          · exfalso
            apply hvalid
            refine ⟨heq ▸ Nat.mod_lt i.1 hs, ?_⟩
            have hi_eq : q₀ * s + b = i.1 := by
              have hdiv := Nat.div_add_mod' i.1 s
              rwa [hd, heq] at hdiv
            exact hi_eq ▸ i.isLt
        · rintro ⟨hd, hlt⟩
          exact ⟨hd, Nat.lt_succ_of_lt hlt⟩
      have hsame_set : intraSet d s q₀ (b + 1) = intraSet d s q₀ b := by
        ext g
        simp only [intraSet, Set.mem_ofPred]
        constructor
        · rintro ⟨i, hd, hm, rfl⟩
          have hmem : i ∈ stageGates M s q₀ (b + 1) := mem_filter.mpr ⟨mem_univ i, hd, hm⟩
          rw [hsame_gates] at hmem
          exact ⟨i, (mem_filter.mp hmem).2.1, (mem_filter.mp hmem).2.2, rfl⟩
        · rintro ⟨i, hd, hlt, rfl⟩
          exact ⟨i, hd, Nat.lt_succ_of_lt hlt, rfl⟩
      rw [hsame_gates, hsame_set]
      exact ih

theorem synth_stage_step (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ : ℕ) :
    CostSynthesis interpretation andCost (stageSet d s p q₀) (stageSet d s p (q₀ + 1))
      ((∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.row₁.1 / 2) / s = q₀),
          (#(pairedCols (hasZhegCol d s) p up.sec up.row₁ up.row₂) - 1)) +
        (∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
          (#(oddCols (hasZhegCol d s) p r) - 1)) +
        (∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) +
        (if q₀ < M / s then 2 ^ s - s - 1 else 0))
      (∑ i ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀),
        if i.1 < k then 1 else 0) := by
  have hcol_avail (c : ZhegCol n M s)
      (hc : match c with | .inl _ => True | .inr cg => cg.1.1 < q₀) :
      zhegColVal d c ∈ stageSet d s p q₀ := by
    cases c with
    | inl cx =>
      have hx : zhegColVal d (.inl cx) ∈ xGroupSet n s := by
        refine ⟨cx.1.1, cx.2.1.map (Additive.fullBlockEmb cx.1), cx.2.2.map, ?_, ?_⟩
        · intro j hj
          obtain ⟨a, _, rfl⟩ := mem_map.mp hj
          exact Additive.fullBlockEmb_div cx.1 a
        · funext x
          rw [sum_map]
          rfl
      simp only [stageSet, Set.mem_union]
      tauto
    | inr cg =>
      have hg : zhegColVal d (.inr cg) ∈
          {g | ∃ cg' : Additive.FullCol M s, cg'.1.1 < q₀ ∧ g = zhegColVal d (.inr cg')} :=
        ⟨cg, hc, rfl⟩
      simp only [stageSet, Set.mem_union]
      tauto
  -- Substep A1: Paired sums first needed at stage `q₀`.
  let pairQ := (zhegPairIdx d s p).filter fun up => (up.2.1.1 / 2) / s = q₀
  have hpair_one (up : ℕ × (Fin (2 * M) × Fin (2 * M))) (hup : up ∈ pairQ) :
      CostSynthesis interpretation andCost (stageSet d s p q₀) {zhegPairVal d s p up}
        (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) 0 := by
    obtain ⟨hup_idx, hup_q⟩ := mem_filter.mp hup
    refine nonempty_sum_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl _ (mem_filter.mp hup_idx).2 (zhegColVal d) fun c hc => ?_
    apply hcol_avail c
    cases c with
    | inl _ => trivial
    | inr cg =>
      have hc₁ := (mem_pairedCols_imp hc).2.2.2.1
      have hlt : cg.1.1 < (up.2.1.1 / 2) / s := (of_decide_eq_true hc₁).1
      omega
  have hpairs := CostSynthesis.biUnion pairQ (fun up => {zhegPairVal d s p up})
    (fun up => #(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) (fun _ => 0) hpair_one
  -- Substep A2: Odd sums at stage `q₀`.
  let oddQ := (zhegOddIdx d s p).filter fun r => (r.1 / 2) / s = q₀
  have hodd_one (r : Fin (2 * M)) (hr : r ∈ oddQ) :
      CostSynthesis interpretation andCost (stageSet d s p q₀) {zhegOddVal d s p r}
        (#(oddCols (hasZhegCol d s) p r) - 1) 0 := by
    obtain ⟨hr_idx, hr_q⟩ := mem_filter.mp hr
    refine nonempty_sum_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl _ (mem_filter.mp hr_idx).2 (zhegColVal d) fun c hc => ?_
    apply hcol_avail c
    cases c with
    | inl _ => trivial
    | inr cg =>
      have hc_r := mem_oddCols_imp hc
      have hlt : cg.1.1 < (r.1 / 2) / s := (of_decide_eq_true hc_r).1
      omega
  have hodds := CostSynthesis.biUnion oddQ (fun r => {zhegOddVal d s p r})
    (fun r => #(oddCols (hasZhegCol d s) p r) - 1) (fun _ => 0) hodd_one
  have hmid : CostSynthesis interpretation andCost (stageSet d s p q₀) (midSet d s p q₀)
      ((∑ up ∈ pairQ, (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) +
        (∑ r ∈ oddQ, (#(oddCols (hasZhegCol d s) p r) - 1))) 0 := by
    have h := ((CostSynthesis.of_subset Set.Subset.rfl).union hpairs).union hodds
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by simp)
  -- Substep B: Sequential conjunction gates in stage `q₀`.
  have hintra := synth_intra_loop d hs hp q₀ s
  have hgates_s : stageGates M s q₀ s = univ.filter (fun i : Fin M => i.1 / s = q₀) := by
    ext i
    simp [stageGates, Nat.mod_lt i.1 hs]
  rw [hgates_s] at hintra
  have hmid_intra := hmid.comp
    (hintra.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Substep C: Full `g`-block subset sums if `q₀ < M / s`.
  let curGBlockSet : Set (BooleanFunction n) :=
    {g | ∃ cg : Additive.FullCol M s, cg.1.1 = q₀ ∧ g = zhegColVal d (.inr cg)}
  have hgblock_step : CostSynthesis interpretation andCost
      (stageSet d s p q₀ ∪ (midSet d s p q₀ ∪ intraSet d s q₀ s)) curGBlockSet
      (if q₀ < M / s then 2 ^ s - s - 1 else 0) 0 := by
    by_cases hq_lt : q₀ < M / s
    · let qFin : Fin (M / s) := ⟨q₀, hq_lt⟩
      let Fg : Fin s → BooleanFunction n := fun a => d.gFn (Additive.fullBlockEmb qFin a)
      have hFg_mem : ∀ a : Fin s, Fg a ∈ stageSet d s p q₀ ∪
          (midSet d s p q₀ ∪ intraSet d s q₀ s) := fun a =>
        Or.inr (Or.inr ⟨Additive.fullBlockEmb qFin a, Additive.fullBlockEmb_div qFin a,
          Nat.mod_lt _ hs, rfl⟩)
      have hgblock := block_nonempty_subSums (G := Bool) (I := interpretation) (w := andCost)
        (addOp := Op.xor) rfl (fun _ => rfl) rfl Fg hFg_mem
      refine hgblock.mono Set.Subset.rfl ?_ (by simp [hq_lt]) le_rfl
      rintro _ ⟨⟨q', T, hT⟩, hcg, rfl⟩
      have hq_eq : q' = qFin := Fin.ext hcg
      subst hq_eq
      exact ⟨T, hT, rfl⟩
    · refine (CostSynthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (by simp [hq_lt])
        le_rfl
      rintro _ ⟨cg, hcg, rfl⟩
      exact (hq_lt (hcg ▸ cg.1.isLt)).elim
  have hall := hmid_intra.comp hgblock_step
  refine hall.mono Set.Subset.rfl ?_ (by dsimp only [pairQ, oddQ]; rfl) (by simp)
  -- Prove `stageSet d s p (q₀ + 1)` is contained in the synthesized union.
  intro g hg
  rcases hg with
    (((((hg_in | hg_c) | hg_x) | ⟨i, hi, rfl⟩) | ⟨cg, hcg, rfl⟩) | ⟨up, hup, hq, rfl⟩)
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · have h_old : d.gFn i ∈ {g | ∃ i' : Fin M, i'.1 / s < q₀ ∧ g = d.gFn i'} :=
        ⟨i, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · have h_new : d.gFn i ∈ intraSet d s q₀ s := ⟨i, heq, Nat.mod_lt i.1 hs, rfl⟩
      simp only [Set.mem_union]; tauto
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hcg with hlt | heq
    · have h_old : zhegColVal d (.inr cg) ∈
          {g | ∃ cg' : Additive.FullCol M s, cg'.1.1 < q₀ ∧ g = zhegColVal d (.inr cg')} :=
        ⟨cg, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · exact Or.inr ⟨cg, heq, rfl⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | heq
    · have h_old : zhegPairVal d s p up ∈
          {g | ∃ up' ∈ zhegPairIdx d s p,
            (up'.2.1.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up'} :=
        ⟨up, hup, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · have h_new : zhegPairVal d s p up ∈
          ⋃ up' ∈ (zhegPairIdx d s p).filter (fun up' => (up'.2.1.1 / 2) / s = q₀),
            {zhegPairVal d s p up'} := by
        rw [Set.mem_iUnion₂]
        exact ⟨up, mem_filter.mpr ⟨hup, heq⟩, rfl⟩
      simp only [midSet, Set.mem_union]; tauto

end StageStep

end Cslib.Circuits.Boolean.Zhegalkin
