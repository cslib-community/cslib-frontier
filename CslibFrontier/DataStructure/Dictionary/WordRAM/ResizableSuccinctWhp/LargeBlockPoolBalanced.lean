/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolState
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deamortized Rebalancing Preservation (`LargeBlockPoolBalanced`)

This module proves `CoreValid` and `toPhys` preservation for the `BlockPoolState` rebalancing
primitives (`actStepOne`, `maybeStartBktJob`, `topSwapStepOne`, `topCleanOne`) of the SOSA 2024
resizable succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main results

* `BlockPoolState.CoreValid.actStepOne_spec`, `BlockPoolState.CoreValid.maybeStartBktJob_spec`,
  `BlockPoolState.CoreValid.topSwapStepOne_spec`, `BlockPoolState.CoreValid.topCleanOne_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

open scoped BigOperators

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Finset

namespace BlockPoolState

/-! ## Section 1: `CoreValid` and `toPhys` Preservation of Rebalancing Primitives -/

private theorem add_sub_head_mod {K hd k : ℕ} (_hK : 0 < K) (hhd : hd < 6 * K) (hk : k < 6 * K) :
    ((hd + k) % (6 * K) + 6 * K - hd) % (6 * K) = k := by
  by_cases hlt : hd + k < 6 * K
  · rw [Nat.mod_eq_of_lt hlt, show hd + k + 6 * K - hd = 6 * K + k by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hmod : (hd + k) % (6 * K) = hd + k - 6 * K := by
      conv_lhs => rw [show hd + k = 6 * K + (hd + k - 6 * K) by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show hd + k - 6 * K + 6 * K - hd = k by omega, Nat.mod_eq_of_lt hk]

private theorem head_add_sub_mod {K hd rk : ℕ} (hhd : hd < 6 * K) (hrk : rk < 6 * K) :
    (hd + (rk + 6 * K - hd) % (6 * K)) % (6 * K) = rk := by
  by_cases hle : hd ≤ rk
  · have hlt_sub : rk - hd < 6 * K := by omega
    rw [show rk + 6 * K - hd = 6 * K + (rk - hd) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt hlt_sub, show hd + (rk - hd) = rk by omega, Nat.mod_eq_of_lt hrk]
  · have hlt_sub : rk + 6 * K - hd < 6 * K := by omega
    rw [Nat.mod_eq_of_lt hlt_sub,
      show hd + (rk + 6 * K - hd) = 6 * K + rk by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt hrk]

private theorem head_shift_add_mod {K hd j : ℕ} (_hK : 0 < K) :
    ((hd + K) % (6 * K) + j) % (6 * K) = (hd + (K + j)) % (6 * K) := by
  rw [Nat.add_mod ((hd + K) % (6 * K)), Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

private theorem head_demote_add_mod {K hd j : ℕ} :
    ((hd + 5 * K) % (6 * K) + (K + j)) % (6 * K) = (hd + j) % (6 * K) := by
  rw [Nat.add_mod ((hd + 5 * K) % (6 * K)), Nat.mod_mod, ← Nat.add_mod,
    show hd + 5 * K + (K + j) = 6 * K + (hd + j) by omega, Nat.add_mod_left]

private theorem add_sub_demote_head_mod {K hd rk k₀ : ℕ} (hK : 0 < K)
    (hhd : hd < 6 * K) (hrk : rk < 6 * K) (hk₀ : k₀ < 5 * K)
    (heq : (rk + 6 * K - hd) % (6 * K) = k₀) :
    (rk + 6 * K - (hd + 5 * K) % (6 * K)) % (6 * K) = K + k₀ := by
  have hrk_eq : (hd + k₀) % (6 * K) = rk := by
    rw [← heq]; exact head_add_sub_mod hhd hrk
  have hhd' : (hd + 5 * K) % (6 * K) < 6 * K := Nat.mod_lt _ (by omega)
  have hrew : ((hd + 5 * K) % (6 * K) + (K + k₀)) % (6 * K) = rk := by
    rw [head_demote_add_mod, hrk_eq]
  rw [← hrew]
  exact add_sub_head_mod hK hhd' (by omega)

private theorem add_sub_promote_head_mod {K hd rk k₀ : ℕ} (hK : 0 < K)
    (hhd : hd < 6 * K) (hrk : rk < 6 * K) (hge : K ≤ k₀) (hlt : k₀ < 6 * K)
    (heq : (rk + 6 * K - hd) % (6 * K) = k₀) :
    (rk + 6 * K - (hd + K) % (6 * K)) % (6 * K) = k₀ - K := by
  have hrk_eq : (hd + k₀) % (6 * K) = rk := by
    rw [← heq]; exact head_add_sub_mod hhd hrk
  have hhd' : (hd + K) % (6 * K) < 6 * K := Nat.mod_lt _ (by omega)
  have hrew : ((hd + K) % (6 * K) + (k₀ - K)) % (6 * K) = rk := by
    rw [head_shift_add_mod hK, show K + (k₀ - K) = k₀ by omega, hrk_eq]
  rw [← hrew]
  exact add_sub_head_mod hK hhd' (by omega)

private theorem filter_tail_card_erase {N P₀ : ℕ} {t₁ t₂ : ℕ → ℕ}
    (hP₀ : P₀ < N) (hin : t₁ P₀ = 0 ∨ t₁ P₀ = 2) (hout : ¬(t₂ P₀ = 0 ∨ t₂ P₀ = 2))
    (hoth : ∀ P < N, P ≠ P₀ → ((t₂ P = 0 ∨ t₂ P = 2) ↔ (t₁ P = 0 ∨ t₁ P = 2))) :
    ((Finset.range N).filter (fun P => t₂ P = 0 ∨ t₂ P = 2)).card + 1 =
      ((Finset.range N).filter (fun P => t₁ P = 0 ∨ t₁ P = 2)).card := by
  set S₁ := (Finset.range N).filter (fun P => t₁ P = 0 ∨ t₁ P = 2)
  set S₂ := (Finset.range N).filter (fun P => t₂ P = 0 ∨ t₂ P = 2)
  have hmem : P₀ ∈ S₁ := mem_filter.mpr ⟨mem_range.mpr hP₀, hin⟩
  have heq : S₂ = S₁.erase P₀ := by
    ext P
    simp only [S₁, S₂, mem_erase, mem_filter, mem_range]
    by_cases hp : P = P₀
    · subst hp; simp [hout]
    · exact ⟨fun h => ⟨hp, h.1, (hoth P h.1 hp).mp h.2⟩,
        fun h => ⟨h.2.1, (hoth P h.2.1 hp).mpr h.2.2⟩⟩
  rw [heq]
  exact Finset.card_erase_add_one hmem

private theorem filter_tail_card_insert {N P₀ : ℕ} {t₁ t₂ : ℕ → ℕ}
    (hP₀ : P₀ < N) (hout : ¬(t₁ P₀ = 0 ∨ t₁ P₀ = 2)) (hin : t₂ P₀ = 0 ∨ t₂ P₀ = 2)
    (hoth : ∀ P < N, P ≠ P₀ → ((t₂ P = 0 ∨ t₂ P = 2) ↔ (t₁ P = 0 ∨ t₁ P = 2))) :
    ((Finset.range N).filter (fun P => t₂ P = 0 ∨ t₂ P = 2)).card =
      ((Finset.range N).filter (fun P => t₁ P = 0 ∨ t₁ P = 2)).card + 1 := by
  exact (filter_tail_card_erase hP₀ hin hout (fun P hlt hp => (hoth P hlt hp).symm)).symm

private theorem filter_tail_card_swap {N S D : ℕ} {t : ℕ → ℕ}
    (hS : S < N) (hD : D < N) (hne : S ≠ D) :
    ((Finset.range N).filter
      (fun P => set1 (set1 t S (t D)) D (t S) P = 0 ∨
        set1 (set1 t S (t D)) D (t S) P = 2)).card =
    ((Finset.range N).filter (fun P => t P = 0 ∨ t P = 2)).card := by
  set f : ℕ → ℕ := fun P => if P = S then D else if P = D then S else P
  have hinv : ∀ P, f (f P) = P := fun P => by
    dsimp only [f]
    by_cases hs : P = S
    · subst hs; simp [hne.symm]
    · by_cases hd : P = D
      · subst hd; simp
      · simp [hs, hd]
  exact Finset.card_bij (fun P _ => f P)
    (fun P hP => by
      obtain ⟨hlt, htag⟩ := mem_filter.mp hP
      rw [mem_range] at hlt
      refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
      · dsimp only [f]; split_ifs <;> assumption
      · dsimp only [f]
        by_cases hs : P = S
        · subst hs; rw [ite_eq_left rfl]; rwa [set1_of_ne _ _ _ _ hne, set1_self] at htag
        · rw [ite_eq_right hs]
          by_cases hd : P = D
          · subst hd; rw [ite_eq_left rfl]; rwa [set1_self] at htag
          · rw [ite_eq_right hd]
            rwa [set1_of_ne _ _ _ _ hd, set1_of_ne _ _ _ _ hs] at htag)
    (fun P₁ _ P₂ _ heq => by
      have h := congrArg f heq
      simpa only [hinv] using h)
    (fun Q hQ => by
      obtain ⟨hlt, htag⟩ := mem_filter.mp hQ
      rw [mem_range] at hlt
      refine ⟨f Q, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, hinv Q⟩
      · dsimp only [f]; split_ifs <;> assumption
      · dsimp only [f]
        by_cases hs : Q = S
        · subst hs; rw [ite_eq_left rfl, set1_self]; exact htag
        · rw [ite_eq_right hs]
          by_cases hd : Q = D
          · subst hd; rw [ite_eq_left rfl, set1_of_ne _ _ _ _ hne, set1_self]; exact htag
          · rw [ite_eq_right hd, set1_of_ne _ _ _ _ hd, set1_of_ne _ _ _ _ hs]; exact htag)

/-- `actStepOne` preserves `CoreValid`, keeps swap indices `< nSide`, preserves `bktCount` for all
buckets, and preserves every `(b', loc')` item lookup across `applyOptSwap`. -/
theorem CoreValid.actStepOne_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    {b : ℕ} (hb : b < bp.M)
    (hprom_q : bp.actCode b = bp.K → bp.q b < bp.maxSlabs) :
    let (bp', osw) := bp.actStepOne b
    bp'.CoreValid ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' : ℕ) (loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap osw arr (bp'.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  have hK := hv.K_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, hcur_le_r⟩ := hv.bkt_bounds b hb
  unfold actStepOne
  by_cases hc0 : bp.actCode b = 0
  · rw [ite_eq_left hc0]
    exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
  · rw [ite_eq_right hc0]
    obtain ⟨hP_lt, hP_tag, hP_m1⟩ := hv.act_fwd b hb hc0
    set P_act := bp.actBlk b
    obtain ⟨htb_lt, htb_P⟩ := hv.tb_fwd P_act hP_lt.le (Or.inr hP_tag)
    by_cases hcK : bp.actCode b ≤ bp.K
    · rw [ite_eq_left hcK]
      set cur := bp.actCode b - 1
      have hcur_eq : bp.actCur b = cur := by
        unfold actCur; rw [ite_eq_right hc0, ite_eq_left hcK]
      have hcur_lt_K : cur < bp.K := by dsimp only [cur]; omega
      by_cases hr_le : bp.r b ≤ cur
      · rw [ite_eq_left hr_le]
        exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
      · rw [ite_eq_right hr_le]
        have hcur_lt_r : cur < bp.r b := Nat.lt_of_not_le hr_le
        set rk_cur := (bp.head b + cur) % (6 * bp.K)
        set t_cur := bp.tailRing b rk_cur
        set t_act := bp.blkMeta2 P_act * bp.K + cur
        have hlive_cur : bp.LiveTail t_cur := ⟨b, hb, cur, hcur_eq.le, hcur_lt_r, rfl⟩
        have hlive_act : bp.LiveTail t_act := by
          have htbw := hv.tail_bwd P_act hP_lt.le cur hcur_lt_K (Or.inl hP_lt)
            (Or.inr ⟨hP_tag, by rw [hP_m1, hcur_eq]⟩)
          obtain ⟨bo, hrko, hk_ge, hk_lt, htr⟩ := htbw
          obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ bo
          refine ⟨bp.tailOwnerBkt t_act, bo,
            (bp.tailOwnerRing t_act + 6 * bp.K - bp.head (bp.tailOwnerBkt t_act)) % (6 * bp.K),
            hk_ge, hk_lt, ?_⟩
          rwa [head_add_sub_mod hhdo hrko]
        have hsw_spec := hv.swapTailCoords_spec hlive_cur hlive_act
        rcases hsw_eq : bp.swapTailCoords t_cur t_act with ⟨bp₁, osw⟩
        rw [hsw_eq] at hsw_spec
        obtain ⟨hv₁, hsw_lt, harr₁⟩ := hsw_spec
        -- Extract that in `bp₁`, `tailRing b rk_cur = t_act` and `tailOwner t_act = (b, rk_cur)`
        have hbp₁_fields :
            bp₁.M = bp.M ∧ bp₁.K = bp.K ∧ bp₁.maxSlabs = bp.maxSlabs ∧ bp₁.nSide = bp.nSide ∧
            bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.head = bp.head ∧ bp₁.actCode = bp.actCode ∧
            bp₁.actBlk = bp.actBlk ∧ bp₁.slabOf = bp.slabOf ∧ bp₁.blkTag = bp.blkTag ∧
            bp₁.blkMeta1 = bp.blkMeta1 ∧ bp₁.blkMeta2 = bp.blkMeta2 ∧
            bp₁.unresLen = bp.unresLen ∧ bp₁.unresStack = bp.unresStack ∧
            bp₁.tbHighWater = bp.tbHighWater ∧ bp₁.freeTbTop = bp.freeTbTop ∧
            bp₁.freeTbStack = bp.freeTbStack ∧ bp₁.tbPhysBlk = bp.tbPhysBlk ∧
            bp₁.topSwapAct = bp.topSwapAct ∧ bp₁.topSwapSrc = bp.topSwapSrc ∧
            bp₁.topSwapDst = bp.topSwapDst ∧ bp₁.topSwapCur = bp.topSwapCur := by
          unfold swapTailCoords at hsw_eq
          by_cases he : t_cur = t_act
          · rw [ite_eq_left he] at hsw_eq; injection hsw_eq with h1 _; subst h1
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [ite_eq_right he] at hsw_eq; injection hsw_eq with h1 _; rw [← h1]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨hM₁, hK₁, hms₁, hn₁, hq₁, hr₁, hhd₁, hac₁, hab₁, hsl₁, hbt₁, hbm1₁, hbm2₁,
          hul₁, hus₁, hthw₁, hftt₁, hfts₁, htpb₁, htsa₁, htss₁, htsd₁, htsc₁⟩ := hbp₁_fields
        have htr₁_cur : bp₁.tailRing b rk_cur = t_act := by
          unfold swapTailCoords at hsw_eq
          by_cases he : t_cur = t_act
          · rw [ite_eq_left he] at hsw_eq; injection hsw_eq with h1 _; rw [← h1]; exact he
          · rw [ite_eq_right he] at hsw_eq; injection hsw_eq with h1 _
            have htfc := hv.tail_fwd b hb cur hcur_eq.le hcur_lt_r
            dsimp only at htfc
            obtain ⟨_, _, _, _, hob_c, hor_c⟩ := htfc
            have hbrk_ne : ¬(b = bp.tailOwnerBkt t_act ∧ rk_cur = bp.tailOwnerRing t_act) := by
              rintro ⟨he1, he2⟩
              have htbw := hv.tail_bwd P_act hP_lt.le cur hcur_lt_K (Or.inl hP_lt)
                (Or.inr ⟨hP_tag, by rw [hP_m1, hcur_eq]⟩)
              dsimp only at htbw
              rw [← he1, ← he2] at htbw
              exact he htbw.2.2.2.2
            rw [← h1]; dsimp only
            rw [hob_c, hor_c, set2_of_ne _ _ _ _ _ _ hbrk_ne, set2_self]
        have hob₁_act : bp₁.tailOwnerBkt t_act = b ∧ bp₁.tailOwnerRing t_act = rk_cur := by
          have htf₁ := hv₁.tail_fwd b (by rw [hM₁]; exact hb) cur
            (by unfold actCur; rw [hac₁, hK₁]; exact hcur_eq.le) (by rw [hr₁]; exact hcur_lt_r)
          dsimp only at htf₁
          rw [hhd₁, hK₁] at htf₁
          rw [htr₁_cur] at htf₁
          exact ⟨htf₁.2.2.2.2.1, htf₁.2.2.2.2.2⟩
        have hphys_act : bp₁.physOfTail t_act = bp.effBlk P_act cur * bp.K + cur := by
          unfold physOfTail
          rw [hK₁, htpb₁]
          have hd_eq : t_act / bp.K = bp.blkMeta2 P_act := by
            dsimp only [t_act]
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hcur_lt_K, zero_add]
          have hm_eq : t_act % bp.K = cur := by
            dsimp only [t_act]
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcur_lt_K]
          have heff₁ : bp₁.effBlk P_act cur = bp.effBlk P_act cur := by
            unfold effBlk; rw [htsa₁, htsc₁, htss₁, htsd₁]
          rw [hd_eq, hm_eq, htb_P, heff₁]
        dsimp only; rw [hsw_eq]; dsimp only
        by_cases hmid : cur + 1 < bp.K
        · rw [ite_eq_left hmid]; dsimp only
          set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b + 1) }
          have hac'_b : bp'.actCur b = cur + 1 := by
            unfold actCur
            have hc' : bp'.actCode b = bp.actCode b + 1 := set1_self _ _ _
            have hk' : bp'.K = bp.K := hK₁
            rw [hc', hk', ite_eq_right (by omega), ite_eq_left (by omega)]
            dsimp only [cur]; omega
          have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
            unfold actCur
            have hc' : bp'.actCode b' = bp.actCode b' :=
              (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b')
            have hk' : bp'.K = bp.K := hK₁
            rw [hc', hk']
          have htp_eq : ∀ b' loc', bp'.toPhys b' loc' = bp₁.toPhys b' loc' := fun b' loc' => by
            have heff_eq : ∀ E o, bp'.effBlk E o = bp₁.effBlk E o := fun _ _ => rfl
            have hpt_eq : ∀ t, bp'.physOfTail t = bp₁.physOfTail t := fun _ => rfl
            by_cases hb' : b' = b
            · subst b'
              unfold toPhys
              have hac₁_b : bp₁.actCur b = cur := by
                unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
              simp only [show bp'.K = bp.K from hK₁, show bp₁.K = bp.K from hK₁,
                show bp'.q = bp.q from hq₁, show bp₁.q = bp.q from hq₁,
                show bp'.slabOf = bp.slabOf from hsl₁, show bp₁.slabOf = bp.slabOf from hsl₁,
                show bp'.actBlk = bp.actBlk from hab₁, show bp₁.actBlk = bp.actBlk from hab₁,
                show bp'.head = bp.head from hhd₁, show bp₁.head = bp.head from hhd₁,
                show bp'.tailRing = bp₁.tailRing from rfl,
                hac'_b, hac₁_b, heff_eq, hpt_eq]
              by_cases hslab : loc' < bp.q b * bp.K
              · rw [ite_eq_left hslab, ite_eq_left hslab]
              · rw [ite_eq_right hslab, ite_eq_right hslab]
                set k := loc' - bp.q b * bp.K
                by_cases hk_lt : k < cur
                · rw [ite_eq_left (by omega), ite_eq_left hk_lt]
                · by_cases hk_eq : k = cur
                  · rw [hk_eq, ite_eq_left (by omega), ite_eq_right (by omega), htr₁_cur, hphys_act]
                    unfold effBlk; rw [htsa₁, htsc₁, htss₁, htsd₁]
                  · rw [ite_eq_right (by omega), ite_eq_right hk_lt]
            · unfold toPhys
              have hac_eq : bp'.actCur b' = bp₁.actCur b' := by
                unfold actCur
                rw [show bp'.actCode b' = bp₁.actCode b' from set1_of_ne _ _ _ _ hb',
                  show bp'.K = bp₁.K from rfl]
              simp only [show bp'.K = bp₁.K from rfl, show bp'.q = bp₁.q from rfl,
                show bp'.slabOf = bp₁.slabOf from rfl, show bp'.actBlk = bp₁.actBlk from rfl,
                show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl,
                hac_eq, heff_eq, hpt_eq]
          have hcv' : bp'.CoreValid :=
            { M_pos := by dsimp only [bp']; rw [hM₁]; exact hv.M_pos
              K_ge := by dsimp only [bp']; rw [hK₁]; exact hv.K_ge
              bkt_bounds := fun b' hb' => by
                rw [show bp'.M = bp.M from hM₁] at hb'
                by_cases hbe : b' = b
                · subst b'
                  rw [hac'_b]
                  dsimp only [bp']
                  rw [hq₁, hms₁, hr₁, hK₁, hhd₁, set1_self]
                  exact ⟨hq_le, hr_lt, hhd_lt, by omega, by omega⟩
                · rw [hac'_ne b' hbe]
                  dsimp only [bp']
                  rw [hq₁, hms₁, hr₁, hK₁, hhd₁, set1_of_ne _ _ _ _ hbe, hac₁]
                  exact hv.bkt_bounds b' hb'
              blkTag_lt := hv₁.blkTag_lt
              blkTag_top := hv₁.blkTag_top
              unres_fwd := hv₁.unres_fwd
              unres_bwd := hv₁.unres_bwd
              slab_fwd := hv₁.slab_fwd
              slab_bwd := hv₁.slab_bwd
              act_fwd := fun b' hb' hne => by
                dsimp only [bp'] at hb' hne ⊢
                by_cases hbe : b' = b
                · subst b'
                  exact hv₁.act_fwd b hb' (by rw [hac₁]; exact hc0)
                · rw [set1_of_ne _ _ _ _ hbe] at hne
                  exact hv₁.act_fwd b' hb' hne
              act_bwd := fun P hP htag => by
                obtain ⟨hb_m, hne_m, hab_m⟩ := hv₁.act_bwd P hP htag
                dsimp only [bp']
                refine ⟨hb_m, ?_, hab_m⟩
                by_cases hbe : bp₁.blkMeta1 P = b
                · rw [hbe, set1_self]; omega
                · rw [set1_of_ne _ _ _ _ hbe]; exact hne_m
              tb_fwd := hv₁.tb_fwd
              freeTb_valid := hv₁.freeTb_valid
              freeTb_inj := hv₁.freeTb_inj
              tbHighWater_supply := hv₁.tbHighWater_supply
              tbHighWater_le_max := hv₁.tbHighWater_le_max
              topSwap_act_le := hv₁.topSwap_act_le
              topSwap_valid := hv₁.topSwap_valid
              tail_fwd := fun b' hb' k hk_ge hk_lt => by
                dsimp only
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                have hrem_eq : bp'.rem = bp₁.rem := rfl
                have hac₁_eq : ∀ x, bp₁.actCur x = bp.actCur x := fun x => by
                  unfold actCur; rw [hac₁, hK₁]
                have hk_ge₁ : bp₁.actCur b' ≤ k := by
                  rw [hac₁_eq]
                  by_cases hbe : b' = b
                  · subst b'; rw [hac'_b] at hk_ge; rw [hcur_eq]; omega
                  · rwa [hac'_ne b' hbe] at hk_ge
                have htf := hv₁.tail_fwd b' hb' k hk_ge₁ hk_lt
                dsimp only at htf
                rw [hBf_eq, hrem_eq, show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
                  show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl,
                  show bp'.tbPhysBlk = bp₁.tbPhysBlk from rfl,
                  show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
                  show bp'.blkTag = bp₁.blkTag from rfl,
                  show bp'.blkMeta1 = bp₁.blkMeta1 from rfl,
                  show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
                  show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl]
                obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                · exact Or.inl h0
                · refine Or.inr ⟨hPlt, ht2, ?_⟩
                  by_cases hbe_P : bp₁.blkMeta1 (bp₁.tbPhysBlk
                      (bp₁.tailRing b' ((bp₁.head b' + k) % (6 * bp₁.K)) / bp₁.K)) = b
                  · rw [hbe_P, hac'_b]
                    set rk' := (bp₁.head b' + k) % (6 * bp₁.K)
                    set t' := bp₁.tailRing b' rk'
                    have hP_eq_act : bp₁.tbPhysBlk (t' / bp₁.K) = P_act := by
                      have hab_m := (hv₁.act_bwd _ hPlt ht2).2.2
                      rw [hbe_P, hab₁] at hab_m; exact hab_m.symm
                    have ht'_ne : t' ≠ t_act := fun hte => by
                      rw [hte] at hob hor
                      have hb_eq : b' = b := hob.symm.trans hob₁_act.1
                      rw [hb_eq, hac'_b] at hk_ge
                      dsimp only [rk'] at hor
                      rw [hb_eq] at hk_lt hor
                      rw [hhd₁, hK₁] at hor
                      have hrk_eq : (bp.head b + k) % (6 * bp.K) = rk_cur :=
                        hor.symm.trans hob₁_act.2
                      have hk_eq_cur : k = cur := by
                        have hk_lt_6K : k < 6 * bp.K := by
                          rw [show bp'.r = bp.r from hr₁] at hk_lt; exact hk_lt.trans hr_lt
                        have h1 := add_sub_head_mod hK hhd_lt hk_lt_6K
                        have h2 := add_sub_head_mod hK hhd_lt (hcur_lt_r.trans hr_lt)
                        rw [hrk_eq] at h1; exact h1.symm.trans h2
                      omega
                    have hdiv_t' : t' / bp.K = bp.blkMeta2 P_act := by
                      rw [← hK₁, ← hc_m2, hP_eq_act, hbm2₁]
                    have hne_mod : t' % bp.K ≠ cur := fun hme => by
                      have hr1 := Nat.div_add_mod t' bp.K
                      rw [hdiv_t', hme, Nat.mul_comm] at hr1
                      exact ht'_ne hr1.symm
                    rw [hac₁_eq, hbe_P, hcur_eq] at hge_m
                    rw [hK₁] at hge_m ⊢
                    omega
                  · rw [hac'_ne _ hbe_P, ← hac₁_eq]; exact hge_m
              tail_bwd := fun P hP_le off hoff hlt hor => by
                dsimp only
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                have hrem_eq : bp'.rem = bp₁.rem := rfl
                have hac₁_eq : ∀ x, bp₁.actCur x = bp.actCur x := fun x => by
                  unfold actCur; rw [hac₁, hK₁]
                have hor₁ : bp₁.blkTag P = 0 ∨
                    (bp₁.blkTag P = 2 ∧ bp₁.actCur (bp₁.blkMeta1 P) ≤ off) := by
                  rcases hor with h0 | ⟨h2, hge⟩
                  · exact Or.inl h0
                  · refine Or.inr ⟨h2, ?_⟩
                    rw [hac₁_eq]
                    change bp₁.blkTag P = 2 at h2
                    rw [show bp'.blkMeta1 P = bp₁.blkMeta1 P from rfl] at hge
                    by_cases hbe : bp₁.blkMeta1 P = b
                    · rw [hbe, hac'_b] at hge; rw [hbe, hcur_eq]; omega
                    · rwa [hac'_ne _ hbe] at hge
                obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv₁.tail_bwd P hP_le off hoff hlt hor₁
                rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
                  show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
                  show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
                  show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl,
                  show bp'.head = bp₁.head from rfl, show bp'.r = bp₁.r from rfl,
                  show bp'.tailRing = bp₁.tailRing from rfl]
                refine ⟨hbo, hrko, ?_, hk_lt, htr⟩
                set t := bp₁.blkMeta2 P * bp₁.K + off
                by_cases hbe : bp₁.tailOwnerBkt t = b
                · rw [hbe, hac'_b]
                  rw [hbe, hac₁_eq, hcur_eq] at hk_ge
                  have hk_ne_cur : (bp₁.tailOwnerRing t + 6 * bp₁.K - bp₁.head b) %
                      (6 * bp₁.K) ≠ cur := fun hke => by
                    obtain ⟨_, _, hhdo₁, _, _⟩ := hv₁.bkt_bounds b (by rw [hM₁]; exact hb)
                    have hrk_eq : bp₁.tailOwnerRing t = rk_cur := by
                      rw [← head_add_sub_mod hhdo₁ hrko, hke, hhd₁, hK₁]
                    rw [hbe, hrk_eq, htr₁_cur] at htr
                    have hP_eq : P = P_act := by
                      have htb₁ := (hv₁.tb_fwd P hP_le (hor₁.imp id And.left)).2
                      have hdiv_t : t / bp₁.K = bp₁.blkMeta2 P := by
                        dsimp only [t]
                        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by rw [hK₁]; exact hK),
                          Nat.div_eq_of_lt hoff, zero_add]
                      have hdiv_act : t_act / bp.K = bp.blkMeta2 P_act := by
                        dsimp only [t_act]
                        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK,
                          Nat.div_eq_of_lt hcur_lt_K, zero_add]
                      rw [htr] at hdiv_act
                      rw [hK₁] at hdiv_t
                      have hm2_eq : bp₁.blkMeta2 P = bp.blkMeta2 P_act :=
                        hdiv_t.symm.trans hdiv_act
                      rw [← htb₁, hm2_eq, htpb₁, htb_P]
                    have hoff_eq : off = cur := by
                      have hm1 : t % bp.K = off := by
                        dsimp only [t]; rw [hK₁, Nat.add_comm, Nat.add_mul_mod_self_right,
                          Nat.mod_eq_of_lt (by rw [← hK₁]; exact hoff)]
                      have hm2 : t_act % bp.K = cur := by
                        dsimp only [t_act]; rw [Nat.add_comm, Nat.add_mul_mod_self_right,
                          Nat.mod_eq_of_lt hcur_lt_K]
                      rw [htr] at hm2; exact hm1.symm.trans hm2
                    rcases hor with h0 | ⟨_, hge⟩
                    · change bp₁.blkTag P = 0 at h0; rw [hP_eq, hbt₁, hP_tag] at h0
                      exact absurd h0 (by decide)
                    · rw [show bp'.blkMeta1 P = bp₁.blkMeta1 P from rfl,
                        hP_eq, hbm1₁, hP_m1, hac'_b, hoff_eq] at hge
                      omega
                  omega
                · rw [hac'_ne _ hbe, ← hac₁_eq]; exact hk_ge }
          have hbc_mid : ∀ b', bp'.bktCount b' = bp.bktCount b' := fun b' => by
            unfold bktCount; dsimp only [bp']; rw [hq₁, hK₁, hr₁]
          refine ⟨hcv', hn₁, hbc_mid, hsw_lt, fun arr b' loc' hb' hloc' => ?_⟩
          rw [htp_eq]
          exact harr₁ arr b' loc' hb' hloc'
        · -- Promote finish: `cur + 1 = bp.K`
          rw [ite_eq_right hmid]; dsimp only
          have hcur_top : cur + 1 = bp.K := by omega
          have hac_eq_K : bp.actCode b = bp.K := by dsimp only [cur] at hcur_top; omega
          have hq_lt_ms : bp.q b < bp.maxSlabs := hprom_q hac_eq_K
          have hK_le_r : bp.K ≤ bp.r b := by omega
          set vp := bp₁.q b
          set tb_old := bp₁.blkMeta2 P_act
          set bp₂ := bp₁.freeTb tb_old
          set bp' : BlockPoolState :=
            { bp₂ with
              q := set1 bp₂.q b (vp + 1)
              r := set1 bp₂.r b (bp₂.r b - bp.K)
              head := set1 bp₂.head b ((bp₂.head b + bp.K) % (6 * bp.K))
              actCode := set1 bp₂.actCode b 0
              slabOf := set2 bp₂.slabOf b vp P_act
              blkTag := set1 bp₂.blkTag P_act 1
              blkMeta2 := set1 bp₂.blkMeta2 P_act vp }
          have hbc_eq : ∀ b', bp'.bktCount b' = bp.bktCount b' := fun b' => by
            unfold bktCount; dsimp only [bp', bp₂, freeTb, vp]
            rw [hK₁, hq₁, hr₁]
            by_cases hbe : b' = b
            · subst hbe; rw [set1_self, set1_self, Nat.add_one_mul]; omega
            · rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe]
          have hac'_b : bp'.actCur b = 0 := by
            unfold actCur
            rw [show bp'.actCode b = 0 from set1_self _ _ _, ite_eq_left rfl]
          have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp₁.actCur b' := fun b' hne => by
            unfold actCur
            rw [show bp'.actCode b' = bp₁.actCode b' from set1_of_ne _ _ _ _ hne,
              show bp'.K = bp₁.K from rfl]
          have htp_eq : ∀ b' loc', loc' < bp.bktCount b' →
              bp'.toPhys b' loc' = bp₁.toPhys b' loc' := fun b' loc' hloc' => by
            have heff_eq : ∀ E o, bp'.effBlk E o = bp₁.effBlk E o := fun _ _ => rfl
            have hpt_eq : ∀ t, bp'.physOfTail t = bp₁.physOfTail t := fun _ => rfl
            by_cases hbe : b' = b
            · subst b'
              unfold toPhys
              simp only [hac'_b, heff_eq, hpt_eq]
              dsimp only [bp', bp₂, freeTb, vp]
              simp only [set1_self, hK₁, hq₁, hab₁, hhd₁]
              have hac₁_b : bp₁.actCur b = cur := by
                unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
              rw [hac₁_b]
              by_cases hslab : loc' < bp.q b * bp.K
              · have hslab' : loc' < (bp.q b + 1) * bp.K := by
                  rw [Nat.add_one_mul]; omega
                rw [ite_eq_left hslab', ite_eq_left hslab]
                have hvp_lt : loc' / bp.K < bp.q b := (Nat.div_lt_iff_lt_mul hK).mpr hslab
                rw [set2_of_ne _ _ _ _ _ _ (fun h => ne_of_lt hvp_lt h.2)]
              · rw [ite_eq_right hslab]
                by_cases hslab' : loc' < (bp.q b + 1) * bp.K
                · rw [ite_eq_left hslab']
                  have hdiv_vp : loc' / bp.K = bp.q b := by
                    apply le_antisymm
                    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hK).mpr hslab')
                    · exact (Nat.le_div_iff_mul_le hK).mpr (Nat.le_of_not_lt hslab)
                  have hsub_eq : loc' - bp.q b * bp.K = loc' % bp.K := by
                    have h := Nat.div_add_mod loc' bp.K
                    rw [hdiv_vp, Nat.mul_comm] at h; omega
                  rw [hdiv_vp, set2_self, hsub_eq]
                  have hmod_lt : loc' % bp.K < bp.K := Nat.mod_lt loc' hK
                  by_cases hlt_cur : loc' % bp.K < cur
                  · rw [ite_eq_left hlt_cur]
                  · have heq_cur : loc' % bp.K = cur := by omega
                    rw [heq_cur, ite_eq_right (not_lt.mpr le_rfl), htr₁_cur, hphys_act]
                    unfold effBlk; rw [htsa₁, htsc₁, htss₁, htsd₁]
                · rw [ite_eq_right hslab']
                  have hnot0 : ¬(loc' - (bp.q b + 1) * bp.K < 0) := Nat.not_lt_zero _
                  have hge_K : bp.K ≤ loc' - bp.q b * bp.K := by
                    rw [Nat.add_one_mul] at hslab'; omega
                  have hnot_cur : ¬(loc' - bp.q b * bp.K < cur) := by omega
                  rw [ite_eq_right hnot0, ite_eq_right hnot_cur]
                  have hshift : ((bp.head b + bp.K) % (6 * bp.K) +
                      (loc' - (bp.q b + 1) * bp.K)) % (6 * bp.K) =
                      (bp.head b + (loc' - bp.q b * bp.K)) % (6 * bp.K) := by
                    rw [head_shift_add_mod hK]
                    congr 2; rw [Nat.add_one_mul]; omega
                  rw [hshift]
            · unfold toPhys
              simp only [hac'_ne b' hbe, heff_eq, hpt_eq]
              dsimp only [bp', bp₂, freeTb]
              have hne2 : ∀ v, ¬(b' = b ∧ v = vp) := fun _ h => hbe h.1
              simp only [set1_of_ne _ _ _ _ hbe, set2_of_ne _ _ _ _ _ _ (hne2 _)]
          have hP_ne_B : P_act ≠ bp₁.B_full :=
            ne_of_lt (by dsimp only [B_full]; rw [hn₁, hK₁]; exact hP_lt)
          have hcv' : bp'.CoreValid :=
            { M_pos := by dsimp only [bp', bp₂, freeTb]; rw [hM₁]; exact hv.M_pos
              K_ge := by dsimp only [bp', bp₂, freeTb]; rw [hK₁]; exact hv.K_ge
              bkt_bounds := fun b' hb' => by
                rw [show bp'.M = bp.M from hM₁] at hb'
                by_cases hbe : b' = b
                · subst b'
                  rw [hac'_b]
                  dsimp only [bp', bp₂, freeTb, vp]
                  rw [hms₁, hK₁, hq₁, hr₁, hhd₁, set1_self, set1_self, set1_self, set1_self]
                  exact ⟨hq_lt_ms, by omega, Nat.mod_lt _ (by omega), Nat.zero_le _, Nat.zero_le _⟩
                · rw [hac'_ne b' hbe]
                  have hac₁_eq : bp₁.actCur b' = bp.actCur b' := by unfold actCur; rw [hac₁, hK₁]
                  rw [hac₁_eq]
                  dsimp only [bp', bp₂, freeTb]
                  rw [hms₁, hK₁, hq₁, hr₁, hhd₁, set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe,
                    set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe, hac₁]
                  exact hv.bkt_bounds b' hb'
              blkTag_lt := fun P hP => by
                dsimp only [bp', bp₂, freeTb]
                by_cases hp : P = P_act
                · subst hp; rw [set1_self]; decide
                · rw [set1_of_ne _ _ _ _ hp]; exact hv₁.blkTag_lt P hP
              blkTag_top := by
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                rw [hBf_eq]; dsimp only [bp', bp₂, freeTb]
                rw [set1_of_ne _ _ _ _ hP_ne_B.symm]; exact hv₁.blkTag_top
              unres_fwd := fun i hi => by
                obtain ⟨h1, h2, h3⟩ := hv₁.unres_fwd i hi
                have hne : bp₁.unresStack i ≠ P_act := fun he => by
                  rw [he, hbt₁, hP_tag] at h2; exact absurd h2 (by decide)
                dsimp only [bp', bp₂, freeTb]
                rw [set1_of_ne _ _ _ _ hne]
                exact ⟨h1, h2, h3⟩
              unres_bwd := fun P hP htag0 => by
                dsimp only [bp', bp₂, freeTb] at hP htag0 ⊢
                have hne : P ≠ P_act := fun he => by
                  rw [he, set1_self] at htag0; exact absurd htag0 (by decide)
                rw [set1_of_ne _ _ _ _ hne] at htag0
                exact hv₁.unres_bwd P hP htag0
              slab_fwd := fun b' hb' v hv_lt => by
                dsimp only [bp', bp₂, freeTb] at hb' hv_lt ⊢
                by_cases hbe : b' = b
                · subst b'; rw [set1_self] at hv_lt
                  by_cases hve : v = vp
                  · subst hve; rw [set2_self, set1_self, set1_self]
                    exact ⟨by dsimp only [B_full]; rw [hn₁, hK₁]; exact hP_lt,
                      rfl, by rw [hbm1₁, hP_m1], rfl⟩
                  · have hv_lt' : v < bp₁.q b := by dsimp only [vp] at hve hv_lt; omega
                    rw [set2_of_ne _ _ _ _ _ _ (fun h => hve h.2)]
                    obtain ⟨h1, h2, h3, h4⟩ := hv₁.slab_fwd b hb' v hv_lt'
                    have hne : bp₁.slabOf b v ≠ P_act := fun he => by
                      rw [he, hbt₁, hP_tag] at h2; exact absurd h2 (by decide)
                    rw [set1_of_ne _ _ _ _ hne, set1_of_ne _ _ _ _ hne]
                    exact ⟨h1, h2, h3, h4⟩
                · rw [set1_of_ne _ _ _ _ hbe] at hv_lt
                  rw [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
                  obtain ⟨h1, h2, h3, h4⟩ := hv₁.slab_fwd b' hb' v hv_lt
                  have hne : bp₁.slabOf b' v ≠ P_act := fun he => by
                    rw [he, hbt₁, hP_tag] at h2; exact absurd h2 (by decide)
                  rw [set1_of_ne _ _ _ _ hne, set1_of_ne _ _ _ _ hne]
                  exact ⟨h1, h2, h3, h4⟩
              slab_bwd := fun P hP htag1 => by
                dsimp only [bp', bp₂, freeTb] at hP htag1 ⊢
                by_cases hp : P = P_act
                · subst hp; rw [set1_self]
                  rw [hbm1₁, hP_m1, set1_self, set2_self, hM₁]
                  exact ⟨hb, Nat.lt_succ_self vp, rfl⟩
                · rw [set1_of_ne _ _ _ _ hp] at htag1
                  obtain ⟨h1, h2, h3⟩ := hv₁.slab_bwd P hP htag1
                  rw [set1_of_ne _ _ _ _ hp]
                  by_cases hbe : bp₁.blkMeta1 P = b
                  · rw [hbe, set1_self]
                    rw [hbe] at h1 h2 h3
                    have hve : bp₁.blkMeta2 P ≠ vp := ne_of_lt h2
                    rw [set2_of_ne _ _ _ _ _ _ (fun h => hve h.2)]
                    exact ⟨h1, Nat.lt_succ_of_lt h2, h3⟩
                  · rw [set1_of_ne _ _ _ _ hbe, set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
                    exact ⟨h1, h2, h3⟩
              act_fwd := fun b' hb' hne => by
                dsimp only [bp', bp₂, freeTb] at hb' hne ⊢
                have hbe : b' ≠ b := fun he => by subst he; rw [set1_self] at hne; exact hne rfl
                rw [set1_of_ne _ _ _ _ hbe] at hne
                obtain ⟨h1, h2, h3⟩ := hv₁.act_fwd b' hb' hne
                have hp : bp₁.actBlk b' ≠ P_act := fun he => by
                  rw [he, hbm1₁, hP_m1] at h3; exact hbe h3.symm
                rw [set1_of_ne _ _ _ _ hp]
                exact ⟨h1, h2, h3⟩
              act_bwd := fun P hP htag2 => by
                dsimp only [bp', bp₂, freeTb] at hP htag2 ⊢
                have hp : P ≠ P_act := fun he => by
                  rw [he, set1_self] at htag2; exact absurd htag2 (by decide)
                rw [set1_of_ne _ _ _ _ hp] at htag2
                obtain ⟨h1, h2, h3⟩ := hv₁.act_bwd P hP htag2
                have hbe : bp₁.blkMeta1 P ≠ b := fun he => by
                  rw [he, hab₁] at h3; exact hp h3.symm
                rw [set1_of_ne _ _ _ _ hbe]
                exact ⟨h1, h2, h3⟩
              tb_fwd := fun P hP hor => by
                dsimp only [bp', bp₂, freeTb] at hP hor ⊢
                have hp : P ≠ P_act := fun he => by
                  rw [he, set1_self] at hor; rcases hor with h | h <;> exact absurd h (by decide)
                rw [set1_of_ne _ _ _ _ hp] at hor
                rw [set1_of_ne _ _ _ _ hp]
                exact hv₁.tb_fwd P hP hor
              freeTb_valid := fun i hi => by
                dsimp only [bp', bp₂, freeTb] at hi ⊢
                by_cases htop : i = bp₁.freeTbTop
                · subst htop; rw [set1_self]
                  dsimp only [tb_old]; rw [hbm2₁, hthw₁]
                  refine ⟨htb_lt, fun P hP hor hme => ?_⟩
                  have hp : P ≠ P_act := fun he => by
                    rw [he, set1_self] at hor; rcases hor with h | h <;> exact absurd h (by decide)
                  rw [set1_of_ne _ _ _ _ hp] at hor hme
                  have htb_P' := (hv₁.tb_fwd P hP hor).2
                  rw [hbm2₁, hme, htpb₁, htb_P] at htb_P'
                  exact hp htb_P'.symm
                · have hi' : i < bp₁.freeTbTop := by omega
                  rw [set1_of_ne _ _ _ _ htop]
                  obtain ⟨h1, h2⟩ := hv₁.freeTb_valid i hi'
                  refine ⟨h1, fun P hP hor => ?_⟩
                  have hp : P ≠ P_act := fun he => by
                    rw [he, set1_self] at hor; rcases hor with h | h <;> exact absurd h (by decide)
                  rw [set1_of_ne _ _ _ _ hp] at hor ⊢
                  exact h2 P hP hor
              freeTb_inj := fun i hi j hj heq => by
                dsimp only [bp', bp₂, freeTb] at hi hj heq ⊢
                have hnot_in : ∀ idx < bp₁.freeTbTop, bp₁.freeTbStack idx ≠ tb_old :=
                  fun idx hidx =>
                  ((hv₁.freeTb_valid idx hidx).2 P_act
                    (by dsimp only [B_full]; rw [hn₁, hK₁]; exact hP_lt.le)
                    (Or.inr (by rw [hbt₁]; exact hP_tag))).symm
                by_cases hi_t : i = bp₁.freeTbTop
                · by_cases hj_t : j = bp₁.freeTbTop
                  · exact hi_t.trans hj_t.symm
                  · rw [hi_t, set1_self, set1_of_ne _ _ _ _ hj_t] at heq
                    exact absurd heq.symm (hnot_in j (by omega))
                · by_cases hj_t : j = bp₁.freeTbTop
                  · rw [hj_t, set1_of_ne _ _ _ _ hi_t, set1_self] at heq
                    exact absurd heq (hnot_in i (by omega))
                  · rw [set1_of_ne _ _ _ _ hi_t, set1_of_ne _ _ _ _ hj_t] at heq
                    exact hv₁.freeTb_inj i (by omega) j (by omega) heq
              tbHighWater_supply := by
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                rw [hBf_eq]
                dsimp only [bp', bp₂, freeTb]
                have hcard := filter_tail_card_erase (N := bp₁.B_full + 1) (P₀ := P_act)
                  (t₁ := bp₁.blkTag) (t₂ := set1 bp₁.blkTag P_act 1)
                  (by dsimp only [B_full] at hP_lt ⊢; rw [hn₁, hK₁]; omega)
                  (Or.inr (by rw [hbt₁]; exact hP_tag))
                  (by rw [set1_self]; decide)
                  (fun P _ hp => by rw [set1_of_ne _ _ _ _ hp])
                have hsup := hv₁.tbHighWater_supply
                change bp₁.tbHighWater ≤ (bp₁.freeTbTop + 1) +
                  ((Finset.range (bp₁.B_full + 1)).filter
                    (fun P => set1 bp₁.blkTag P_act 1 P = 0 ∨
                      set1 bp₁.blkTag P_act 1 P = 2)).card
                omega
              tbHighWater_le_max := hv₁.tbHighWater_le_max
              topSwap_act_le := hv₁.topSwap_act_le
              topSwap_valid := fun ha => by
                obtain ⟨h1, h2, h3, h4, h5⟩ := hv₁.topSwap_valid ha
                dsimp only [bp', bp₂, freeTb]
                have hne_d : bp₁.topSwapDst ≠ P_act := fun he => by
                  rw [he, hbt₁, hP_tag] at h4; exact absurd h4 (by decide)
                rw [set1_of_ne _ _ _ _ hne_d]
                exact ⟨h1, h2, h3, h4, h5⟩
              tail_fwd := fun b' hb' k hk_ge hk_lt => by
                dsimp only
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                have hrem_eq : bp'.rem = bp₁.rem := rfl
                rw [show bp'.M = bp₁.M from rfl] at hb'
                rw [show bp'.r = set1 bp₁.r b (bp₁.r b - bp.K) from rfl] at hk_lt
                rw [hBf_eq, hrem_eq, show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
                  show bp'.head = set1 bp₁.head b ((bp₁.head b + bp.K) % (6 * bp.K)) from rfl,
                  show bp'.tailRing = bp₁.tailRing from rfl,
                  show bp'.tbPhysBlk = bp₁.tbPhysBlk from rfl,
                  show bp'.blkMeta2 = set1 bp₁.blkMeta2 P_act vp from rfl,
                  show bp'.blkTag = set1 bp₁.blkTag P_act 1 from rfl,
                  show bp'.blkMeta1 = bp₁.blkMeta1 from rfl,
                  show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
                  show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl]
                by_cases hbe : b' = b
                · subst b'
                  rw [set1_self] at hk_lt
                  rw [set1_self]
                  have hk_old_lt : bp₁.K + k < bp₁.r b := by
                    rw [hr₁] at hk_lt; rw [hK₁, hr₁]; omega
                  have hk_old_ge : bp₁.actCur b ≤ bp₁.K + k := by
                    have hac₁_b : bp₁.actCur b = cur := by
                      unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
                    rw [hac₁_b, hK₁]; omega
                  have htf := hv₁.tail_fwd b hb' (bp₁.K + k) hk_old_ge hk_old_lt
                  dsimp only at htf
                  have hrk_eq : ((bp₁.head b + bp.K) % (6 * bp.K) + k) % (6 * bp₁.K) =
                      (bp₁.head b + (bp₁.K + k)) % (6 * bp₁.K) := by
                    rw [← hK₁]; exact head_shift_add_mod (by rw [hK₁]; exact hK)
                  rw [hrk_eq]
                  obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                  set rk' := (bp₁.head b + (bp₁.K + k)) % (6 * bp₁.K)
                  set t' := bp₁.tailRing b rk'
                  have hP_ne_act : bp₁.tbPhysBlk (t' / bp₁.K) ≠ P_act := fun he => by
                    have hdiv_eq : t' / bp₁.K = bp₁.blkMeta2 P_act := by
                      rw [← hc_m2, he]
                    have hoff_lt : t' % bp₁.K < bp₁.K := Nat.mod_lt _ (by rw [hK₁]; exact hK)
                    rcases hkind with ⟨ht0, _⟩ | ⟨_, _, hge_m⟩
                    · rw [he, hbt₁, hP_tag] at ht0; exact absurd ht0 (by decide)
                    · rw [he, hbm1₁, hP_m1] at hge_m
                      have hac₁_b : bp₁.actCur b = cur := by
                        unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
                      rw [hac₁_b] at hge_m
                      have hoff_eq_cur : t' % bp₁.K = cur := by
                        rw [hK₁] at hoff_lt hge_m ⊢; omega
                      have ht'_eq_act : t' = t_act := by
                        have hr1 := Nat.div_add_mod t' bp₁.K
                        rw [hdiv_eq, hoff_eq_cur, hK₁, hbm2₁, Nat.mul_comm] at hr1
                        exact hr1.symm
                      rw [ht'_eq_act] at hor
                      have hrk_eq2 : rk' = rk_cur := hor.symm.trans hob₁_act.2
                      dsimp only [rk'] at hrk_eq2
                      rw [hhd₁, hK₁] at hrk_eq2
                      have h1 := add_sub_head_mod hK hhd_lt
                        (by rw [hr₁, hK₁] at hk_old_lt; exact hk_old_lt.trans hr_lt)
                      have h2 := add_sub_head_mod hK hhd_lt (hcur_lt_r.trans hr_lt)
                      rw [hrk_eq2] at h1
                      have hk_eq := h1.symm.trans h2
                      omega
                  rw [set1_of_ne _ _ _ _ hP_ne_act, set1_of_ne _ _ _ _ hP_ne_act]
                  refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                  rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                  · exact Or.inl h0
                  · refine Or.inr ⟨hPlt, ht2, ?_⟩
                    have hbe2 : bp₁.blkMeta1 (bp₁.tbPhysBlk (t' / bp₁.K)) ≠ b := fun he2 => by
                      have hab_m := (hv₁.act_bwd _ hPlt ht2).2.2
                      rw [he2, hab₁] at hab_m; exact hP_ne_act hab_m.symm
                    rwa [hac'_ne _ hbe2]
                · rw [set1_of_ne _ _ _ _ hbe] at hk_lt ⊢
                  rw [hac'_ne b' hbe] at hk_ge
                  have htf := hv₁.tail_fwd b' hb' k hk_ge hk_lt
                  dsimp only at htf
                  obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                  set rk' := (bp₁.head b' + k) % (6 * bp₁.K)
                  set t' := bp₁.tailRing b' rk'
                  have hP_ne_act : bp₁.tbPhysBlk (t' / bp₁.K) ≠ P_act := fun he => by
                    have hdiv_eq : t' / bp₁.K = bp₁.blkMeta2 P_act := by rw [← hc_m2, he]
                    have hoff_lt : t' % bp₁.K < bp₁.K := Nat.mod_lt _ (by rw [hK₁]; exact hK)
                    rcases hkind with ⟨ht0, _⟩ | ⟨_, _, hge_m⟩
                    · rw [he, hbt₁, hP_tag] at ht0; exact absurd ht0 (by decide)
                    · rw [he, hbm1₁, hP_m1] at hge_m
                      have hac₁_b : bp₁.actCur b = cur := by
                        unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
                      rw [hac₁_b] at hge_m
                      have hoff_eq_cur : t' % bp₁.K = cur := by
                        rw [hK₁] at hoff_lt hge_m ⊢; omega
                      have ht'_eq_act : t' = t_act := by
                        have hr1 := Nat.div_add_mod t' bp₁.K
                        rw [hdiv_eq, hoff_eq_cur, hK₁, hbm2₁, Nat.mul_comm] at hr1
                        exact hr1.symm
                      rw [ht'_eq_act] at hob
                      exact hbe (hob.symm.trans hob₁_act.1)
                  rw [set1_of_ne _ _ _ _ hP_ne_act, set1_of_ne _ _ _ _ hP_ne_act]
                  refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                  rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                  · exact Or.inl h0
                  · refine Or.inr ⟨hPlt, ht2, ?_⟩
                    have hbe2 : bp₁.blkMeta1 (bp₁.tbPhysBlk (t' / bp₁.K)) ≠ b := fun he2 => by
                      have hab_m := (hv₁.act_bwd _ hPlt ht2).2.2
                      rw [he2, hab₁] at hab_m; exact hP_ne_act hab_m.symm
                    rwa [hac'_ne _ hbe2]
              tail_bwd := fun P hP_le off hoff hlt hor => by
                dsimp only
                have hBf_eq : bp'.B_full = bp₁.B_full := rfl
                have hrem_eq : bp'.rem = bp₁.rem := rfl
                rw [hBf_eq] at hP_le; rw [hBf_eq, hrem_eq] at hlt
                rw [show bp'.K = bp₁.K from rfl] at hoff
                have hp : P ≠ P_act := fun he => by
                  dsimp only [bp', bp₂, freeTb] at hor
                  rw [he, set1_self] at hor
                  rcases hor with h | ⟨h, _⟩ <;> exact absurd h (by decide)
                have hor₁ : bp₁.blkTag P = 0 ∨
                    (bp₁.blkTag P = 2 ∧ bp₁.actCur (bp₁.blkMeta1 P) ≤ off) := by
                  rw [show bp'.blkTag P = bp₁.blkTag P from set1_of_ne _ _ _ _ hp,
                    show bp'.blkMeta1 P = bp₁.blkMeta1 P from rfl] at hor
                  rcases hor with h0 | ⟨h2, hge⟩
                  · exact Or.inl h0
                  · have hP_lt' : P < bp₁.B_full := by
                      rcases hlt with h1 | _
                      · exact h1
                      · by_contra hge_B
                        have heqB : P = bp₁.B_full := by omega
                        rw [heqB, hv₁.blkTag_top] at h2; exact absurd h2 (by decide)
                    have hbe2 : bp₁.blkMeta1 P ≠ b := fun he2 => by
                      have hab_m := (hv₁.act_bwd P hP_lt' h2).2.2
                      rw [he2, hab₁] at hab_m; exact hp hab_m.symm
                    rw [hac'_ne _ hbe2] at hge
                    exact Or.inr ⟨h2, hge⟩
                obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv₁.tail_bwd P hP_le off hoff hlt hor₁
                rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
                  show bp'.blkMeta2 P = bp₁.blkMeta2 P from set1_of_ne _ _ _ _ hp,
                  show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
                  show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl,
                  show bp'.head = set1 bp₁.head b ((bp₁.head b + bp.K) % (6 * bp.K)) from rfl,
                  show bp'.r = set1 bp₁.r b (bp₁.r b - bp.K) from rfl,
                  show bp'.tailRing = bp₁.tailRing from rfl]
                set t := bp₁.blkMeta2 P * bp₁.K + off
                by_cases hbe : bp₁.tailOwnerBkt t = b
                · rw [hbe, set1_self, set1_self, hac'_b]
                  rw [hbe] at hk_ge hk_lt htr
                  have hac₁_b : bp₁.actCur b = cur := by
                    unfold actCur; rw [hac₁, hK₁]; exact hcur_eq
                  rw [hac₁_b] at hk_ge
                  set k₀ := (bp₁.tailOwnerRing t + 6 * bp₁.K - bp₁.head b) % (6 * bp₁.K)
                  have hk₀_ne_cur : k₀ ≠ cur := fun hke => by
                    obtain ⟨_, _, hhdo₁, _, _⟩ := hv₁.bkt_bounds b (by rw [hM₁]; exact hb)
                    have hrk_eq : bp₁.tailOwnerRing t = rk_cur := by
                      rw [← head_add_sub_mod hhdo₁ hrko]
                      change (bp₁.head b + k₀) % (6 * bp₁.K) = rk_cur
                      rw [hke, hhd₁, hK₁]
                    rw [hrk_eq, htr₁_cur] at htr
                    have htb₁ := (hv₁.tb_fwd P hP_le (hor₁.imp id And.left)).2
                    have hdiv_t : t / bp₁.K = bp₁.blkMeta2 P := by
                      dsimp only [t]
                      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by rw [hK₁]; exact hK),
                        Nat.div_eq_of_lt hoff, zero_add]
                    have hdiv_act : t_act / bp.K = bp.blkMeta2 P_act := by
                      dsimp only [t_act]
                      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK,
                        Nat.div_eq_of_lt hcur_lt_K, zero_add]
                    rw [htr] at hdiv_act; rw [hK₁] at hdiv_t
                    have hm2_eq : bp₁.blkMeta2 P = bp.blkMeta2 P_act := hdiv_t.symm.trans hdiv_act
                    rw [← htb₁, hm2_eq, htpb₁, htb_P] at hp
                    exact hp rfl
                  have hk₀_ge_K : bp₁.K ≤ k₀ := by rw [hK₁]; omega
                  have hk_new := add_sub_promote_head_mod (by rw [hK₁]; exact hK)
                    (by rw [hhd₁, hK₁]; exact hhd_lt) hrko hk₀_ge_K
                    (hk_lt.trans (by rw [hr₁, hK₁]; exact hr_lt)) (rfl : k₀ = k₀)
                  rw [hK₁] at hk_new
                  have hk_lhs : (bp₁.tailOwnerRing t + 6 * bp₁.K -
                      (bp₁.head b + bp.K) % (6 * bp.K)) % (6 * bp₁.K) = k₀ - bp.K := by
                    rw [hK₁]; exact hk_new
                  rw [hk_lhs]
                  exact ⟨by rw [hM₁]; exact hb, hrko, Nat.zero_le _,
                    by rw [hK₁] at hk₀_ge_K; omega, htr⟩
                · rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe, hac'_ne _ hbe]
                  exact ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ }
          refine ⟨hcv', hn₁, hbc_eq, hsw_lt, fun arr b' loc' hb' hloc' => ?_⟩
          rw [htp_eq b' loc' hloc']
          exact harr₁ arr b' loc' hb' hloc'
    · -- Demote step: `bp.K < bp.actCode b`
      rw [ite_eq_right hcK]
      set cur := bp.actCode b - bp.K
      have hcur_pos : 1 ≤ cur := by dsimp only [cur]; omega
      have hcur_le_K : cur ≤ bp.K := by dsimp only [cur]; omega
      have hcur_eq : bp.actCur b = cur := by
        unfold actCur; rw [ite_eq_right hc0, ite_eq_right hcK]
      set cur' := cur - 1
      have hcur'_lt_cur : cur' < cur := by dsimp only [cur']; omega
      have hcur'_lt_K : cur' < bp.K := hcur'_lt_cur.trans_le hcur_le_K
      have hcur'_lt_r : cur' < bp.r b := hcur'_lt_cur.trans_le (hcur_eq ▸ hcur_le_r)
      set rk := (bp.head b + cur') % (6 * bp.K)
      set tIdx := bp.blkMeta2 P_act * bp.K + cur'
      have htIdx_div : tIdx / bp.K = bp.blkMeta2 P_act := by
        dsimp only [tIdx]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hcur'_lt_K, zero_add]
      have htIdx_mod : tIdx % bp.K = cur' := by
        dsimp only [tIdx]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcur'_lt_K]
      have htIdx_lt : tIdx < 8 * bp.M * bp.K := by
        have hlt_hw : bp.blkMeta2 P_act < 8 * bp.M := htb_lt.trans_le hv.tbHighWater_le_max
        have hle1 : (bp.blkMeta2 P_act + 1) * bp.K ≤ (8 * bp.M) * bp.K :=
          Nat.mul_le_mul_right bp.K hlt_hw
        rw [Nat.add_one_mul] at hle1; dsimp only [tIdx]; omega
      have htIdx_not_live : ∀ b' < bp.M, ∀ k, bp.actCur b' ≤ k → k < bp.r b' →
          bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) ≠ tIdx :=
        fun b' hb' k hk_ge hk_lt hte => by
        have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
        dsimp only at htf
        rw [hte, htIdx_div, htIdx_mod, htb_P] at htf
        rcases htf.2.2.2.1 with ⟨ht0, _⟩ | ⟨_, _, hge_m⟩
        · rw [hP_tag] at ht0; exact absurd ht0 (by decide)
        · rw [hP_m1, hcur_eq] at hge_m; omega
      have hrk_not_live : ∀ k, cur ≤ k → k < bp.r b →
          (bp.head b + k) % (6 * bp.K) ≠ rk := fun k hk_ge hk_lt hrke => by
        have h1 := add_sub_head_mod hK hhd_lt (hk_lt.trans hr_lt)
        have h2 := add_sub_head_mod hK hhd_lt (hcur'_lt_r.trans hr_lt)
        rw [hrke] at h1
        have hke := h1.symm.trans h2
        omega
      set bp₁ : BlockPoolState :=
        { bp with
          tailRing := set2 bp.tailRing b rk tIdx
          tailOwnerBkt := set1 bp.tailOwnerBkt tIdx b
          tailOwnerRing := set1 bp.tailOwnerRing tIdx rk }
      by_cases hgt1 : 1 < cur
      · rw [ite_eq_left hgt1]; dsimp only
        set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b - 1) }
        have hac'_b : bp'.actCur b = cur' := by
          unfold actCur
          have hc' : bp'.actCode b = bp.actCode b - 1 := set1_self _ _ _
          have hk' : bp'.K = bp.K := rfl
          rw [hc', hk', ite_eq_right (by omega), ite_eq_right (by omega)]
          dsimp only [cur', cur]; omega
        have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
          unfold actCur
          have hc' : bp'.actCode b' = bp.actCode b' := set1_of_ne _ _ _ _ hne
          have hk' : bp'.K = bp.K := rfl
          rw [hc', hk']
        have htp_lt : ∀ b' loc', loc' < bp.bktCount b' →
            bp'.toPhys b' loc' = bp.toPhys b' loc' := fun b' loc' hloc' => by
          have heff_eq : ∀ E o, bp'.effBlk E o = bp.effBlk E o := fun _ _ => rfl
          have hpt_eq : ∀ t, bp'.physOfTail t = bp.physOfTail t := fun _ => rfl
          have hq_eq : bp'.q b' = bp.q b' := rfl
          have hK_eq : bp'.K = bp.K := rfl
          have hab_eq : bp'.actBlk b' = bp.actBlk b' := rfl
          have hsl_eq : bp'.slabOf = bp.slabOf := rfl
          have hhd_eq : bp'.head b' = bp.head b' := rfl
          by_cases hbe : b' = b
          · subst b'
            unfold toPhys
            rw [hq_eq, hK_eq, hab_eq, hsl_eq, hhd_eq, hac'_b, hcur_eq]
            simp only [heff_eq, hpt_eq]
            dsimp only [bp', bp₁]
            by_cases hslab : loc' < bp.q b * bp.K
            · rw [ite_eq_left hslab, ite_eq_left hslab]
            · rw [ite_eq_right hslab, ite_eq_right hslab]
              set k := loc' - bp.q b * bp.K
              have hk_lt_r : k < bp.r b := by unfold bktCount at hloc'; omega
              by_cases hk_lt : k < cur'
              · rw [ite_eq_left hk_lt, ite_eq_left (hk_lt.trans hcur'_lt_cur)]
              · rw [ite_eq_right hk_lt]
                by_cases hk_eq : k = cur'
                · rw [hk_eq, ite_eq_left hcur'_lt_cur, set2_self]
                  unfold physOfTail
                  rw [htIdx_div, htIdx_mod, htb_P]
                · have hk_ge_cur : cur ≤ k := by omega
                  rw [ite_eq_right (not_lt.mpr hk_ge_cur),
                    set2_of_ne _ _ _ _ _ _ (fun h => hrk_not_live k hk_ge_cur hk_lt_r h.2)]
          · unfold toPhys
            rw [hq_eq, hK_eq, hab_eq, hsl_eq, hhd_eq, hac'_ne b' hbe]
            simp only [heff_eq, hpt_eq]
            dsimp only [bp', bp₁]
            simp only [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
        have hcv' : bp'.CoreValid :=
          { M_pos := hv.M_pos
            K_ge := hv.K_ge
            bkt_bounds := fun b' hb' => by
              by_cases hbe : b' = b
              · subst b'; rw [hac'_b]
                dsimp only [bp', bp₁]; rw [set1_self]
                exact ⟨hq_le, hr_lt, hhd_lt, by omega, hcur'_lt_r.le⟩
              · rw [hac'_ne b' hbe]
                dsimp only [bp', bp₁]; rw [set1_of_ne _ _ _ _ hbe]
                exact hv.bkt_bounds b' hb'
            blkTag_lt := hv.blkTag_lt
            blkTag_top := hv.blkTag_top
            unres_fwd := hv.unres_fwd
            unres_bwd := hv.unres_bwd
            slab_fwd := hv.slab_fwd
            slab_bwd := hv.slab_bwd
            act_fwd := fun b' hb' hne => by
              dsimp only [bp', bp₁] at hb' hne ⊢
              by_cases hbe : b' = b
              · subst b'; exact ⟨hP_lt, hP_tag, hP_m1⟩
              · rw [set1_of_ne _ _ _ _ hbe] at hne; exact hv.act_fwd b' hb' hne
            act_bwd := fun P hP htag2 => by
              obtain ⟨h1, h2, h3⟩ := hv.act_bwd P hP htag2
              dsimp only [bp', bp₁]
              refine ⟨h1, ?_, h3⟩
              by_cases hbe : bp.blkMeta1 P = b
              · rw [hbe, set1_self]; omega
              · rw [set1_of_ne _ _ _ _ hbe]; exact h2
            tb_fwd := hv.tb_fwd
            freeTb_valid := hv.freeTb_valid
            freeTb_inj := hv.freeTb_inj
            tbHighWater_supply := hv.tbHighWater_supply
            tbHighWater_le_max := hv.tbHighWater_le_max
            topSwap_act_le := hv.topSwap_act_le
            topSwap_valid := hv.topSwap_valid
            tail_fwd := fun b' hb' k hk_ge hk_lt => by
              have hBf_eq : bp'.B_full = bp.B_full := rfl
              have hrem_eq : bp'.rem = bp.rem := rfl
              rw [hBf_eq, hrem_eq]
              by_cases hbe : b' = b
              · subst b'; rw [hac'_b] at hk_ge
                dsimp only [bp', bp₁] at hk_lt ⊢
                by_cases hke : k = cur'
                · subst hke; rw [set2_self, htIdx_div, htIdx_mod, htb_P, set1_self, set1_self]
                  exact ⟨htIdx_lt, hP_lt.le, rfl,
                    Or.inr ⟨hP_lt, hP_tag, by rw [hP_m1, hac'_b]⟩, rfl, rfl⟩
                · have hk_ge_cur : bp.actCur b ≤ k := by rw [hcur_eq]; omega
                  rw [set2_of_ne _ _ _ _ _ _ (fun h =>
                    hrk_not_live k (by rw [← hcur_eq]; exact hk_ge_cur) hk_lt h.2)]
                  have htf := hv.tail_fwd b hb k hk_ge_cur hk_lt
                  dsimp only at htf
                  have hne_t : bp.tailRing b ((bp.head b + k) % (6 * bp.K)) ≠ tIdx :=
                    htIdx_not_live b hb k hk_ge_cur hk_lt
                  rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
                  obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                  refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                  rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                  · exact Or.inl h0
                  · refine Or.inr ⟨hPlt, ht2, ?_⟩
                    by_cases hbe2 : bp.blkMeta1 (bp.tbPhysBlk
                        (bp.tailRing b ((bp.head b + k) % (6 * bp.K)) / bp.K)) = b
                    · rw [hbe2, hac'_b]; rw [hbe2, hcur_eq] at hge_m; omega
                    · rwa [hac'_ne _ hbe2]
              · rw [hac'_ne b' hbe] at hk_ge
                dsimp only [bp', bp₁] at hb' hk_lt ⊢
                rw [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
                have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
                dsimp only at htf
                have hne_t : bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) ≠ tIdx :=
                  htIdx_not_live b' hb' k hk_ge hk_lt
                rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
                obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                · exact Or.inl h0
                · refine Or.inr ⟨hPlt, ht2, ?_⟩
                  by_cases hbe2 : bp.blkMeta1 (bp.tbPhysBlk
                      (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K)) = b
                  · rw [hbe2, hac'_b]; rw [hbe2, hcur_eq] at hge_m; omega
                  · rwa [hac'_ne _ hbe2]
            tail_bwd := fun P hP_le off hoff hlt hor => by
              dsimp only
              have hBf_eq : bp'.B_full = bp.B_full := rfl
              have hrem_eq : bp'.rem = bp.rem := rfl
              rw [hBf_eq] at hP_le; rw [hBf_eq, hrem_eq] at hlt
              set t := bp.blkMeta2 P * bp.K + off
              have hK_eq : bp'.K = bp.K := rfl
              rw [hK_eq]
              by_cases hte : t = tIdx
              · have htob : bp'.tailOwnerBkt t = b := by
                  dsimp only [bp', bp₁]; rw [hte, set1_self]
                have htor : bp'.tailOwnerRing t = rk := by
                  dsimp only [bp', bp₁]; rw [hte, set1_self]
                rw [htob, htor, hac'_b]
                dsimp only [bp', bp₁]
                have hrk_lt : rk < 6 * bp.K := Nat.mod_lt _ (by omega)
                have hk_re : (rk + 6 * bp.K - bp.head b) % (6 * bp.K) = cur' :=
                  add_sub_head_mod hK hhd_lt (hcur'_lt_r.trans hr_lt)
                rw [hk_re, set2_self]
                exact ⟨hb, hrk_lt, le_rfl, hcur'_lt_r, hte.symm⟩
              · have htob : bp'.tailOwnerBkt t = bp.tailOwnerBkt t := set1_of_ne _ _ _ _ hte
                have htor : bp'.tailOwnerRing t = bp.tailOwnerRing t := set1_of_ne _ _ _ _ hte
                rw [htob, htor]
                have hor₀ : bp.blkTag P = 0 ∨
                    (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off) := by
                  have hbt_p : bp'.blkTag P = bp.blkTag P := rfl
                  have hbm1_p : bp'.blkMeta1 P = bp.blkMeta1 P := rfl
                  rw [hbt_p, hbm1_p] at hor
                  rcases hor with h0 | ⟨h2, hge⟩
                  · exact Or.inl h0
                  · refine Or.inr ⟨h2, ?_⟩
                    by_cases hbe2 : bp.blkMeta1 P = b
                    · rw [hbe2, hac'_b] at hge; rw [hbe2, hcur_eq]
                      have hP_lt' : P < bp.B_full := by
                        rcases hlt with h1 | _
                        · exact h1
                        · by_contra hgeB
                          have heqB : P = bp.B_full := by omega
                          rw [heqB, hv.blkTag_top] at h2; exact absurd h2 (by decide)
                      have hab_m := (hv.act_bwd P hP_lt' h2).2.2
                      rw [hbe2] at hab_m
                      have hoff_ne : off ≠ cur' := fun hoe => by
                        subst hab_m; subst hoe; exact hte rfl
                      omega
                    · rwa [hac'_ne _ hbe2] at hge
                obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt hor₀
                have hne2 : ¬(bp.tailOwnerBkt t = b ∧ bp.tailOwnerRing t = rk) := by
                  rintro ⟨he1, he2⟩
                  rw [he1, he2] at hk_ge hk_lt
                  have hk_re : (rk + 6 * bp.K - bp.head b) % (6 * bp.K) = cur' :=
                    add_sub_head_mod hK hhd_lt (hcur'_lt_r.trans hr_lt)
                  rw [hk_re, hcur_eq] at hk_ge; omega
                have htr_p : bp'.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) =
                    bp.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) :=
                  set2_of_ne _ _ _ _ _ _ hne2
                have hM_eq : bp'.M = bp.M := rfl
                have hhd_eq : ∀ x, bp'.head x = bp.head x := fun _ => rfl
                have hr_eq : ∀ x, bp'.r x = bp.r x := fun _ => rfl
                rw [htr_p, hM_eq, hhd_eq, hr_eq]
                refine ⟨hbo, hrko, ?_, hk_lt, htr⟩
                by_cases hbe : bp.tailOwnerBkt t = b
                · rw [hbe, hac'_b]; rw [hbe, hcur_eq] at hk_ge
                  dsimp only [t, cur'] at hk_ge ⊢; omega
                · rwa [hac'_ne _ hbe] }
        exact ⟨hcv', rfl, fun _ => rfl, fun _ h => by simp at h,
          fun _ b' loc' _ hloc' => congrArg _ (htp_lt b' loc' hloc')⟩
      · -- Demote finish: `cur = 1` (`cur' = 0`)
        rw [ite_eq_right hgt1]; dsimp only
        have hcur1 : cur = 1 := by omega
        have hcur'0 : cur' = 0 := by dsimp only [cur']; omega
        set bp₂ := bp₁.unresPush P_act
        set bp' : BlockPoolState := { bp₂ with actCode := set1 bp₂.actCode b 0 }
        have hac'_b : bp'.actCur b = 0 := by
          unfold actCur
          have hc' : bp'.actCode b = 0 := set1_self _ _ _
          rw [hc', ite_eq_left rfl]
        have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
          unfold actCur
          have hc' : bp'.actCode b' = bp.actCode b' := set1_of_ne _ _ _ _ hne
          have hk' : bp'.K = bp.K := rfl
          rw [hc', hk']
        have htp_lt : ∀ b' loc', loc' < bp.bktCount b' →
            bp'.toPhys b' loc' = bp.toPhys b' loc' := fun b' loc' hloc' => by
          have heff_eq : ∀ E o, bp'.effBlk E o = bp.effBlk E o := fun _ _ => rfl
          have hpt_eq : ∀ t, bp'.physOfTail t = bp.physOfTail t := fun _ => rfl
          have hq_eq : bp'.q b' = bp.q b' := rfl
          have hK_eq : bp'.K = bp.K := rfl
          have hab_eq : bp'.actBlk b' = bp.actBlk b' := rfl
          have hsl_eq : bp'.slabOf = bp.slabOf := rfl
          have hhd_eq : bp'.head b' = bp.head b' := rfl
          by_cases hbe : b' = b
          · subst b'
            unfold toPhys
            rw [hq_eq, hK_eq, hab_eq, hsl_eq, hhd_eq, hac'_b, hcur_eq]
            simp only [heff_eq, hpt_eq]
            dsimp only [bp', bp₂, unresPush, bp₁]
            by_cases hslab : loc' < bp.q b * bp.K
            · rw [ite_eq_left hslab, ite_eq_left hslab]
            · rw [ite_eq_right hslab, ite_eq_right hslab, ite_eq_right (Nat.not_lt_zero _)]
              set k := loc' - bp.q b * bp.K
              have hk_lt_r : k < bp.r b := by unfold bktCount at hloc'; omega
              by_cases hk0 : k = 0
              · rw [hk0, hcur1, ite_eq_left Nat.zero_lt_one,
                  show (bp.head b + 0) % (6 * bp.K) = rk by rw [← hcur'0], set2_self]
                unfold physOfTail
                rw [htIdx_div, htIdx_mod, htb_P, hcur'0]
              · have hk_ge_cur : cur ≤ k := by omega
                rw [ite_eq_right (not_lt.mpr hk_ge_cur),
                  set2_of_ne _ _ _ _ _ _ (fun h => hrk_not_live k hk_ge_cur hk_lt_r h.2)]
          · unfold toPhys
            rw [hq_eq, hK_eq, hab_eq, hsl_eq, hhd_eq, hac'_ne b' hbe]
            simp only [heff_eq, hpt_eq]
            dsimp only [bp', bp₂, unresPush, bp₁]
            simp only [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
        have hP_ne_B : P_act ≠ bp.B_full := ne_of_lt hP_lt
        have hcv' : bp'.CoreValid :=
          { M_pos := hv.M_pos
            K_ge := hv.K_ge
            bkt_bounds := fun b' hb' => by
              by_cases hbe : b' = b
              · subst b'; rw [hac'_b]
                dsimp only [bp', bp₂, unresPush, bp₁]; rw [set1_self]
                exact ⟨hq_le, hr_lt, hhd_lt, Nat.zero_le _, Nat.zero_le _⟩
              · rw [hac'_ne b' hbe]
                dsimp only [bp', bp₂, unresPush, bp₁]; rw [set1_of_ne _ _ _ _ hbe]
                exact hv.bkt_bounds b' hb'
            blkTag_lt := fun P hP => by
              dsimp only [bp', bp₂, unresPush, bp₁]
              by_cases hp : P = P_act
              · subst hp; rw [set1_self]; decide
              · rw [set1_of_ne _ _ _ _ hp]; exact hv.blkTag_lt P hP
            blkTag_top := by
              have hBf_eq : bp'.B_full = bp.B_full := rfl
              rw [hBf_eq]; dsimp only [bp', bp₂, unresPush, bp₁]
              rw [set1_of_ne _ _ _ _ hP_ne_B.symm]; exact hv.blkTag_top
            unres_fwd := fun i hi => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hi ⊢
              by_cases hit : i = bp.unresLen
              · subst hit; rw [set1_self, set1_self, set1_self]
                exact ⟨hP_lt, rfl, rfl⟩
              · obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i (by omega)
                have hneP : bp.unresStack i ≠ P_act := fun he => by
                  rw [he, hP_tag] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hit, set1_of_ne _ _ _ _ hneP, set1_of_ne _ _ _ _ hneP]
                exact ⟨h1, h2, h3⟩
            unres_bwd := fun P hP htag0 => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hP htag0 ⊢
              by_cases hp : P = P_act
              · subst hp; rw [set1_self, set1_self]
                exact ⟨Nat.lt_succ_self _, rfl⟩
              · rw [set1_of_ne _ _ _ _ hp] at htag0 ⊢
                obtain ⟨h1, h2⟩ := hv.unres_bwd P hP htag0
                rw [set1_of_ne _ _ _ _ (ne_of_lt h1)]
                exact ⟨Nat.lt_succ_of_lt h1, h2⟩
            slab_fwd := fun b' hb' v hv_lt => by
              obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
              have hneP : bp.slabOf b' v ≠ P_act := fun he => by
                rw [he, hP_tag] at h2; exact absurd h2 (by decide)
              dsimp only [bp', bp₂, unresPush, bp₁]
              rw [set1_of_ne _ _ _ _ hneP, set1_of_ne _ _ _ _ hneP]
              exact ⟨h1, h2, h3, h4⟩
            slab_bwd := fun P hP htag1 => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hP htag1 ⊢
              have hp : P ≠ P_act := fun he => by
                rw [he, set1_self] at htag1; exact absurd htag1 (by decide)
              rw [set1_of_ne _ _ _ _ hp] at htag1 ⊢
              exact hv.slab_bwd P hP htag1
            act_fwd := fun b' hb' hne => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hb' hne ⊢
              have hbe : b' ≠ b := fun he => by subst he; rw [set1_self] at hne; exact hne rfl
              rw [set1_of_ne _ _ _ _ hbe] at hne
              obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
              have hp : bp.actBlk b' ≠ P_act := fun he => by
                rw [he, hP_m1] at h3; exact hbe h3.symm
              rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
              exact ⟨h1, h2, h3⟩
            act_bwd := fun P hP htag2 => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hP htag2 ⊢
              have hp : P ≠ P_act := fun he => by
                rw [he, set1_self] at htag2; exact absurd htag2 (by decide)
              rw [set1_of_ne _ _ _ _ hp] at htag2 ⊢
              obtain ⟨h1, h2, h3⟩ := hv.act_bwd P hP htag2
              have hbe : bp.blkMeta1 P ≠ b := fun he => by
                rw [he] at h3; exact hp h3.symm
              rw [set1_of_ne _ _ _ _ hbe]
              exact ⟨h1, h2, h3⟩
            tb_fwd := fun P hP hor => by
              dsimp only [bp', bp₂, unresPush, bp₁] at hP hor ⊢
              by_cases hp : P = P_act
              · subst hp; exact ⟨htb_lt, htb_P⟩
              · rw [set1_of_ne _ _ _ _ hp] at hor; exact hv.tb_fwd P hP hor
            freeTb_valid := fun i hi => by
              obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
              refine ⟨h1, fun P hP hor => ?_⟩
              dsimp only [bp', bp₂, unresPush, bp₁] at hP hor ⊢
              by_cases hp : P = P_act
              · subst hp; exact h2 P_act hP (Or.inr hP_tag)
              · rw [set1_of_ne _ _ _ _ hp] at hor; exact h2 P hP hor
            freeTb_inj := hv.freeTb_inj
            tbHighWater_supply := by
              have hcard_eq : ((Finset.range (bp'.B_full + 1)).filter
                  (fun P => bp'.blkTag P = 0 ∨ bp'.blkTag P = 2)).card =
                  ((Finset.range (bp.B_full + 1)).filter
                    (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card :=
                congrArg Finset.card (by
                  ext P; simp only [mem_filter]
                  have hBf : bp'.B_full = bp.B_full := rfl
                  rw [hBf]
                  refine and_congr_right fun _ => ?_
                  change (set1 bp.blkTag P_act 0 P = 0 ∨ set1 bp.blkTag P_act 0 P = 2) ↔ _
                  by_cases hp : P = P_act
                  · subst hp; simp only [set1_self, hP_tag, true_or, or_true]
                  · rw [set1_of_ne _ _ _ _ hp])
              change bp.tbHighWater ≤ bp.freeTbTop + _
              rw [hcard_eq]
              exact hv.tbHighWater_supply
            tbHighWater_le_max := hv.tbHighWater_le_max
            topSwap_act_le := hv.topSwap_act_le
            topSwap_valid := fun ha => by
              obtain ⟨h1, h2, h3, h4, h5⟩ := hv.topSwap_valid ha
              dsimp only [bp', bp₂, unresPush, bp₁]
              have hne_d : bp.topSwapDst ≠ P_act := fun he => by
                rw [he, hP_tag] at h4; exact absurd h4 (by decide)
              rw [set1_of_ne _ _ _ _ hne_d]
              exact ⟨h1, h2, h3, h4, h5⟩
            tail_fwd := fun b' hb' k hk_ge hk_lt => by
              dsimp only
              have hBf_eq : bp'.B_full = bp.B_full := rfl
              have hrem_eq : bp'.rem = bp.rem := rfl
              rw [hBf_eq, hrem_eq]
              rw [show bp'.M = bp.M from rfl] at hb'
              rw [show bp'.r = bp.r from rfl] at hk_lt
              rw [show bp'.M = bp.M from rfl, show bp'.K = bp.K from rfl,
                show bp'.head = bp.head from rfl,
                show bp'.tbPhysBlk = bp.tbPhysBlk from rfl,
                show bp'.blkMeta2 = bp.blkMeta2 from rfl,
                show bp'.tailRing = set2 bp.tailRing b rk tIdx from rfl,
                show bp'.blkTag = set1 bp.blkTag P_act 0 from rfl,
                show bp'.blkMeta1 = set1 bp.blkMeta1 P_act bp.unresLen from rfl,
                show bp'.tailOwnerBkt = set1 bp.tailOwnerBkt tIdx b from rfl,
                show bp'.tailOwnerRing = set1 bp.tailOwnerRing tIdx rk from rfl]
              by_cases hbe : b' = b
              · subst b'
                by_cases hk0 : k = 0
                · subst hk0
                  have hrk0 : (bp.head b + 0) % (6 * bp.K) = rk := by rw [← hcur'0]
                  rw [hrk0, set2_self]
                  have hd0 : tIdx / bp.K = bp.blkMeta2 P_act := htIdx_div
                  have hm0 : tIdx % bp.K = 0 := htIdx_mod.trans hcur'0
                  rw [hd0, hm0, htb_P]
                  rw [set1_self, set1_self, set1_self, set1_self]
                  exact ⟨htIdx_lt, hP_lt.le, rfl, Or.inl ⟨rfl, Or.inl hP_lt⟩, rfl, rfl⟩
                · have hk_ge_cur : bp.actCur b ≤ k := by rw [hcur_eq, hcur1]; omega
                  rw [set2_of_ne _ _ _ _ _ _ (fun h =>
                    hrk_not_live k (by rw [hcur1]; omega) hk_lt h.2)]
                  have htf := hv.tail_fwd b hb k hk_ge_cur hk_lt
                  dsimp only at htf
                  have hne_t : bp.tailRing b ((bp.head b + k) % (6 * bp.K)) ≠ tIdx :=
                    htIdx_not_live b hb k hk_ge_cur hk_lt
                  rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
                  obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                  refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                  set Pt := bp.tbPhysBlk (bp.tailRing b ((bp.head b + k) % (6 * bp.K)) / bp.K)
                  by_cases hp : Pt = P_act
                  · rw [hp, set1_self]; exact Or.inl ⟨rfl, Or.inl hP_lt⟩
                  · rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                    rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                    · exact Or.inl h0
                    · have hbe2 : bp.blkMeta1 Pt ≠ b := fun he2 => by
                        have hab_m := (hv.act_bwd Pt hPlt ht2).2.2
                        rw [he2] at hab_m; exact hp hab_m.symm
                      rw [hac'_ne _ hbe2]
                      exact Or.inr ⟨hPlt, ht2, hge_m⟩
              · rw [hac'_ne b' hbe] at hk_ge
                rw [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
                have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
                dsimp only at htf
                have hne_t : bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) ≠ tIdx :=
                  htIdx_not_live b' hb' k hk_ge hk_lt
                rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
                obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                set Pt := bp.tbPhysBlk (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K)
                by_cases hp : Pt = P_act
                · rw [hp, set1_self]; exact Or.inl ⟨rfl, Or.inl hP_lt⟩
                · rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                  rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                  · exact Or.inl h0
                  · have hbe2 : bp.blkMeta1 Pt ≠ b := fun he2 => by
                      have hab_m := (hv.act_bwd Pt hPlt ht2).2.2
                      rw [he2] at hab_m; exact hp hab_m.symm
                    rw [hac'_ne _ hbe2]
                    exact Or.inr ⟨hPlt, ht2, hge_m⟩
            tail_bwd := fun P hP_le off hoff hlt hor => by
              dsimp only
              have hBf_eq : bp'.B_full = bp.B_full := rfl
              have hrem_eq : bp'.rem = bp.rem := rfl
              rw [hBf_eq] at hP_le; rw [hBf_eq, hrem_eq] at hlt
              rw [show bp'.blkMeta2 P = bp.blkMeta2 P from rfl,
                show bp'.K = bp.K from rfl]
              set t := bp.blkMeta2 P * bp.K + off
              by_cases hte : t = tIdx
              · have htob : bp'.tailOwnerBkt t = b := by
                  dsimp only [bp', bp₂, unresPush, bp₁]; rw [hte, set1_self]
                have htor : bp'.tailOwnerRing t = rk := by
                  dsimp only [bp', bp₂, unresPush, bp₁]; rw [hte, set1_self]
                rw [htob, htor, hac'_b]
                dsimp only [bp', bp₂, unresPush, bp₁]
                have hrk_lt : rk < 6 * bp.K := Nat.mod_lt _ (by omega)
                have hk_re : (rk + 6 * bp.K - bp.head b) % (6 * bp.K) = cur' :=
                  add_sub_head_mod hK hhd_lt (hcur'_lt_r.trans hr_lt)
                rw [hk_re, set2_self]
                exact ⟨hb, hrk_lt, Nat.zero_le _, hcur'_lt_r, hte.symm⟩
              · have htob : bp'.tailOwnerBkt t = bp.tailOwnerBkt t := by
                  dsimp only [bp', bp₂, unresPush, bp₁]; exact set1_of_ne _ _ _ _ hte
                have htor : bp'.tailOwnerRing t = bp.tailOwnerRing t := by
                  dsimp only [bp', bp₂, unresPush, bp₁]; exact set1_of_ne _ _ _ _ hte
                rw [htob, htor]
                have hor₀' : bp.blkTag P = 0 ∨
                    (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off) := by
                  by_cases hp : P = P_act
                  · subst hp
                    have hoff_ne0 : off ≠ 0 := fun hoe => by
                      subst hoe; exact hte (by dsimp only [t, tIdx]; rw [hcur'0])
                    exact Or.inr ⟨hP_tag, by rw [hP_m1, hcur_eq, hcur1]; omega⟩
                  · have hbt_p : bp'.blkTag P = bp.blkTag P := by
                      dsimp only [bp', bp₂, unresPush, bp₁]; exact set1_of_ne _ _ _ _ hp
                    have hbm1_p : bp'.blkMeta1 P = bp.blkMeta1 P := by
                      dsimp only [bp', bp₂, unresPush, bp₁]; exact set1_of_ne _ _ _ _ hp
                    rw [hbt_p, hbm1_p] at hor
                    rcases hor with h0 | ⟨h2, hge⟩
                    · exact Or.inl h0
                    · have hP_lt' : P < bp.B_full := by
                        rcases hlt with h1 | _
                        · exact h1
                        · by_contra hgeB
                          have heqB : P = bp.B_full := by omega
                          rw [heqB, hv.blkTag_top] at h2; exact absurd h2 (by decide)
                      have hbe2 : bp.blkMeta1 P ≠ b := fun he2 => by
                        have hab_m := (hv.act_bwd P hP_lt' h2).2.2
                        rw [he2] at hab_m; exact hp hab_m.symm
                      rw [hac'_ne _ hbe2] at hge
                      exact Or.inr ⟨h2, hge⟩
                obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt hor₀'
                have hne2 : ¬(bp.tailOwnerBkt t = b ∧ bp.tailOwnerRing t = rk) := by
                  rintro ⟨he1, he2⟩
                  rw [he1, he2] at hk_ge hk_lt
                  have hk_re : (rk + 6 * bp.K - bp.head b) % (6 * bp.K) = cur' :=
                    add_sub_head_mod hK hhd_lt (hcur'_lt_r.trans hr_lt)
                  rw [hk_re, hcur_eq, hcur1, hcur'0] at hk_ge; omega
                have htr_p : bp'.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) =
                    bp.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) := by
                  dsimp only [bp', bp₂, unresPush, bp₁]; exact set2_of_ne _ _ _ _ _ _ hne2
                rw [htr_p]
                have hM_eq : bp'.M = bp.M := rfl
                have hhd_eq : ∀ x, bp'.head x = bp.head x := fun _ => rfl
                have hr_eq : ∀ x, bp'.r x = bp.r x := fun _ => rfl
                rw [hM_eq, hhd_eq, hr_eq]
                refine ⟨hbo, hrko, ?_, hk_lt, htr⟩
                by_cases hbe : bp.tailOwnerBkt t = b
                · rw [hbe, hac'_b]; exact Nat.zero_le _
                · rwa [hac'_ne _ hbe] }
        exact ⟨hcv', rfl, fun _ => rfl, fun _ h => by simp at h,
          fun _ b' loc' _ hloc' => congrArg _ (htp_lt b' loc' hloc')⟩

/-- `maybeStartBktJob` preserves `CoreValid`, `nSide`, `bktCount`, and every `toPhys` slot. -/
theorem CoreValid.maybeStartBktJob_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    {b : ℕ} (hb : b < bp.M) :
    let bp' := bp.maybeStartBktJob b
    bp'.CoreValid ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp'.toPhys b' loc' = bp.toPhys b' loc') := by
  have hK := hv.K_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, _⟩ := hv.bkt_bounds b hb
  unfold maybeStartBktJob
  by_cases hc_nz : bp.actCode b ≠ 0
  · rw [ite_eq_left hc_nz]
    exact ⟨hv, rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩
  · rw [ite_eq_right hc_nz]
    push Not at hc_nz
    by_cases hprom : 5 * bp.K ≤ bp.r b ∧ bp.q b < bp.maxSlabs ∧ 5 ≤ bp.unresLen
    · rw [ite_eq_left hprom]; dsimp only
      obtain ⟨hr_ge5, hq_lt_ms, h5_ul⟩ := hprom
      obtain ⟨hidx5, hidx_lt, hP_add3, hP_avoids⟩ := hv.findPromoteIdx_spec h5_ul
      set idx := bp.findPromoteIdx
      set P_act := bp.unresStack idx
      obtain ⟨hP_lt, hP_tag0, hP_m1_idx⟩ := hv.unres_fwd idx hidx_lt
      set lastIdx := bp.unresLen - 1
      set P_last := bp.unresStack lastIdx
      obtain ⟨hPl_lt, hPl_tag0, hPl_m1⟩ := hv.unres_fwd lastIdx (by omega)
      have hP_ne_B : P_act ≠ bp.B_full := ne_of_lt hP_lt
      set bp₁ := bp.unresRemoveAt idx
      set bp' : BlockPoolState :=
        { bp₁ with
          blkTag := set1 bp₁.blkTag P_act 2
          blkMeta1 := set1 bp₁.blkMeta1 P_act b
          actBlk := set1 bp₁.actBlk b P_act
          actCode := set1 bp₁.actCode b 1 }
      have hac'_eq : ∀ b', bp'.actCur b' = bp.actCur b' := fun b' => by
        unfold actCur
        have hk' : bp'.K = bp.K := rfl
        by_cases hbe : b' = b
        · subst b'
          have hc' : bp'.actCode b = 1 := set1_self _ _ _
          rw [hc', hk', hc_nz, ite_eq_left rfl, ite_eq_right Nat.one_ne_zero,
            ite_eq_left (Nat.succ_le_of_lt hK)]
        · have hc' : bp'.actCode b' = bp.actCode b' := set1_of_ne _ _ _ _ hbe
          rw [hc', hk']
      have htp_eq : ∀ b' loc', bp'.toPhys b' loc' = bp.toPhys b' loc' := fun b' loc' => by
        unfold toPhys
        have hq_eq : bp'.q b' = bp.q b' := rfl
        have hK_eq : bp'.K = bp.K := rfl
        have hsl_eq : bp'.slabOf = bp.slabOf := rfl
        have hhd_eq : bp'.head b' = bp.head b' := rfl
        have htr_eq : bp'.tailRing = bp.tailRing := rfl
        have heff_eq : ∀ E o, bp'.effBlk E o = bp.effBlk E o := fun _ _ => rfl
        have hpt_eq : ∀ t, bp'.physOfTail t = bp.physOfTail t := fun _ => rfl
        rw [hq_eq, hK_eq, hsl_eq, hhd_eq, htr_eq, hac'_eq b']
        simp only [heff_eq, hpt_eq]
        by_cases hbe : b' = b
        · subst b'
          have hac0 : bp.actCur b = 0 := by unfold actCur; rw [ite_eq_left hc_nz]
          rw [hac0]
          by_cases hslab : loc' < bp.q b * bp.K
          · rw [ite_eq_left hslab, ite_eq_left hslab]
          · rw [ite_eq_right hslab, ite_eq_right hslab,
              ite_eq_right (Nat.not_lt_zero _), ite_eq_right (Nat.not_lt_zero _)]
        · have hab' : bp'.actBlk b' = bp.actBlk b' := set1_of_ne _ _ _ _ hbe
          rw [hab']
      have hPl_ne_P : idx < lastIdx → P_last ≠ P_act := fun hlt he => by
        have h : bp.blkMeta1 P_last = lastIdx := hPl_m1
        rw [he, hP_m1_idx] at h; omega
      have hcv' : bp'.CoreValid :=
        { M_pos := hv.M_pos
          K_ge := hv.K_ge
          bkt_bounds := fun b' hb' => by
            rw [hac'_eq b']
            dsimp only [bp', bp₁, unresRemoveAt] at hb' ⊢
            by_cases hbe : b' = b
            · subst b'; rw [set1_self]
              have hac0 : bp.actCur b = 0 := by unfold actCur; rw [ite_eq_left hc_nz]
              rw [hac0]
              exact ⟨hq_le, hr_lt, hhd_lt, by omega, Nat.zero_le _⟩
            · rw [set1_of_ne _ _ _ _ hbe]; exact hv.bkt_bounds b' hb'
          blkTag_lt := fun P hP => by
            dsimp only [bp', bp₁, unresRemoveAt]
            by_cases hp : P = P_act
            · subst hp; rw [set1_self]; decide
            · rw [set1_of_ne _ _ _ _ hp]; exact hv.blkTag_lt P hP
          blkTag_top := by
            have hBf_eq : bp'.B_full = bp.B_full := rfl
            rw [hBf_eq]; dsimp only [bp', bp₁, unresRemoveAt]
            rw [set1_of_ne _ _ _ _ hP_ne_B.symm]; exact hv.blkTag_top
          unres_fwd := fun i hi => by
            dsimp only [bp', bp₁, unresRemoveAt] at hi ⊢
            by_cases hie : i = idx
            · subst hie
              have hilt : idx < lastIdx := hi
              have hneP := hPl_ne_P hilt
              rw [set1_self, set1_of_ne _ _ _ _ hneP, set1_of_ne _ _ _ _ hneP,
                ite_eq_left hilt, set1_self]
              exact ⟨hPl_lt, hPl_tag0, rfl⟩
            · rw [set1_of_ne _ _ _ _ hie]
              obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i (by omega)
              have hneP : bp.unresStack i ≠ P_act := fun he => by
                rw [he, hP_m1_idx] at h3; exact hie h3.symm
              have hnePl : bp.unresStack i ≠ P_last := fun he => by
                rw [he, hPl_m1] at h3; omega
              rw [set1_of_ne _ _ _ _ hneP, set1_of_ne _ _ _ _ hneP]
              split_ifs with hilt
              · rw [set1_of_ne _ _ _ _ hnePl]; exact ⟨h1, h2, h3⟩
              · exact ⟨h1, h2, h3⟩
          unres_bwd := fun P hP htag0 => by
            dsimp only [bp', bp₁, unresRemoveAt] at hP htag0 ⊢
            have hp : P ≠ P_act := fun he => by
              rw [he, set1_self] at htag0; exact absurd htag0 (by decide)
            rw [set1_of_ne _ _ _ _ hp] at htag0 ⊢
            obtain ⟨hm_lt, hm_eq⟩ := hv.unres_bwd P hP htag0
            by_cases hPl : P = P_last
            · subst hPl
              have hilt : idx < lastIdx := by
                by_contra hge
                have heq_idx : idx = lastIdx := by omega
                exact hp (by dsimp only [P_last, P_act]; rw [heq_idx])
              rw [ite_eq_left hilt, set1_self, set1_self]
              exact ⟨hilt, rfl⟩
            · have hm_ne_last : bp.blkMeta1 P ≠ lastIdx := fun he => by
                rw [he] at hm_eq; exact hPl hm_eq.symm
              have hm_ne_idx : bp.blkMeta1 P ≠ idx := fun he => by
                rw [he] at hm_eq; exact hp hm_eq.symm
              split_ifs with hilt
              · rw [set1_of_ne _ _ _ _ hPl, set1_of_ne _ _ _ _ hm_ne_idx]
                exact ⟨by omega, hm_eq⟩
              · rw [set1_of_ne _ _ _ _ hm_ne_idx]
                exact ⟨by omega, hm_eq⟩
          slab_fwd := fun b' hb' v hv_lt => by
            obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
            have hneP : bp.slabOf b' v ≠ P_act := fun he => by
              rw [he, hP_tag0] at h2; exact absurd h2 (by decide)
            have hnePl : bp.slabOf b' v ≠ P_last := fun he => by
              rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
            dsimp only [bp', bp₁, unresRemoveAt]
            rw [set1_of_ne _ _ _ _ hneP, set1_of_ne _ _ _ _ hneP]
            split_ifs with hilt
            · rw [set1_of_ne _ _ _ _ hnePl]; exact ⟨h1, h2, h3, h4⟩
            · exact ⟨h1, h2, h3, h4⟩
          slab_bwd := fun P hP htag1 => by
            dsimp only [bp', bp₁, unresRemoveAt] at hP htag1 ⊢
            have hp : P ≠ P_act := fun he => by
              rw [he, set1_self] at htag1; exact absurd htag1 (by decide)
            rw [set1_of_ne _ _ _ _ hp] at htag1 ⊢
            have hPl : P ≠ P_last := fun he => by
              rw [he, hPl_tag0] at htag1; exact absurd htag1 (by decide)
            split_ifs with hilt
            · rw [set1_of_ne _ _ _ _ hPl]; exact hv.slab_bwd P hP htag1
            · exact hv.slab_bwd P hP htag1
          act_fwd := fun b' hb' hne => by
            dsimp only [bp', bp₁, unresRemoveAt] at hb' hne ⊢
            by_cases hbe : b' = b
            · subst hbe; rw [set1_self, set1_self, set1_self]
              exact ⟨hP_lt, rfl, rfl⟩
            · rw [set1_of_ne _ _ _ _ hbe] at hne
              obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
              have hp : bp.actBlk b' ≠ P_act := fun he => by
                rw [he, hP_tag0] at h2; exact absurd h2 (by decide)
              have hPl : bp.actBlk b' ≠ P_last := fun he => by
                rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
              rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
              split_ifs with hilt
              · rw [set1_of_ne _ _ _ _ hPl]; exact ⟨h1, h2, h3⟩
              · exact ⟨h1, h2, h3⟩
          act_bwd := fun P hP htag2 => by
            dsimp only [bp', bp₁, unresRemoveAt] at hP htag2 ⊢
            by_cases hp : P = P_act
            · subst hp; rw [set1_self, set1_self, set1_self]
              exact ⟨hb, Nat.one_ne_zero, rfl⟩
            · rw [set1_of_ne _ _ _ _ hp] at htag2 ⊢
              have hPl : P ≠ P_last := fun he => by
                rw [he, hPl_tag0] at htag2; exact absurd htag2 (by decide)
              have hm1_eq : (if idx < lastIdx then set1 bp.blkMeta1 P_last idx else bp.blkMeta1) P =
                  bp.blkMeta1 P := by
                split_ifs with hilt
                · exact set1_of_ne _ _ _ _ hPl
                · rfl
              rw [hm1_eq]
              obtain ⟨h1, h2, h3⟩ := hv.act_bwd P hP htag2
              have hbe : bp.blkMeta1 P ≠ b := fun he => by rw [he, hc_nz] at h2; exact h2 rfl
              rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe]
              exact ⟨h1, h2, h3⟩
          tb_fwd := fun P hP hor => by
            dsimp only [bp', bp₁, unresRemoveAt] at hP hor ⊢
            by_cases hp : P = P_act
            · subst hp; exact hv.tb_fwd P_act hP (Or.inl hP_tag0)
            · rw [set1_of_ne _ _ _ _ hp] at hor; exact hv.tb_fwd P hP hor
          freeTb_valid := fun i hi => by
            obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
            refine ⟨h1, fun P hP hor => ?_⟩
            dsimp only [bp', bp₁, unresRemoveAt] at hP hor ⊢
            by_cases hp : P = P_act
            · subst hp; exact h2 P_act hP (Or.inl hP_tag0)
            · rw [set1_of_ne _ _ _ _ hp] at hor; exact h2 P hP hor
          freeTb_inj := hv.freeTb_inj
          tbHighWater_supply := by
            have hcard_eq : ((Finset.range (bp'.B_full + 1)).filter
                (fun P => bp'.blkTag P = 0 ∨ bp'.blkTag P = 2)).card =
                ((Finset.range (bp.B_full + 1)).filter
                  (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card :=
              congrArg Finset.card (by
                ext P; simp only [mem_filter]
                have hBf : bp'.B_full = bp.B_full := rfl
                rw [hBf]
                refine and_congr_right fun _ => ?_
                change (set1 bp.blkTag P_act 2 P = 0 ∨ set1 bp.blkTag P_act 2 P = 2) ↔ _
                by_cases hp : P = P_act
                · subst hp
                  have hPt0 : bp.blkTag P_act = 0 := hP_tag0
                  simp only [set1_self, hPt0, or_true, true_or]
                · rw [set1_of_ne _ _ _ _ hp])
            change bp.tbHighWater ≤ bp.freeTbTop + _
            rw [hcard_eq]
            exact hv.tbHighWater_supply
          tbHighWater_le_max := hv.tbHighWater_le_max
          topSwap_act_le := hv.topSwap_act_le
          topSwap_valid := fun ha => by
            obtain ⟨h1, h2, h3, h4, h5⟩ := hv.topSwap_valid ha
            have ha_bp : bp.topSwapAct = 1 := ha
            have hne_d : bp.topSwapDst ≠ P_act :=
              (hP_avoids.resolve_left (by omega)).1.symm
            dsimp only [bp', bp₁, unresRemoveAt]
            rw [set1_of_ne _ _ _ _ hne_d]
            exact ⟨h1, h2, h3, h4, h5⟩
          tail_fwd := fun b' hb' k hk_ge hk_lt => by
            dsimp only
            have hBf_eq : bp'.B_full = bp.B_full := rfl
            have hrem_eq : bp'.rem = bp.rem := rfl
            rw [hac'_eq b'] at hk_ge
            have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
            dsimp only at htf
            rw [hBf_eq, hrem_eq, show bp'.M = bp.M from rfl, show bp'.K = bp.K from rfl,
              show bp'.head = bp.head from rfl, show bp'.tailRing = bp.tailRing from rfl,
              show bp'.tbPhysBlk = bp.tbPhysBlk from rfl, show bp'.blkMeta2 = bp.blkMeta2 from rfl,
              show bp'.tailOwnerBkt = bp.tailOwnerBkt from rfl,
              show bp'.tailOwnerRing = bp.tailOwnerRing from rfl,
              show bp'.blkTag = set1 bp.blkTag P_act 2 from rfl,
              show bp'.blkMeta1 = set1 (if idx < lastIdx then set1 bp.blkMeta1 P_last idx
                else bp.blkMeta1) P_act b from rfl]
            obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
            refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
            set Pt := bp.tbPhysBlk (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K)
            by_cases hp : Pt = P_act
            · rw [hp, set1_self, set1_self, hac'_eq b,
                show bp.actCur b = 0 by unfold actCur; rw [ite_eq_left hc_nz]]
              exact Or.inr ⟨hP_lt, rfl, Nat.zero_le _⟩
            · rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
              rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
              · exact Or.inl h0
              · have hPl : Pt ≠ P_last := fun he => by
                  rw [he, hPl_tag0] at ht2; exact absurd ht2 (by decide)
                have hm1_eq : (if idx < lastIdx then set1 bp.blkMeta1 P_last idx
                    else bp.blkMeta1) Pt = bp.blkMeta1 Pt := by
                  split_ifs with hilt
                  · exact set1_of_ne _ _ _ _ hPl
                  · rfl
                rw [hm1_eq, hac'_eq]
                exact Or.inr ⟨hPlt, ht2, hge_m⟩
          tail_bwd := fun P hP_le off hoff hlt hor => by
            dsimp only
            have hBf_eq : bp'.B_full = bp.B_full := rfl
            have hrem_eq : bp'.rem = bp.rem := rfl
            rw [hBf_eq] at hP_le; rw [hBf_eq, hrem_eq] at hlt
            have hor₀ : bp.blkTag P = 0 ∨
                (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off) := by
              by_cases hp : P = P_act
              · subst hp; exact Or.inl hP_tag0
              · have hbt_p : bp'.blkTag P = bp.blkTag P := set1_of_ne _ _ _ _ hp
                have hbm1_p : bp'.blkMeta1 P =
                    (if idx < lastIdx then set1 bp.blkMeta1 P_last idx else bp.blkMeta1) P :=
                  set1_of_ne _ _ _ _ hp
                rw [hbt_p, hbm1_p] at hor
                rcases hor with h0 | ⟨h2, hge⟩
                · exact Or.inl h0
                · have hPl : P ≠ P_last := fun he => by
                    rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
                  have hm1_eq : (if idx < lastIdx then set1 bp.blkMeta1 P_last idx
                      else bp.blkMeta1) P = bp.blkMeta1 P := by
                    split_ifs with hilt
                    · exact set1_of_ne _ _ _ _ hPl
                    · rfl
                  rw [hm1_eq, hac'_eq] at hge
                  exact Or.inr ⟨h2, hge⟩
            obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt hor₀
            rw [show bp'.blkMeta2 P = bp.blkMeta2 P from rfl,
              show bp'.K = bp.K from rfl,
              show bp'.tailOwnerBkt = bp.tailOwnerBkt from rfl,
              show bp'.tailOwnerRing = bp.tailOwnerRing from rfl,
              show bp'.head = bp.head from rfl,
              show bp'.M = bp.M from rfl,
              show bp'.r = bp.r from rfl,
              show bp'.tailRing = bp.tailRing from rfl, hac'_eq]
            exact ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ }
      exact ⟨hcv', rfl, fun _ => rfl, fun b' _ loc' _ => htp_eq b' loc'⟩
    · rw [ite_eq_right hprom]
      by_cases hdem : 0 < bp.q b ∧ 2 * bp.r b ≤ 7 * bp.K
      · -- Start Demote
        rw [ite_eq_left hdem]; dsimp only
        obtain ⟨hq_pos, hr_le35⟩ := hdem
        set vp := bp.q b - 1
        have hvp_lt : vp < bp.q b := by dsimp only [vp]; omega
        obtain ⟨hP_lt, hP_tag1, hP_m1, hP_m2⟩ := hv.slab_fwd b hb vp hvp_lt
        set P_act := bp.slabOf b vp
        have hP_ne_B : P_act ≠ bp.B_full := ne_of_lt hP_lt
        set bp₁ := bp.allocTbFor P_act
        set bp' : BlockPoolState :=
          { bp₁ with
            q := set1 bp₁.q b vp
            r := set1 bp₁.r b (bp.r b + bp.K)
            head := set1 bp₁.head b ((bp.head b + 5 * bp.K) % (6 * bp.K))
            actBlk := set1 bp₁.actBlk b P_act
            actCode := set1 bp₁.actCode b (2 * bp.K)
            blkTag := set1 bp₁.blkTag P_act 2
            blkMeta1 := set1 bp₁.blkMeta1 P_act b }
        -- Helper facts about `allocTbFor`
        set tb_new := if 0 < bp.freeTbTop then bp.freeTbStack (bp.freeTbTop - 1)
          else bp.tbHighWater
        have htb_not_used : ∀ P ≤ bp.B_full, (bp.blkTag P = 0 ∨ bp.blkTag P = 2) →
            bp.blkMeta2 P ≠ tb_new := fun P hP hor => by
          dsimp only [tb_new]
          by_cases hft : 0 < bp.freeTbTop
          · rw [ite_eq_left hft]
            exact (hv.freeTb_valid (bp.freeTbTop - 1) (by omega)).2 P hP hor
          · rw [ite_eq_right hft]
            exact ne_of_lt (hv.tb_fwd P hP hor).1
        have hbp₁_m2 : bp₁.blkMeta2 = set1 bp.blkMeta2 P_act tb_new ∧
            bp₁.tbPhysBlk = set1 bp.tbPhysBlk tb_new P_act := by
          dsimp only [bp₁, tb_new]; unfold allocTbFor
          split_ifs <;> exact ⟨rfl, rfl⟩
        have hbp₁_core : bp₁.M = bp.M ∧ bp₁.K = bp.K ∧ bp₁.maxSlabs = bp.maxSlabs ∧
            bp₁.nSide = bp.nSide ∧ bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.head = bp.head ∧
            bp₁.actCode = bp.actCode ∧ bp₁.actBlk = bp.actBlk ∧ bp₁.slabOf = bp.slabOf ∧
            bp₁.tailRing = bp.tailRing ∧ bp₁.blkTag = bp.blkTag ∧ bp₁.blkMeta1 = bp.blkMeta1 ∧
            bp₁.unresLen = bp.unresLen ∧ bp₁.unresStack = bp.unresStack ∧
            bp₁.tailOwnerBkt = bp.tailOwnerBkt ∧ bp₁.tailOwnerRing = bp.tailOwnerRing ∧
            bp₁.topSwapAct = bp.topSwapAct ∧ bp₁.topSwapSrc = bp.topSwapSrc ∧
            bp₁.topSwapDst = bp.topSwapDst ∧ bp₁.topSwapCur = bp.topSwapCur := by
          dsimp only [bp₁]; unfold allocTbFor; split_ifs <;>
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨hM₁, hK₁, hms₁, hn₁, hq₁, hr₁, hhd₁, hac₁, hab₁, hsl₁, htr₁, hbt₁, hbm1₁,
          hul₁, hus₁, htob₁, htor₁, htsa₁, htss₁, htsd₁, htsc₁⟩ := hbp₁_core
        have hac'_b : bp'.actCur b = bp.K := by
          unfold actCur
          have hc' : bp'.actCode b = 2 * bp.K := set1_self _ _ _
          have hk' : bp'.K = bp.K := hK₁
          rw [hc', hk', ite_eq_right (by omega), ite_eq_right (by omega)]
          omega
        have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
          unfold actCur
          have hc' : bp'.actCode b' = bp.actCode b' :=
            (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b')
          have hk' : bp'.K = bp.K := hK₁
          rw [hc', hk']
        have hbc_eq : ∀ b', bp'.bktCount b' = bp.bktCount b' := fun b' => by
          unfold bktCount; dsimp only [bp']
          rw [hK₁, hq₁, hr₁]
          by_cases hbe : b' = b
          · subst b'; rw [set1_self, set1_self]
            have hq_re : bp.q b * bp.K = vp * bp.K + bp.K := by
              have hq1 : bp.q b = vp + 1 := by dsimp only [vp]; omega
              rw [hq1, Nat.add_one_mul]
            omega
          · rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe]
        have hpt_live_eq : ∀ b' < bp.M, ∀ k, bp.actCur b' ≤ k → k < bp.r b' →
            bp'.physOfTail (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))) =
              bp.physOfTail (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))) :=
          fun b' hb' k hk_ge hk_lt => by
            have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
            dsimp only at htf
            obtain ⟨_, hP_le, hm2_eq, hkind, _, _⟩ := htf
            have hne_tb : bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K ≠ tb_new := by
              rw [← hm2_eq]
              exact htb_not_used _ hP_le
                (hkind.imp And.left (fun h => h.2.1))
            unfold physOfTail
            have heff_eq : ∀ E o, bp'.effBlk E o = bp.effBlk E o := by
              intro E o; unfold effBlk
              have ha' : bp'.topSwapAct = bp.topSwapAct := htsa₁
              have hc' : bp'.topSwapCur = bp.topSwapCur := htsc₁
              have hs' : bp'.topSwapSrc = bp.topSwapSrc := htss₁
              have hd' : bp'.topSwapDst = bp.topSwapDst := htsd₁
              rw [ha', hc', hs', hd']
            have hK' : bp'.K = bp.K := hK₁
            have htpb' : bp'.tbPhysBlk = set1 bp.tbPhysBlk tb_new P_act := hbp₁_m2.2
            rw [hK', htpb', set1_of_ne _ _ _ _ hne_tb, heff_eq]
        have htp_lt : ∀ b' loc', b' < bp.M → loc' < bp.bktCount b' →
            bp'.toPhys b' loc' = bp.toPhys b' loc' := fun b' loc' hb' hloc' => by
          have heff_eq : ∀ E o, bp'.effBlk E o = bp.effBlk E o := by
            intro E o; unfold effBlk
            have ha' : bp'.topSwapAct = bp.topSwapAct := htsa₁
            have hc' : bp'.topSwapCur = bp.topSwapCur := htsc₁
            have hs' : bp'.topSwapSrc = bp.topSwapSrc := htss₁
            have hd' : bp'.topSwapDst = bp.topSwapDst := htsd₁
            rw [ha', hc', hs', hd']
          have hK' : bp'.K = bp.K := hK₁
          have hsl' : bp'.slabOf = bp.slabOf := hsl₁
          have htr' : bp'.tailRing = bp.tailRing := htr₁
          by_cases hbe : b' = b
          · subst b'
            have hq' : bp'.q b = vp := set1_self _ _ _
            have hab' : bp'.actBlk b = P_act := set1_self _ _ _
            have hhd' : bp'.head b = (bp.head b + 5 * bp.K) % (6 * bp.K) := set1_self _ _ _
            unfold toPhys
            rw [hq', hK', hsl', hac'_b, hab', htr', hhd']
            simp only [heff_eq]
            have hac0 : bp.actCur b = 0 := by unfold actCur; rw [ite_eq_left hc_nz]
            rw [hac0]
            by_cases hslab' : loc' < vp * bp.K
            · have hslab : loc' < bp.q b * bp.K :=
                hslab'.trans_le (Nat.mul_le_mul_right _ hvp_lt.le)
              rw [ite_eq_left hslab', ite_eq_left hslab]
            · rw [ite_eq_right hslab']
              by_cases hslab : loc' < bp.q b * bp.K
              · rw [ite_eq_left hslab]
                have hq_re : bp.q b * bp.K = vp * bp.K + bp.K := by
                  have hq1 : bp.q b = vp + 1 := by dsimp only [vp]; omega
                  rw [hq1, Nat.add_one_mul]
                have hlt_K : loc' - vp * bp.K < bp.K := by omega
                rw [ite_eq_left hlt_K]
                have hdiv_vp : loc' / bp.K = vp := by
                  apply le_antisymm
                  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hK).mpr
                      (by rw [Nat.add_one_mul, ← hq_re]; exact hslab))
                  · exact (Nat.le_div_iff_mul_le hK).mpr (Nat.le_of_not_lt hslab')
                have hmod_vp : loc' % bp.K = loc' - vp * bp.K := by
                  have h := Nat.div_add_mod loc' bp.K
                  rw [hdiv_vp, Nat.mul_comm] at h; omega
                rw [hdiv_vp, hmod_vp]
              · rw [ite_eq_right hslab, ite_eq_right (Nat.not_lt_zero _)]
                have hq_re : bp.q b * bp.K = vp * bp.K + bp.K := by
                  have hq1 : bp.q b = vp + 1 := by dsimp only [vp]; omega
                  rw [hq1, Nat.add_one_mul]
                have hge_K : bp.K ≤ loc' - vp * bp.K := by omega
                rw [ite_eq_right (not_lt.mpr hge_K)]
                have hsub_re : loc' - vp * bp.K = bp.K + (loc' - bp.q b * bp.K) := by omega
                rw [hsub_re, head_demote_add_mod]
                have hk_lt_r : loc' - bp.q b * bp.K < bp.r b := by unfold bktCount at hloc'; omega
                exact hpt_live_eq b hb (loc' - bp.q b * bp.K)
                  (by rw [hac0]; exact Nat.zero_le _) hk_lt_r
          · have hq' : bp'.q b' = bp.q b' := (set1_of_ne _ _ _ _ hbe).trans (congrFun hq₁ b')
            have hab' : bp'.actBlk b' = bp.actBlk b' :=
              (set1_of_ne _ _ _ _ hbe).trans (congrFun hab₁ b')
            have hhd' : bp'.head b' = bp.head b' :=
              (set1_of_ne _ _ _ _ hbe).trans (congrFun hhd₁ b')
            unfold toPhys
            rw [hq', hK', hsl', hac'_ne b' hbe, hab', htr', hhd']
            simp only [heff_eq]
            by_cases hslab : loc' < bp.q b' * bp.K
            · rw [ite_eq_left hslab, ite_eq_left hslab]
            · rw [ite_eq_right hslab, ite_eq_right hslab]
              set k := loc' - bp.q b' * bp.K
              by_cases hact : k < bp.actCur b'
              · rw [ite_eq_left hact, ite_eq_left hact]
              · rw [ite_eq_right hact, ite_eq_right hact]
                have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
                exact hpt_live_eq b' hb' k (Nat.le_of_not_lt hact) hk_lt_r
        have hcv' : bp'.CoreValid :=
          { M_pos := by dsimp only [bp']; rw [hM₁]; exact hv.M_pos
            K_ge := by dsimp only [bp']; rw [hK₁]; exact hv.K_ge
            bkt_bounds := fun b' hb' => by
              rw [show bp'.M = bp.M from hM₁] at hb'
              by_cases hbe : b' = b
              · subst b'; rw [hac'_b]
                dsimp only [bp']; rw [hms₁, hK₁, set1_self, set1_self, set1_self, set1_self]
                exact ⟨by omega, by omega, Nat.mod_lt _ (by omega), le_rfl, by omega⟩
              · rw [hac'_ne b' hbe]
                dsimp only [bp']
                rw [hms₁, hK₁, set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe,
                  set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe, hq₁, hr₁, hhd₁, hac₁]
                exact hv.bkt_bounds b' hb'
            blkTag_lt := fun P hP => by
              dsimp only [bp', B_full] at hP ⊢
              rw [hn₁, hK₁] at hP; rw [hbt₁]
              by_cases hp : P = P_act
              · subst hp; rw [set1_self]; decide
              · rw [set1_of_ne _ _ _ _ hp]; exact hv.blkTag_lt P hP
            blkTag_top := by
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              rw [hBf_eq]; dsimp only [bp']; rw [hbt₁, set1_of_ne _ _ _ _ hP_ne_B.symm]
              exact hv.blkTag_top
            unres_fwd := fun i hi => by
              dsimp only [bp', B_full] at hi ⊢
              rw [hul₁] at hi; rw [hus₁, hn₁, hK₁, hbt₁, hbm1₁]
              obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i hi
              have hp : bp.unresStack i ≠ P_act := fun he => by
                rw [he, hP_tag1] at h2; exact absurd h2 (by decide)
              rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
              exact ⟨h1, h2, h3⟩
            unres_bwd := fun P hP htag0 => by
              dsimp only [bp', B_full] at hP htag0 ⊢
              rw [hn₁, hK₁] at hP; rw [hbt₁] at htag0; rw [hbm1₁, hul₁, hus₁]
              have hp : P ≠ P_act := fun he => by
                rw [he, set1_self] at htag0; exact absurd htag0 (by decide)
              rw [set1_of_ne _ _ _ _ hp] at htag0 ⊢
              exact hv.unres_bwd P hP htag0
            slab_fwd := fun b' hb' v hv_lt => by
              dsimp only [bp', B_full] at hb' hv_lt ⊢
              rw [hM₁] at hb'; rw [hsl₁, hn₁, hK₁, hbt₁, hbm1₁, hbp₁_m2.1]
              by_cases hbe : b' = b
              · subst b'; rw [set1_self] at hv_lt
                have hv_lt_old : v < bp.q b := hv_lt.trans hvp_lt
                obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b hb v hv_lt_old
                have hp : bp.slabOf b v ≠ P_act := fun he => by
                  rw [he, hP_m2] at h4; exact (ne_of_lt hv_lt) h4.symm
                rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                exact ⟨h1, h2, h3, h4⟩
              · rw [set1_of_ne _ _ _ _ hbe, hq₁] at hv_lt
                obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
                have hp : bp.slabOf b' v ≠ P_act := fun he => by
                  rw [he, hP_m1] at h3; exact hbe h3.symm
                rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                exact ⟨h1, h2, h3, h4⟩
            slab_bwd := fun P hP htag1 => by
              dsimp only [bp', B_full] at hP htag1 ⊢
              rw [hn₁, hK₁] at hP; rw [hbt₁] at htag1
              have hp : P ≠ P_act := fun he => by
                rw [he, set1_self] at htag1; exact absurd htag1 (by decide)
              rw [set1_of_ne _ _ _ _ hp] at htag1
              obtain ⟨h1, h2, h3⟩ := hv.slab_bwd P hP htag1
              rw [hbm1₁, hM₁, hbp₁_m2.1, hsl₁, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
              by_cases hbe : bp.blkMeta1 P = b
              · rw [hbe, set1_self]; rw [hbe] at h2 h3
                have hne_vp : bp.blkMeta2 P ≠ vp := fun he => by
                  rw [he] at h3; exact hp h3.symm
                exact ⟨hb, by dsimp only [vp] at hne_vp ⊢; omega, h3⟩
              · rw [set1_of_ne _ _ _ _ hbe, hq₁]; exact ⟨h1, h2, h3⟩
            act_fwd := fun b' hb' hne => by
              dsimp only [bp', B_full] at hb' hne ⊢
              rw [hM₁] at hb'; rw [hn₁, hK₁, hbt₁, hbm1₁]
              by_cases hbe : b' = b
              · subst b'; rw [set1_self, set1_self, set1_self]
                exact ⟨hP_lt, rfl, rfl⟩
              · rw [set1_of_ne _ _ _ _ hbe, hac₁] at hne
                obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
                have hp : bp.actBlk b' ≠ P_act := fun he => by
                  rw [he, hP_tag1] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hbe, hab₁, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                exact ⟨h1, h2, h3⟩
            act_bwd := fun P hP htag2 => by
              dsimp only [bp', B_full] at hP htag2 ⊢
              rw [hn₁, hK₁] at hP; rw [hbt₁] at htag2; rw [hM₁, hbm1₁]
              by_cases hp : P = P_act
              · subst hp; rw [set1_self, set1_self, set1_self]
                exact ⟨hb, by omega, rfl⟩
              · rw [set1_of_ne _ _ _ _ hp] at htag2 ⊢
                obtain ⟨h1, h2, h3⟩ := hv.act_bwd P hP htag2
                have hbe : bp.blkMeta1 P ≠ b := fun he => by rw [he, hc_nz] at h2; exact h2 rfl
                rw [set1_of_ne _ _ _ _ hbe, set1_of_ne _ _ _ _ hbe, hac₁, hab₁]
                exact ⟨h1, h2, h3⟩
            tb_fwd := fun P hP hor => by
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              rw [hBf_eq] at hP
              dsimp only [bp'] at hor ⊢
              rw [hbt₁] at hor
              rw [hbp₁_m2.1, hbp₁_m2.2]
              by_cases hp : P = P_act
              · subst hp; rw [set1_self, set1_self]
                refine ⟨?_, rfl⟩
                dsimp only [bp₁, allocTbFor, tb_new]
                by_cases hft : 0 < bp.freeTbTop
                · rw [ite_eq_left hft, ite_eq_left hft]; dsimp only
                  exact (hv.freeTb_valid (bp.freeTbTop - 1) (by omega)).1
                · rw [ite_eq_right hft, ite_eq_right hft]; dsimp only; omega
              · rw [set1_of_ne _ _ _ _ hp] at hor ⊢
                obtain ⟨h1, h2⟩ := hv.tb_fwd P hP hor
                have hne_tb := htb_not_used P hP hor
                rw [set1_of_ne _ _ _ _ hne_tb]
                refine ⟨?_, h2⟩
                dsimp only [bp₁, allocTbFor]
                split_ifs <;> dsimp only <;> omega
            freeTb_valid := fun i hi => by
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              rw [hBf_eq]
              dsimp only [bp', bp₁, allocTbFor] at hi ⊢
              by_cases hft : 0 < bp.freeTbTop
              · simp only [hft, ↓reduceIte] at hi ⊢
                obtain ⟨h1, h2⟩ := hv.freeTb_valid i (by omega)
                refine ⟨h1, fun P hP hor => ?_⟩
                by_cases hp : P = P_act
                · subst hp; rw [set1_self]
                  intro heq
                  exact absurd (hv.freeTb_inj i (by omega) (bp.freeTbTop - 1) (by omega) heq.symm)
                    (ne_of_lt hi)
                · rw [set1_of_ne _ _ _ _ hp] at hor ⊢; exact h2 P hP hor
              · simp only [hft, ↓reduceIte] at hi
                omega
            freeTb_inj := fun i hi j hj heq => by
              dsimp only [bp', bp₁, allocTbFor] at hi hj heq ⊢
              by_cases hft : 0 < bp.freeTbTop
              · simp only [hft, ↓reduceIte] at hi hj heq
                exact hv.freeTb_inj i (by omega) j (by omega) heq
              · simp only [hft, ↓reduceIte] at hi
                omega
            tbHighWater_supply := by
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              rw [hBf_eq]
              have hcard := filter_tail_card_insert (N := bp.B_full + 1) (P₀ := P_act)
                (t₁ := bp.blkTag) (t₂ := set1 bp.blkTag P_act 2)
                (by omega) (by rw [hP_tag1]; decide) (by rw [set1_self]; decide)
                (fun P _ hp => by rw [set1_of_ne _ _ _ _ hp])
              have hsup := hv.tbHighWater_supply
              dsimp only [bp', bp₁, allocTbFor]
              by_cases hft : 0 < bp.freeTbTop
              · simp only [hft, ↓reduceIte]; omega
              · simp only [hft, ↓reduceIte]; omega
            tbHighWater_le_max := by
              dsimp only [bp', bp₁, allocTbFor]
              by_cases hft : 0 < bp.freeTbTop
              · simp only [hft, ↓reduceIte]; exact hv.tbHighWater_le_max
              · simp only [hft, ↓reduceIte]
                have hft0 : bp.freeTbTop = 0 := by omega
                have hsup := hv.tbHighWater_supply
                rw [hft0, zero_add] at hsup
                obtain ⟨hcard_eq, hlt_8M⟩ := hv.tail_block_card_lt
                rw [hcard_eq] at hsup; omega
            topSwap_act_le := by dsimp only [bp']; rw [htsa₁]; exact hv.topSwap_act_le
            topSwap_valid := fun ha => by
              dsimp only [bp', B_full] at ha ⊢
              rw [htsa₁] at ha
              obtain ⟨h1, h2, h3, h4, h5⟩ := hv.topSwap_valid ha
              have hne_d : bp.topSwapDst ≠ P_act := fun he => by
                rw [he, hP_tag1] at h4; exact absurd h4 (by decide)
              rw [htsc₁, hK₁, htss₁, htsd₁, hn₁, hbt₁, set1_of_ne _ _ _ _ hne_d]
              exact ⟨h1, h2, h3, h4, h5⟩
            tail_fwd := fun b' hb' k hk_ge hk_lt => by
              dsimp only
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              have hrem_eq : bp'.rem = bp.rem := by dsimp only [bp', rem]; rw [hn₁, hK₁]
              rw [hBf_eq, hrem_eq]
              rw [show bp'.M = bp.M from hM₁] at hb'
              rw [show bp'.r = set1 bp₁.r b (bp.r b + bp.K) from rfl] at hk_lt
              rw [show bp'.M = bp.M from hM₁, show bp'.K = bp.K from hK₁,
                show bp'.tailRing = bp.tailRing from htr₁,
                show bp'.tbPhysBlk = set1 bp.tbPhysBlk tb_new P_act from hbp₁_m2.2,
                show bp'.blkMeta2 = set1 bp.blkMeta2 P_act tb_new from hbp₁_m2.1,
                show bp'.blkTag = set1 bp.blkTag P_act 2 from congrArg (set1 · P_act 2) hbt₁,
                show bp'.blkMeta1 = set1 bp.blkMeta1 P_act b from congrArg (set1 · P_act b) hbm1₁,
                show bp'.tailOwnerBkt = bp.tailOwnerBkt from htob₁,
                show bp'.tailOwnerRing = bp.tailOwnerRing from htor₁,
                show bp'.head = set1 bp₁.head b ((bp.head b + 5 * bp.K) % (6 * bp.K)) from rfl]
              by_cases hbe : b' = b
              · subst b'
                rw [hac'_b] at hk_ge
                rw [set1_self] at hk_lt
                rw [set1_self]
                set k₀ := k - bp.K
                have hk_re : k = bp.K + k₀ := by dsimp only [k₀]; omega
                have hk₀_lt : k₀ < bp.r b := by dsimp only [k₀]; omega
                have hac0 : bp.actCur b = 0 := by unfold actCur; rw [ite_eq_left hc_nz]
                rw [hk_re, head_demote_add_mod]
                have htf := hv.tail_fwd b hb k₀ (by rw [hac0]; exact Nat.zero_le _) hk₀_lt
                dsimp only at htf
                obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                set t' := bp.tailRing b ((bp.head b + k₀) % (6 * bp.K))
                have hne_tb : t' / bp.K ≠ tb_new := by
                  rw [← hc_m2]; exact htb_not_used _ hb_le (hkind.imp And.left (fun h => h.2.1))
                rw [set1_of_ne _ _ _ _ hne_tb]
                have hp : bp.tbPhysBlk (t' / bp.K) ≠ P_act := fun he => by
                  rcases hkind with ⟨ht0, _⟩ | ⟨_, ht2, _⟩
                  · rw [he, hP_tag1] at ht0; exact absurd ht0 (by decide)
                  · rw [he, hP_tag1] at ht2; exact absurd ht2 (by decide)
                rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                · exact Or.inl h0
                · have hbe2 : bp.blkMeta1 (bp.tbPhysBlk (t' / bp.K)) ≠ b := fun he2 => by
                    have hne_c := (hv.act_bwd _ hPlt ht2).2.1
                    rw [he2, hc_nz] at hne_c; exact hne_c rfl
                  rw [hac'_ne _ hbe2]
                  exact Or.inr ⟨hPlt, ht2, hge_m⟩
              · rw [hac'_ne b' hbe] at hk_ge
                rw [set1_of_ne _ _ _ _ hbe, hr₁] at hk_lt
                rw [set1_of_ne _ _ _ _ hbe, hhd₁]
                have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
                dsimp only at htf
                obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
                set t' := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
                have hne_tb : t' / bp.K ≠ tb_new := by
                  rw [← hc_m2]; exact htb_not_used _ hb_le (hkind.imp And.left (fun h => h.2.1))
                rw [set1_of_ne _ _ _ _ hne_tb]
                have hp : bp.tbPhysBlk (t' / bp.K) ≠ P_act := fun he => by
                  rcases hkind with ⟨ht0, _⟩ | ⟨_, ht2, _⟩
                  · rw [he, hP_tag1] at ht0; exact absurd ht0 (by decide)
                  · rw [he, hP_tag1] at ht2; exact absurd ht2 (by decide)
                rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
                refine ⟨ha, hb_le, hc_m2, ?_, hob, hor⟩
                rcases hkind with h0 | ⟨hPlt, ht2, hge_m⟩
                · exact Or.inl h0
                · have hbe2 : bp.blkMeta1 (bp.tbPhysBlk (t' / bp.K)) ≠ b := fun he2 => by
                    have hne_c := (hv.act_bwd _ hPlt ht2).2.1
                    rw [he2, hc_nz] at hne_c; exact hne_c rfl
                  rw [hac'_ne _ hbe2]
                  exact Or.inr ⟨hPlt, ht2, hge_m⟩
            tail_bwd := fun P hP_le off hoff hlt hor => by
              dsimp only
              have hBf_eq : bp'.B_full = bp.B_full := by dsimp only [bp', B_full]; rw [hn₁, hK₁]
              have hrem_eq : bp'.rem = bp.rem := by dsimp only [bp', rem]; rw [hn₁, hK₁]
              rw [hBf_eq] at hP_le; rw [hBf_eq, hrem_eq] at hlt
              rw [show bp'.K = bp.K from hK₁] at hoff
              have hp : P ≠ P_act := fun he => by
                rw [he] at hor
                have hbt' : bp'.blkTag P_act = 2 := set1_self _ _ _
                have hbm1' : bp'.blkMeta1 P_act = b := set1_self _ _ _
                rw [hbt', hbm1', hac'_b] at hor
                rcases hor with h0 | ⟨_, hge⟩
                · exact absurd h0 (by decide)
                · omega
              have hor₀ : bp.blkTag P = 0 ∨
                  (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off) := by
                have hbt' : bp'.blkTag P = bp.blkTag P :=
                  (set1_of_ne _ _ _ _ hp).trans (congrFun hbt₁ P)
                have hbm1' : bp'.blkMeta1 P = bp.blkMeta1 P :=
                  (set1_of_ne _ _ _ _ hp).trans (congrFun hbm1₁ P)
                rw [hbt', hbm1'] at hor
                rcases hor with h0 | ⟨h2, hge⟩
                · exact Or.inl h0
                · have hP_lt' : P < bp.B_full := by
                    rcases hlt with h1 | _
                    · exact h1
                    · by_contra hgeB
                      have heqB : P = bp.B_full := by omega
                      rw [heqB, hv.blkTag_top] at h2; exact absurd h2 (by decide)
                  have hbe2 : bp.blkMeta1 P ≠ b := fun he2 => by
                    have hne_c := (hv.act_bwd P hP_lt' h2).2.1
                    rw [he2, hc_nz] at hne_c; exact hne_c rfl
                  rw [hac'_ne _ hbe2] at hge
                  exact Or.inr ⟨h2, hge⟩
              obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt hor₀
              have hm2' : bp'.blkMeta2 P = bp.blkMeta2 P := by
                rw [show bp'.blkMeta2 = bp₁.blkMeta2 from rfl, hbp₁_m2.1, set1_of_ne _ _ _ _ hp]
              rw [show bp'.M = bp.M from hM₁, show bp'.K = bp.K from hK₁, hm2',
                show bp'.tailOwnerBkt = bp.tailOwnerBkt from htob₁,
                show bp'.tailOwnerRing = bp.tailOwnerRing from htor₁,
                show bp'.tailRing = bp.tailRing from htr₁]
              set t := bp.blkMeta2 P * bp.K + off
              by_cases hbe : bp.tailOwnerBkt t = b
              · have hhd_b : bp'.head b = (bp.head b + 5 * bp.K) % (6 * bp.K) := set1_self _ _ _
                have hr_b : bp'.r b = bp.r b + bp.K := set1_self _ _ _
                rw [hbe, hhd_b, hr_b, hac'_b]
                rw [hbe] at hk_ge hk_lt htr
                set k₀ := (bp.tailOwnerRing t + 6 * bp.K - bp.head b) % (6 * bp.K)
                have hk₀_lt5 : k₀ < 5 * bp.K := by omega
                have hk_new := add_sub_demote_head_mod hK hhd_lt hrko hk₀_lt5 (rfl : k₀ = k₀)
                rw [hk_new]
                exact ⟨hb, hrko, by omega, by omega, htr⟩
              · have hhd_o : bp'.head (bp.tailOwnerBkt t) = bp.head (bp.tailOwnerBkt t) :=
                  (set1_of_ne _ _ _ _ hbe).trans (congrFun hhd₁ _)
                have hr_o : bp'.r (bp.tailOwnerBkt t) = bp.r (bp.tailOwnerBkt t) :=
                  (set1_of_ne _ _ _ _ hbe).trans (congrFun hr₁ _)
                rw [hhd_o, hr_o, hac'_ne _ hbe]
                exact ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ }
        exact ⟨hcv', hn₁, hbc_eq, fun b' hb' loc' hloc' => htp_lt b' loc' hb' hloc'⟩
      · rw [ite_eq_right hdem]
        exact ⟨hv, rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- Key 1-offset physical swap identity for advancing `topSwapCur` from `cur` to `cur + 1`. -/
private theorem topSwap_step_apply {α : Type*} {bp : BlockPoolState}
    (hact : bp.topSwapAct = 1) (hK : 0 < bp.K) (hcur : bp.topSwapCur < bp.K)
    (_hSD : bp.topSwapSrc ≠ bp.topSwapDst)
    (arr : ℕ → α) (P off : ℕ) (hoff : off < bp.K) :
    let sw : PhysSwap := ⟨bp.topSwapSrc * bp.K + bp.topSwapCur,
      bp.topSwapDst * bp.K + bp.topSwapCur⟩
    let bp_next := { bp with topSwapCur := bp.topSwapCur + 1 }
    sw.apply arr (bp_next.effBlk P off * bp.K + off) =
      arr (bp.effBlk P off * bp.K + off) := by
  dsimp only
  set S := bp.topSwapSrc
  set D := bp.topSwapDst
  set cur := bp.topSwapCur
  set sw : PhysSwap := ⟨S * bp.K + cur, D * bp.K + cur⟩
  have slot_ne_of_off : off ≠ cur → ∀ E, E * bp.K + off ≠ S * bp.K + cur ∧
      E * bp.K + off ≠ D * bp.K + cur := fun hne E => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hm := congrArg (· % bp.K) h
      simp only [Nat.add_comm _ off, Nat.add_comm _ cur, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hcur] at hm
      exact hne hm
    · have hm := congrArg (· % bp.K) h
      simp only [Nat.add_comm _ off, Nat.add_comm _ cur, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hcur] at hm
      exact hne hm
  by_cases hoe : off = cur
  · subst hoe
    unfold effBlk; dsimp only
    have hc_old : ¬(bp.topSwapAct = 1 ∧ cur < cur) := fun h => Nat.lt_irrefl _ h.2
    have hc_new : bp.topSwapAct = 1 ∧ cur < cur + 1 := ⟨hact, Nat.lt_succ_self cur⟩
    rw [ite_eq_right hc_old, ite_eq_left hc_new]
    by_cases hs : P = S
    · subst hs; rw [ite_eq_left rfl, PhysSwap.apply_p₂]
    · rw [ite_eq_right hs]
      by_cases hd : P = D
      · subst hd; rw [ite_eq_left rfl, PhysSwap.apply_p₁]
      · rw [ite_eq_right hd]
        have h1 : P * bp.K + cur ≠ S * bp.K + cur := fun h => by
          have hd1 := congrArg (· / bp.K) h
          simp only [Nat.add_comm _ cur, Nat.add_mul_div_right _ _ hK,
            Nat.div_eq_of_lt hcur, zero_add] at hd1
          exact hs hd1
        have h2 : P * bp.K + cur ≠ D * bp.K + cur := fun h => by
          have hd1 := congrArg (· / bp.K) h
          simp only [Nat.add_comm _ cur, Nat.add_mul_div_right _ _ hK,
            Nat.div_eq_of_lt hcur, zero_add] at hd1
          exact hd hd1
        exact PhysSwap.apply_of_ne sw arr h1 h2
  · have heff_eq : ({ bp with topSwapCur := cur + 1 } : BlockPoolState).effBlk P off =
        bp.effBlk P off := by
      unfold effBlk
      have ha' : ({ bp with topSwapCur := cur + 1 } : BlockPoolState).topSwapAct =
          bp.topSwapAct := rfl
      have hc' : ({ bp with topSwapCur := cur + 1 } : BlockPoolState).topSwapCur = cur + 1 := rfl
      have hs' : ({ bp with topSwapCur := cur + 1 } : BlockPoolState).topSwapSrc = S := rfl
      have hd' : ({ bp with topSwapCur := cur + 1 } : BlockPoolState).topSwapDst = D := rfl
      rw [ha', hc', hs', hd']
      by_cases hlt : off < cur
      · have hc1 : bp.topSwapAct = 1 ∧ off < cur + 1 := ⟨hact, Nat.lt_succ_of_lt hlt⟩
        have hc2 : bp.topSwapAct = 1 ∧ off < cur := ⟨hact, hlt⟩
        rw [ite_eq_left hc1, ite_eq_left hc2]
      · have hn1 : ¬(bp.topSwapAct = 1 ∧ off < cur + 1) := fun h => by omega
        have hn2 : ¬(bp.topSwapAct = 1 ∧ off < cur) := fun h => hlt h.2
        rw [ite_eq_right hn1, ite_eq_right hn2]
    rw [heff_eq]
    obtain ⟨h1, h2⟩ := slot_ne_of_off hoe (bp.effBlk P off)
    exact PhysSwap.apply_of_ne sw arr h1 h2

private theorem CoreValid.topSwap_mid_toPhys {α : Type*} {bp : BlockPoolState} (hv : bp.CoreValid)
    (ha1 : bp.topSwapAct = 1) (arr : ℕ → α) {b' loc' : ℕ}
    (hb' : b' < bp.M) (_hloc' : loc' < bp.bktCount b') :
    (PhysSwap.mk (bp.topSwapSrc * bp.K + bp.topSwapCur)
      (bp.topSwapDst * bp.K + bp.topSwapCur)).apply arr
      (({ bp with topSwapCur := bp.topSwapCur + 1 } : BlockPoolState).toPhys b' loc') =
      arr (bp.toPhys b' loc') := by
  have hK := hv.K_pos
  obtain ⟨hcur_lt, _, _, _, hSD⟩ := hv.topSwap_valid ha1
  set bp_n : BlockPoolState := { bp with topSwapCur := bp.topSwapCur + 1 }
  unfold toPhys
  rw [show bp_n.K = bp.K from rfl, show bp_n.q = bp.q from rfl,
    show bp_n.slabOf = bp.slabOf from rfl,
    show bp_n.actCur b' = bp.actCur b' from rfl,
    show bp_n.actBlk = bp.actBlk from rfl,
    show bp_n.tailRing = bp.tailRing from rfl,
    show bp_n.head = bp.head from rfl]
  by_cases hslab : loc' < bp.q b' * bp.K
  · rw [ite_eq_left hslab, ite_eq_left hslab]
    exact topSwap_step_apply ha1 hK hcur_lt hSD arr _ (loc' % bp.K) (Nat.mod_lt loc' hK)
  · rw [ite_eq_right hslab, ite_eq_right hslab]
    set k := loc' - bp.q b' * bp.K
    by_cases hact_k : k < bp.actCur b'
    · rw [ite_eq_left hact_k, ite_eq_left hact_k]
      obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b' hb'
      exact topSwap_step_apply ha1 hK hcur_lt hSD arr _ k (hact_k.trans_le (actCur_le_K hc_le))
    · rw [ite_eq_right hact_k, ite_eq_right hact_k]
      unfold physOfTail
      rw [show bp_n.K = bp.K from rfl, show bp_n.tbPhysBlk = bp.tbPhysBlk from rfl]
      set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
      exact topSwap_step_apply ha1 hK hcur_lt hSD arr _ (t % bp.K) (Nat.mod_lt t hK)

/-- `commitTopSwap` (called when `topSwapAct = 1` and `topSwapCur + 1 = K`) produces a `CoreValid`
state whose `toPhys` agrees pointwise with `{ bp with topSwapCur := bp.K }`. -/
private theorem CoreValid.commitTopSwap_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    (hact : bp.topSwapAct = 1) :
    let bp_mid : BlockPoolState := { bp with topSwapCur := bp.K }
    let bp' := bp.commitTopSwap
    bp'.CoreValid ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp'.toPhys b' loc' = bp_mid.toPhys b' loc') := by
  have hK := hv.K_pos
  obtain ⟨hcur_lt, hS_lt, hD_lt, hD_tag0, hSD⟩ := hv.topSwap_valid hact
  set S := bp.topSwapSrc
  set D := bp.topSwapDst
  obtain ⟨hposD_lt, hposD_eq⟩ := hv.unres_bwd D hD_lt hD_tag0
  obtain ⟨htbD_lt, htbD_eq⟩ := hv.tb_fwd D hD_lt.le (Or.inl hD_tag0)
  set bp_mid : BlockPoolState := { bp with topSwapCur := bp.K }
  have hmid_eff : ∀ P off, off < bp.K →
      bp_mid.effBlk P off = if P = S then D else if P = D then S else P := fun P off hoff => by
    unfold effBlk
    have ha_m : bp_mid.topSwapAct = bp.topSwapAct := rfl
    have hc_m : bp_mid.topSwapCur = bp.K := rfl
    have hs_m : bp_mid.topSwapSrc = S := rfl
    have hd_m : bp_mid.topSwapDst = D := rfl
    rw [ha_m, hc_m, hs_m, hd_m, ite_eq_left ⟨hact, hoff⟩]
  have hS_ne_B : S ≠ bp.B_full := ne_of_lt hS_lt
  have hD_ne_B : D ≠ bp.B_full := ne_of_lt hD_lt
  have htagS_lt3 := hv.blkTag_lt S hS_lt
  -- Split on `bp.blkTag S ∈ {0, 1, 2}`
  by_cases htagS0 : bp.blkTag S = 0
  · obtain ⟨hposS_lt, hposS_eq⟩ := hv.unres_bwd S hS_lt htagS0
    obtain ⟨htbS_lt, htbS_eq⟩ := hv.tb_fwd S hS_lt.le (Or.inl htagS0)
    have hpos_ne : bp.blkMeta1 S ≠ bp.blkMeta1 D := fun he => by
      have h := congrArg bp.unresStack he; rw [hposS_eq, hposD_eq] at h; exact hSD h
    have htb_ne : bp.blkMeta2 S ≠ bp.blkMeta2 D := fun he => by
      have h := congrArg bp.tbPhysBlk he; rw [htbS_eq, htbD_eq] at h; exact hSD h
    set bp' := bp.commitTopSwap
    have hbp'_def : bp' =
        { bp with
          topSwapAct := 0
          topSwapCur := 0
          blkTag := set1 (set1 bp.blkTag S 0) D 0
          blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S)
          blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S)
          unresStack := set1 (set1 bp.unresStack (bp.blkMeta1 D) S) (bp.blkMeta1 S) D
          tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D } := by
      dsimp only [bp']; unfold commitTopSwap; dsimp only; rw [ite_eq_left htagS0, htagS0]
    have htag_eq : set1 (set1 bp.blkTag S 0) D 0 = bp.blkTag := by
      ext P
      by_cases pd : P = D
      · subst pd; rw [set1_self, hD_tag0]
      · rw [set1_of_ne _ _ _ _ pd]
        by_cases ps : P = S
        · subst ps; rw [set1_self, htagS0]
        · rw [set1_of_ne _ _ _ _ ps]
    have htp_eq : ∀ b' < bp.M, ∀ loc' < bp.bktCount b',
        bp'.toPhys b' loc' = bp_mid.toPhys b' loc' := fun b' hb' loc' hloc' => by
      rw [hbp'_def]
      set bp₀ : BlockPoolState :=
        { bp with
          topSwapAct := 0, topSwapCur := 0,
          blkTag := set1 (set1 bp.blkTag S 0) D 0,
          blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
          blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
          unresStack := set1 (set1 bp.unresStack (bp.blkMeta1 D) S) (bp.blkMeta1 S) D,
          tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D }
      have heff0 : ∀ E o, bp₀.effBlk E o = E := fun E o => by
        unfold effBlk; rw [show bp₀.topSwapAct = 0 from rfl]; simp
      unfold toPhys
      rw [show bp₀.K = bp.K from rfl, show bp₀.q = bp.q from rfl,
        show bp₀.slabOf = bp.slabOf from rfl,
        show bp₀.actCur b' = bp.actCur b' from rfl,
        show bp₀.actBlk = bp.actBlk from rfl,
        show bp₀.tailRing = bp.tailRing from rfl,
        show bp₀.head = bp.head from rfl,
        show bp_mid.K = bp.K from rfl, show bp_mid.q = bp.q from rfl,
        show bp_mid.slabOf = bp.slabOf from rfl,
        show bp_mid.actCur b' = bp.actCur b' from rfl,
        show bp_mid.actBlk = bp.actBlk from rfl,
        show bp_mid.tailRing = bp.tailRing from rfl,
        show bp_mid.head = bp.head from rfl]
      simp only [heff0]
      by_cases hslab : loc' < bp.q b' * bp.K
      · rw [ite_eq_left hslab, ite_eq_left hslab]
        have hvp : loc' / bp.K < bp.q b' := (Nat.div_lt_iff_lt_mul hK).mpr hslab
        obtain ⟨_, htag1, _, _⟩ := hv.slab_fwd b' hb' (loc' / bp.K) hvp
        have hneS : bp.slabOf b' (loc' / bp.K) ≠ S := fun he => by
          rw [he, htagS0] at htag1; exact absurd htag1 (by decide)
        have hneD : bp.slabOf b' (loc' / bp.K) ≠ D := fun he => by
          rw [he, hD_tag0] at htag1; exact absurd htag1 (by decide)
        rw [hmid_eff _ _ (Nat.mod_lt loc' hK), ite_eq_right hneS, ite_eq_right hneD]
      · rw [ite_eq_right hslab, ite_eq_right hslab]
        set k := loc' - bp.q b' * bp.K
        have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
        by_cases hact_k : k < bp.actCur b'
        · rw [ite_eq_left hact_k, ite_eq_left hact_k]
          obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b' hb'
          obtain ⟨_, htag2, _⟩ := hv.act_fwd b' hb' (actCode_ne_zero_of_lt_actCur hact_k)
          have hneS : bp.actBlk b' ≠ S := fun he => by
            rw [he, htagS0] at htag2; exact absurd htag2 (by decide)
          have hneD : bp.actBlk b' ≠ D := fun he => by
            rw [he, hD_tag0] at htag2; exact absurd htag2 (by decide)
          rw [hmid_eff _ _ (hact_k.trans_le (actCur_le_K hc_le)),
            ite_eq_right hneS, ite_eq_right hneD]
        · rw [ite_eq_right hact_k, ite_eq_right hact_k]
          unfold physOfTail
          rw [show bp₀.K = bp.K from rfl, show bp_mid.K = bp.K from rfl,
            show bp_mid.tbPhysBlk = bp.tbPhysBlk from rfl, heff0]
          dsimp only [bp₀]
          set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
          have hoff : t % bp.K < bp.K := Nat.mod_lt t hK
          rw [hmid_eff _ _ hoff]
          have htf := hv.tail_fwd b' hb' k (Nat.le_of_not_lt hact_k) hk_lt_r
          dsimp only at htf
          obtain ⟨_, _, hm2_t, _, _, _⟩ := htf
          by_cases htS : t / bp.K = bp.blkMeta2 S
          · rw [htS, set1_self, htbS_eq, ite_eq_left rfl]
          · rw [set1_of_ne _ _ _ _ htS]
            by_cases htD : t / bp.K = bp.blkMeta2 D
            · rw [htD, set1_self, htbD_eq, ite_eq_right hSD.symm, ite_eq_left rfl]
            · rw [set1_of_ne _ _ _ _ htD]
              have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he =>
                htS (hm2_t.symm.trans (congrArg _ he))
              have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                htD (hm2_t.symm.trans (congrArg _ he))
              rw [ite_eq_right hneS, ite_eq_right hneD]
    have hcv' : bp'.CoreValid := by
      rw [hbp'_def]
      exact
        { M_pos := hv.M_pos
          K_ge := hv.K_ge
          bkt_bounds := hv.bkt_bounds
          blkTag_lt := fun P hP => by dsimp only at hP ⊢; rw [htag_eq]; exact hv.blkTag_lt P hP
          blkTag_top := by dsimp only; rw [htag_eq]; exact hv.blkTag_top
          unres_fwd := fun i hi => by
            dsimp only at hi ⊢; rw [htag_eq]
            by_cases hiS : i = bp.blkMeta1 S
            · subst hiS; rw [set1_self, set1_self]; exact ⟨hD_lt, hD_tag0, rfl⟩
            · rw [set1_of_ne _ _ _ _ hiS]
              by_cases hiD : i = bp.blkMeta1 D
              · subst hiD; rw [set1_self, set1_of_ne _ _ _ _ hSD, set1_self]
                exact ⟨hS_lt, htagS0, rfl⟩
              · rw [set1_of_ne _ _ _ _ hiD]
                obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i hi
                have hneS : bp.unresStack i ≠ S := fun he => hiS (h3.symm.trans (congrArg _ he))
                have hneD : bp.unresStack i ≠ D := fun he => hiD (h3.symm.trans (congrArg _ he))
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨h1, h2, h3⟩
          unres_bwd := fun P hP htag0 => by
            dsimp only at hP htag0 ⊢; rw [htag_eq] at htag0
            by_cases pd : P = D
            · subst pd; rw [set1_self, set1_self]; exact ⟨hposS_lt, rfl⟩
            · rw [set1_of_ne _ _ _ _ pd]
              by_cases ps : P = S
              · subst ps; rw [set1_self, set1_of_ne _ _ _ _ hpos_ne.symm, set1_self]
                exact ⟨hposD_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ ps]
                obtain ⟨h1, h2⟩ := hv.unres_bwd P hP htag0
                have hm_neS : bp.blkMeta1 P ≠ bp.blkMeta1 S := fun he =>
                  ps (h2.symm.trans ((congrArg _ he).trans hposS_eq))
                have hm_neD : bp.blkMeta1 P ≠ bp.blkMeta1 D := fun he =>
                  pd (h2.symm.trans ((congrArg _ he).trans hposD_eq))
                rw [set1_of_ne _ _ _ _ hm_neS, set1_of_ne _ _ _ _ hm_neD]
                exact ⟨h1, h2⟩
          slab_fwd := fun b' hb' v hv_lt => by
            dsimp only at hb' hv_lt ⊢; rw [htag_eq]
            obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
            have hneS : bp.slabOf b' v ≠ S := fun he => by
              rw [he, htagS0] at h2; exact absurd h2 (by decide)
            have hneD : bp.slabOf b' v ≠ D := fun he => by
              rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
            rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
              set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
            exact ⟨h1, h2, h3, h4⟩
          slab_bwd := fun P hP htag1 => by
            dsimp only at hP htag1 ⊢; rw [htag_eq] at htag1
            have pd : P ≠ D := fun he => by
              rw [he, hD_tag0] at htag1; exact absurd htag1 (by decide)
            have ps : P ≠ S := fun he => by rw [he, htagS0] at htag1; exact absurd htag1 (by decide)
            rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps,
              set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps]
            exact hv.slab_bwd P hP htag1
          act_fwd := fun b' hb' hne => by
            dsimp only at hb' hne ⊢; rw [htag_eq]
            obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
            have hneS : bp.actBlk b' ≠ S := fun he => by
              rw [he, htagS0] at h2; exact absurd h2 (by decide)
            have hneD : bp.actBlk b' ≠ D := fun he => by
              rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
            rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
            exact ⟨h1, h2, h3⟩
          act_bwd := fun P hP htag2 => by
            dsimp only at hP htag2 ⊢; rw [htag_eq] at htag2
            have pd : P ≠ D := fun he => by
              rw [he, hD_tag0] at htag2; exact absurd htag2 (by decide)
            have ps : P ≠ S := fun he => by rw [he, htagS0] at htag2; exact absurd htag2 (by decide)
            rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps]
            exact hv.act_bwd P hP htag2
          tb_fwd := fun P hP hor => by
            dsimp only at hP hor ⊢; rw [htag_eq] at hor
            by_cases pd : P = D
            · subst pd; rw [set1_self, set1_self]; exact ⟨htbS_lt, rfl⟩
            · rw [set1_of_ne _ _ _ _ pd]
              by_cases ps : P = S
              · subst ps; rw [set1_self, set1_of_ne _ _ _ _ htb_ne.symm, set1_self]
                exact ⟨htbD_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ ps]
                obtain ⟨h1, h2⟩ := hv.tb_fwd P hP hor
                have hm_neS : bp.blkMeta2 P ≠ bp.blkMeta2 S := fun he =>
                  ps (h2.symm.trans ((congrArg _ he).trans htbS_eq))
                have hm_neD : bp.blkMeta2 P ≠ bp.blkMeta2 D := fun he =>
                  pd (h2.symm.trans ((congrArg _ he).trans htbD_eq))
                rw [set1_of_ne _ _ _ _ hm_neS, set1_of_ne _ _ _ _ hm_neD]
                exact ⟨h1, h2⟩
          freeTb_valid := fun i hi => by
            obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
            refine ⟨h1, fun P hP hor => ?_⟩
            dsimp only at hP hor ⊢; rw [htag_eq] at hor
            by_cases pd : P = D
            · subst pd; rw [set1_self]; exact h2 S hS_lt.le (Or.inl htagS0)
            · rw [set1_of_ne _ _ _ _ pd]
              by_cases ps : P = S
              · subst ps; rw [set1_self]; exact h2 D hD_lt.le (Or.inl hD_tag0)
              · rw [set1_of_ne _ _ _ _ ps]; exact h2 P hP hor
          freeTb_inj := hv.freeTb_inj
          tbHighWater_supply := by
            have hBf_eq : ({ bp with
              topSwapAct := 0, topSwapCur := 0,
              blkTag := set1 (set1 bp.blkTag S 0) D 0,
              blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
              blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
              unresStack := set1 (set1 bp.unresStack (bp.blkMeta1 D) S) (bp.blkMeta1 S) D,
              tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D } :
              BlockPoolState).B_full = bp.B_full := rfl
            dsimp only; rw [hBf_eq, htag_eq]; exact hv.tbHighWater_supply
          tbHighWater_le_max := hv.tbHighWater_le_max
          topSwap_act_le := Nat.zero_le 1
          topSwap_valid := fun h => by simp at h
          tail_fwd := fun b' hb' k hk_ge hk_lt => by
            have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
            dsimp only at htf ⊢
            rw [htag_eq]
            obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
            set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
            by_cases htS : t / bp.K = bp.blkMeta2 S
            · rw [htS, set1_self, set1_self]
              exact ⟨ha, hD_lt.le, rfl, Or.inl ⟨hD_tag0, Or.inl hD_lt⟩, hob, hor⟩
            · rw [set1_of_ne _ _ _ _ htS]
              by_cases htD : t / bp.K = bp.blkMeta2 D
              · rw [htD, set1_self, set1_of_ne _ _ _ _ hSD, set1_self]
                exact ⟨ha, hS_lt.le, rfl, Or.inl ⟨htagS0, Or.inl hS_lt⟩, hob, hor⟩
              · rw [set1_of_ne _ _ _ _ htD]
                have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he =>
                  htS (hc_m2.symm.trans (congrArg _ he))
                have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                  htD (hc_m2.symm.trans (congrArg _ he))
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩
          tail_bwd := fun P hP_le off hoff hlt hor => by
            dsimp only at hP_le hoff hlt hor ⊢
            rw [htag_eq] at hor
            by_cases pd : P = D
            · subst pd; rw [set1_self]
              exact hv.tail_bwd S hS_lt.le off hoff (Or.inl hS_lt) (Or.inl htagS0)
            · rw [set1_of_ne _ _ _ _ pd]
              by_cases ps : P = S
              · subst ps; rw [set1_self]
                exact hv.tail_bwd D hD_lt.le off hoff (Or.inl hD_lt) (Or.inl hD_tag0)
              · rw [set1_of_ne _ _ _ _ ps]
                rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps] at hor
                exact hv.tail_bwd P hP_le off hoff hlt hor }
    exact ⟨hcv', by rw [hbp'_def], fun _ => by rw [hbp'_def]; rfl, htp_eq⟩
  · by_cases htagS1 : bp.blkTag S = 1
    · obtain ⟨hbS, hvpS, hslabS_eq⟩ := hv.slab_bwd S hS_lt htagS1
      set bp' := bp.commitTopSwap
      have hbp'_def : bp' =
          { bp with
            topSwapAct := 0
            topSwapCur := 0
            blkTag := set1 (set1 bp.blkTag S 0) D 1
            blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S)
            blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S)
            slabOf := set2 bp.slabOf (bp.blkMeta1 S) (bp.blkMeta2 S) D
            unresStack := set1 bp.unresStack (bp.blkMeta1 D) S
            tbPhysBlk := set1 bp.tbPhysBlk (bp.blkMeta2 D) S } := by
        dsimp only [bp']; unfold commitTopSwap; dsimp only
        rw [ite_eq_right htagS0, ite_eq_left htagS1, htagS1]
      have htp_eq : ∀ b' < bp.M, ∀ loc' < bp.bktCount b',
          bp'.toPhys b' loc' = bp_mid.toPhys b' loc' := fun b' hb' loc' hloc' => by
        rw [hbp'_def]
        set bp₀ : BlockPoolState :=
          { bp with
            topSwapAct := 0, topSwapCur := 0,
            blkTag := set1 (set1 bp.blkTag S 0) D 1,
            blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
            blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
            slabOf := set2 bp.slabOf (bp.blkMeta1 S) (bp.blkMeta2 S) D,
            unresStack := set1 bp.unresStack (bp.blkMeta1 D) S,
            tbPhysBlk := set1 bp.tbPhysBlk (bp.blkMeta2 D) S }
        have heff0 : ∀ E o, bp₀.effBlk E o = E := fun E o => by
          unfold effBlk
          rw [show bp₀.topSwapAct = 0 from rfl]; simp
        unfold toPhys
        rw [show bp₀.K = bp.K from rfl, show bp₀.q = bp.q from rfl,
          show bp₀.actCur b' = bp.actCur b' from rfl,
          show bp₀.actBlk = bp.actBlk from rfl,
          show bp₀.tailRing = bp.tailRing from rfl,
          show bp₀.head = bp.head from rfl,
          show bp_mid.K = bp.K from rfl, show bp_mid.q = bp.q from rfl,
          show bp_mid.slabOf = bp.slabOf from rfl,
          show bp_mid.actCur b' = bp.actCur b' from rfl,
          show bp_mid.actBlk = bp.actBlk from rfl,
          show bp_mid.tailRing = bp.tailRing from rfl,
          show bp_mid.head = bp.head from rfl]
        simp only [heff0]
        by_cases hslab : loc' < bp.q b' * bp.K
        · rw [ite_eq_left hslab, ite_eq_left hslab]
          have hvp : loc' / bp.K < bp.q b' := (Nat.div_lt_iff_lt_mul hK).mpr hslab
          have hoff : loc' % bp.K < bp.K := Nat.mod_lt loc' hK
          rw [hmid_eff _ _ hoff]
          dsimp only [bp₀]
          by_cases matchS : b' = bp.blkMeta1 S ∧ loc' / bp.K = bp.blkMeta2 S
          · rcases matchS with ⟨rfl, hv_eq⟩
            rw [hv_eq, set2_self, hslabS_eq, ite_eq_left rfl]
          · rw [set2_of_ne _ _ _ _ _ _ matchS]
            obtain ⟨_, htag1_v, hm1_v, hm2_v⟩ := hv.slab_fwd b' hb' (loc' / bp.K) hvp
            have hneS : bp.slabOf b' (loc' / bp.K) ≠ S := fun he => by
              rw [he] at hm1_v hm2_v; exact matchS ⟨hm1_v.symm, hm2_v.symm⟩
            have hneD : bp.slabOf b' (loc' / bp.K) ≠ D := fun he => by
              rw [he, hD_tag0] at htag1_v; exact absurd htag1_v (by decide)
            rw [ite_eq_right hneS, ite_eq_right hneD]
        · rw [ite_eq_right hslab, ite_eq_right hslab]
          set k := loc' - bp.q b' * bp.K
          have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
          by_cases hact_k : k < bp.actCur b'
          · rw [ite_eq_left hact_k, ite_eq_left hact_k]
            obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b' hb'
            obtain ⟨_, htag2, _⟩ := hv.act_fwd b' hb' (actCode_ne_zero_of_lt_actCur hact_k)
            have hneS : bp.actBlk b' ≠ S := fun he => by
              rw [he, htagS1] at htag2; exact absurd htag2 (by decide)
            have hneD : bp.actBlk b' ≠ D := fun he => by
              rw [he, hD_tag0] at htag2; exact absurd htag2 (by decide)
            rw [hmid_eff _ _ (hact_k.trans_le (actCur_le_K hc_le)),
              ite_eq_right hneS, ite_eq_right hneD]
          · rw [ite_eq_right hact_k, ite_eq_right hact_k]
            unfold physOfTail
            rw [show bp₀.K = bp.K from rfl, show bp_mid.K = bp.K from rfl,
              show bp_mid.tbPhysBlk = bp.tbPhysBlk from rfl, heff0]
            dsimp only [bp₀]
            set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
            have hoff : t % bp.K < bp.K := Nat.mod_lt t hK
            rw [hmid_eff _ _ hoff]
            have htf := hv.tail_fwd b' hb' k (Nat.le_of_not_lt hact_k) hk_lt_r
            dsimp only at htf
            obtain ⟨_, _, hm2_t, hkind_t, _, _⟩ := htf
            by_cases htD : t / bp.K = bp.blkMeta2 D
            · rw [htD, set1_self, htbD_eq, ite_eq_right hSD.symm, ite_eq_left rfl]
            · rw [set1_of_ne _ _ _ _ htD]
              have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                htD (hm2_t.symm.trans (congrArg _ he))
              have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he => by
                rcases hkind_t with ⟨ht0, _⟩ | ⟨_, ht2, _⟩
                · rw [he, htagS1] at ht0; exact absurd ht0 (by decide)
                · rw [he, htagS1] at ht2; exact absurd ht2 (by decide)
              rw [ite_eq_right hneS, ite_eq_right hneD]
      have hcv' : bp'.CoreValid := by
        rw [hbp'_def]
        exact
          { M_pos := hv.M_pos
            K_ge := hv.K_ge
            bkt_bounds := hv.bkt_bounds
            blkTag_lt := fun P hP => by
              dsimp only at hP ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self]; decide
              · rw [set1_of_ne _ _ _ _ pd]
                by_cases ps : P = S
                · subst ps; rw [set1_self]; decide
                · rw [set1_of_ne _ _ _ _ ps]; exact hv.blkTag_lt P hP
            blkTag_top := by
              change set1 (set1 bp.blkTag S 0) D _ bp.B_full = 0
              rw [set1_of_ne _ _ _ _ hD_ne_B.symm, set1_of_ne _ _ _ _ hS_ne_B.symm]
              exact hv.blkTag_top
            unres_fwd := fun i hi => by
              dsimp only at hi ⊢
              by_cases hiD : i = bp.blkMeta1 D
              · subst hiD
                rw [set1_self, set1_of_ne _ _ _ _ hSD, set1_self,
                  set1_of_ne _ _ _ _ hSD, set1_self]
                exact ⟨hS_lt, rfl, rfl⟩
              · rw [set1_of_ne _ _ _ _ hiD]
                obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i hi
                have hneD : bp.unresStack i ≠ D := fun he => hiD (h3.symm.trans (congrArg _ he))
                have hneS : bp.unresStack i ≠ S := fun he => by
                  rw [he, htagS1] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨h1, h2, h3⟩
            unres_bwd := fun P hP htag0 => by
              dsimp only at hP htag0 ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at htag0; exact absurd htag0 (by decide)
              rw [set1_of_ne _ _ _ _ pd] at htag0 ⊢
              by_cases ps : P = S
              · subst ps; rw [set1_self, set1_self]; exact ⟨hposD_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ ps] at htag0 ⊢
                obtain ⟨h1, h2⟩ := hv.unres_bwd P hP htag0
                have hm_neD : bp.blkMeta1 P ≠ bp.blkMeta1 D := fun he =>
                  pd (h2.symm.trans ((congrArg _ he).trans hposD_eq))
                rw [set1_of_ne _ _ _ _ hm_neD]
                exact ⟨h1, h2⟩
            slab_fwd := fun b' hb' v hv_lt => by
              dsimp only at hb' hv_lt ⊢
              by_cases hm : b' = bp.blkMeta1 S ∧ v = bp.blkMeta2 S
              · rcases hm with ⟨rfl, rfl⟩
                rw [set2_self, set1_self, set1_self, set1_self]
                exact ⟨hD_lt, rfl, rfl, rfl⟩
              · rw [set2_of_ne _ _ _ _ _ _ hm]
                obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
                have hneS : bp.slabOf b' v ≠ S := fun he => by
                  rw [he] at h3 h4; exact hm ⟨h3.symm, h4.symm⟩
                have hneD : bp.slabOf b' v ≠ D := fun he => by
                  rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨h1, h2, h3, h4⟩
            slab_bwd := fun P hP htag1 => by
              dsimp only at hP htag1 ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self, set1_self, set2_self]
                exact ⟨hbS, hvpS, rfl⟩
              · rw [set1_of_ne _ _ _ _ pd] at htag1 ⊢
                have ps : P ≠ S := fun he => by
                  rw [he, set1_self] at htag1; exact absurd htag1 (by decide)
                rw [set1_of_ne _ _ _ _ ps] at htag1 ⊢
                rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps]
                obtain ⟨h1, h2, h3⟩ := hv.slab_bwd P hP htag1
                have hne_m : ¬(bp.blkMeta1 P = bp.blkMeta1 S ∧ bp.blkMeta2 P = bp.blkMeta2 S) := by
                  rintro ⟨e1, e2⟩; rw [e1, e2, hslabS_eq] at h3; exact ps h3.symm
                rw [set2_of_ne _ _ _ _ _ _ hne_m]
                exact ⟨h1, h2, h3⟩
            act_fwd := fun b' hb' hne => by
              dsimp only at hb' hne ⊢
              obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
              have hneD : bp.actBlk b' ≠ D := fun he => by
                rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
              have hneS : bp.actBlk b' ≠ S := fun he => by
                rw [he, htagS1] at h2; exact absurd h2 (by decide)
              rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
              exact ⟨h1, h2, h3⟩
            act_bwd := fun P hP htag2 => by
              dsimp only at hP htag2 ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at htag2; exact absurd htag2 (by decide)
              have ps : P ≠ S := fun he => by
                rw [he, set1_of_ne _ _ _ _ hSD, set1_self] at htag2; exact absurd htag2 (by decide)
              rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps] at htag2 ⊢
              exact hv.act_bwd P hP htag2
            tb_fwd := fun P hP hor => by
              dsimp only at hP hor ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at hor; rcases hor with h | h <;> exact absurd h (by decide)
              rw [set1_of_ne _ _ _ _ pd] at hor ⊢
              by_cases ps : P = S
              · subst ps; rw [set1_self, set1_self]; exact ⟨htbD_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ ps] at hor ⊢
                obtain ⟨h1, h2⟩ := hv.tb_fwd P hP hor
                have hm_neD : bp.blkMeta2 P ≠ bp.blkMeta2 D := fun he =>
                  pd (h2.symm.trans ((congrArg _ he).trans htbD_eq))
                rw [set1_of_ne _ _ _ _ hm_neD]
                exact ⟨h1, h2⟩
            freeTb_valid := fun i hi => by
              obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
              refine ⟨h1, fun P hP hor => ?_⟩
              dsimp only at hP hor ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at hor; rcases hor with h | h <;> exact absurd h (by decide)
              rw [set1_of_ne _ _ _ _ pd] at hor ⊢
              by_cases ps : P = S
              · subst ps; rw [set1_self]; exact h2 D hD_lt.le (Or.inl hD_tag0)
              · rw [set1_of_ne _ _ _ _ ps] at hor ⊢; exact h2 P hP hor
            freeTb_inj := hv.freeTb_inj
            tbHighWater_supply := by
              have hBf_eq : ({ bp with
                topSwapAct := 0, topSwapCur := 0,
                blkTag := set1 (set1 bp.blkTag S 0) D 1,
                blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
                blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
                slabOf := set2 bp.slabOf (bp.blkMeta1 S) (bp.blkMeta2 S) D,
                unresStack := set1 bp.unresStack (bp.blkMeta1 D) S,
                tbPhysBlk := set1 bp.tbPhysBlk (bp.blkMeta2 D) S } :
                BlockPoolState).B_full = bp.B_full := rfl
              dsimp only; rw [hBf_eq]
              have hcard := filter_tail_card_swap (N := bp.B_full + 1) (t := bp.blkTag)
                (by omega : S < bp.B_full + 1) (by omega : D < bp.B_full + 1) hSD
              rw [hD_tag0, htagS1] at hcard
              rw [hcard]; exact hv.tbHighWater_supply
            tbHighWater_le_max := hv.tbHighWater_le_max
            topSwap_act_le := Nat.zero_le 1
            topSwap_valid := fun h => by simp at h
            tail_fwd := fun b' hb' k hk_ge hk_lt => by
              have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
              dsimp only at htf ⊢
              obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
              set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
              by_cases htD : t / bp.K = bp.blkMeta2 D
              · rw [htD, set1_self, set1_of_ne _ _ _ _ hSD, set1_self,
                  set1_of_ne _ _ _ _ hSD, set1_self]
                exact ⟨ha, hS_lt.le, rfl, Or.inl ⟨rfl, Or.inl hS_lt⟩, hob, hor⟩
              · rw [set1_of_ne _ _ _ _ htD]
                have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                  htD (hc_m2.symm.trans (congrArg _ he))
                have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he => by
                  rcases hkind with ⟨ht0, _⟩ | ⟨_, ht2, _⟩
                  · rw [he, htagS1] at ht0; exact absurd ht0 (by decide)
                  · rw [he, htagS1] at ht2; exact absurd ht2 (by decide)
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩
            tail_bwd := fun P hP_le off hoff hlt hor => by
              dsimp only at hP_le hoff hlt hor ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at hor; rcases hor with h | ⟨h, _⟩ <;> exact absurd h (by decide)
              rw [set1_of_ne _ _ _ _ pd] at hor ⊢
              by_cases ps : P = S
              · subst ps; rw [set1_self]
                exact hv.tail_bwd D hD_lt.le off hoff (Or.inl hD_lt) (Or.inl hD_tag0)
              · rw [set1_of_ne _ _ _ _ ps] at hor ⊢
                rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps] at hor
                exact hv.tail_bwd P hP_le off hoff hlt hor }
      exact ⟨hcv', by rw [hbp'_def], fun _ => by rw [hbp'_def]; rfl, htp_eq⟩
    · -- `bp.blkTag S = 2`
      have htagS2 : bp.blkTag S = 2 := by omega
      obtain ⟨hbS, hneS_c, hactS_eq⟩ := hv.act_bwd S hS_lt htagS2
      obtain ⟨htbS_lt, htbS_eq⟩ := hv.tb_fwd S hS_lt.le (Or.inr htagS2)
      have htb_ne : bp.blkMeta2 S ≠ bp.blkMeta2 D := fun he => by
        have h := congrArg bp.tbPhysBlk he; rw [htbS_eq, htbD_eq] at h; exact hSD h
      set bp' := bp.commitTopSwap
      have hbp'_def : bp' =
          { bp with
            topSwapAct := 0
            topSwapCur := 0
            blkTag := set1 (set1 bp.blkTag S 0) D 2
            blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S)
            blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S)
            actBlk := set1 bp.actBlk (bp.blkMeta1 S) D
            unresStack := set1 bp.unresStack (bp.blkMeta1 D) S
            tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D } := by
        dsimp only [bp']; unfold commitTopSwap; dsimp only
        rw [ite_eq_right htagS0, ite_eq_right htagS1, htagS2]
      have htp_eq : ∀ b' < bp.M, ∀ loc' < bp.bktCount b',
          bp'.toPhys b' loc' = bp_mid.toPhys b' loc' := fun b' hb' loc' hloc' => by
        rw [hbp'_def]
        set bp₀ : BlockPoolState :=
          { bp with
            topSwapAct := 0, topSwapCur := 0,
            blkTag := set1 (set1 bp.blkTag S 0) D 2,
            blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
            blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
            actBlk := set1 bp.actBlk (bp.blkMeta1 S) D,
            unresStack := set1 bp.unresStack (bp.blkMeta1 D) S,
            tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D }
        have heff0 : ∀ E o, bp₀.effBlk E o = E := fun E o => by
          unfold effBlk; rw [show bp₀.topSwapAct = 0 from rfl]; simp
        unfold toPhys
        rw [show bp₀.K = bp.K from rfl, show bp₀.q = bp.q from rfl,
          show bp₀.slabOf = bp.slabOf from rfl,
          show bp₀.actCur b' = bp.actCur b' from rfl,
          show bp₀.tailRing = bp.tailRing from rfl,
          show bp₀.head = bp.head from rfl,
          show bp_mid.K = bp.K from rfl, show bp_mid.q = bp.q from rfl,
          show bp_mid.slabOf = bp.slabOf from rfl,
          show bp_mid.actCur b' = bp.actCur b' from rfl,
          show bp_mid.actBlk = bp.actBlk from rfl,
          show bp_mid.tailRing = bp.tailRing from rfl,
          show bp_mid.head = bp.head from rfl]
        simp only [heff0]
        by_cases hslab : loc' < bp.q b' * bp.K
        · rw [ite_eq_left hslab, ite_eq_left hslab]
          have hvp : loc' / bp.K < bp.q b' := (Nat.div_lt_iff_lt_mul hK).mpr hslab
          obtain ⟨_, htag1_v, _, _⟩ := hv.slab_fwd b' hb' (loc' / bp.K) hvp
          have hneS : bp.slabOf b' (loc' / bp.K) ≠ S := fun he => by
            rw [he, htagS2] at htag1_v; exact absurd htag1_v (by decide)
          have hneD : bp.slabOf b' (loc' / bp.K) ≠ D := fun he => by
            rw [he, hD_tag0] at htag1_v; exact absurd htag1_v (by decide)
          rw [hmid_eff _ _ (Nat.mod_lt loc' hK), ite_eq_right hneS, ite_eq_right hneD]
        · rw [ite_eq_right hslab, ite_eq_right hslab]
          set k := loc' - bp.q b' * bp.K
          have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
          by_cases hact_k : k < bp.actCur b'
          · rw [ite_eq_left hact_k, ite_eq_left hact_k]
            obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b' hb'
            rw [hmid_eff _ _ (hact_k.trans_le (actCur_le_K hc_le))]
            dsimp only [bp₀]
            by_cases hbeS : b' = bp.blkMeta1 S
            · subst hbeS; rw [set1_self, hactS_eq, ite_eq_left rfl]
            · rw [set1_of_ne _ _ _ _ hbeS]
              obtain ⟨_, htag2, hm1_b⟩ := hv.act_fwd b' hb' (actCode_ne_zero_of_lt_actCur hact_k)
              have hneS : bp.actBlk b' ≠ S := fun he => by
                rw [he] at hm1_b; exact hbeS hm1_b.symm
              have hneD : bp.actBlk b' ≠ D := fun he => by
                rw [he, hD_tag0] at htag2; exact absurd htag2 (by decide)
              rw [ite_eq_right hneS, ite_eq_right hneD]
          · rw [ite_eq_right hact_k, ite_eq_right hact_k]
            unfold physOfTail
            rw [show bp₀.K = bp.K from rfl, show bp_mid.K = bp.K from rfl,
              show bp_mid.tbPhysBlk = bp.tbPhysBlk from rfl, heff0]
            dsimp only [bp₀]
            set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
            have hoff : t % bp.K < bp.K := Nat.mod_lt t hK
            rw [hmid_eff _ _ hoff]
            have htf := hv.tail_fwd b' hb' k (Nat.le_of_not_lt hact_k) hk_lt_r
            dsimp only at htf
            obtain ⟨_, _, hm2_t, _, _, _⟩ := htf
            by_cases htS : t / bp.K = bp.blkMeta2 S
            · rw [htS, set1_self, htbS_eq, ite_eq_left rfl]
            · rw [set1_of_ne _ _ _ _ htS]
              by_cases htD : t / bp.K = bp.blkMeta2 D
              · rw [htD, set1_self, htbD_eq, ite_eq_right hSD.symm, ite_eq_left rfl]
              · rw [set1_of_ne _ _ _ _ htD]
                have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he =>
                  htS (hm2_t.symm.trans (congrArg _ he))
                have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                  htD (hm2_t.symm.trans (congrArg _ he))
                rw [ite_eq_right hneS, ite_eq_right hneD]
      have hcv' : bp'.CoreValid := by
        rw [hbp'_def]
        exact
          { M_pos := hv.M_pos
            K_ge := hv.K_ge
            bkt_bounds := hv.bkt_bounds
            blkTag_lt := fun P hP => by
              dsimp only at hP ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self]; decide
              · rw [set1_of_ne _ _ _ _ pd]
                by_cases ps : P = S
                · subst ps; rw [set1_self]; decide
                · rw [set1_of_ne _ _ _ _ ps]; exact hv.blkTag_lt P hP
            blkTag_top := by
              change set1 (set1 bp.blkTag S 0) D _ bp.B_full = 0
              rw [set1_of_ne _ _ _ _ hD_ne_B.symm, set1_of_ne _ _ _ _ hS_ne_B.symm]
              exact hv.blkTag_top
            unres_fwd := fun i hi => by
              dsimp only at hi ⊢
              by_cases hiD : i = bp.blkMeta1 D
              · subst hiD
                rw [set1_self, set1_of_ne _ _ _ _ hSD, set1_self,
                  set1_of_ne _ _ _ _ hSD, set1_self]
                exact ⟨hS_lt, rfl, rfl⟩
              · rw [set1_of_ne _ _ _ _ hiD]
                obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i hi
                have hneD : bp.unresStack i ≠ D := fun he => hiD (h3.symm.trans (congrArg _ he))
                have hneS : bp.unresStack i ≠ S := fun he => by
                  rw [he, htagS2] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨h1, h2, h3⟩
            unres_bwd := fun P hP htag0 => by
              dsimp only at hP htag0 ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at htag0; exact absurd htag0 (by decide)
              rw [set1_of_ne _ _ _ _ pd] at htag0 ⊢
              by_cases ps : P = S
              · subst ps; rw [set1_self, set1_self]; exact ⟨hposD_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ ps] at htag0 ⊢
                obtain ⟨h1, h2⟩ := hv.unres_bwd P hP htag0
                have hm_neD : bp.blkMeta1 P ≠ bp.blkMeta1 D := fun he =>
                  pd (h2.symm.trans ((congrArg _ he).trans hposD_eq))
                rw [set1_of_ne _ _ _ _ hm_neD]
                exact ⟨h1, h2⟩
            slab_fwd := fun b' hb' v hv_lt => by
              dsimp only at hb' hv_lt ⊢
              obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hv_lt
              have hneD : bp.slabOf b' v ≠ D := fun he => by
                rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
              have hneS : bp.slabOf b' v ≠ S := fun he => by
                rw [he, htagS2] at h2; exact absurd h2 (by decide)
              rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
              exact ⟨h1, h2, h3, h4⟩
            slab_bwd := fun P hP htag1 => by
              dsimp only at hP htag1 ⊢
              have pd : P ≠ D := fun he => by
                rw [he, set1_self] at htag1; exact absurd htag1 (by decide)
              have ps : P ≠ S := fun he => by
                rw [he, set1_of_ne _ _ _ _ hSD, set1_self] at htag1; exact absurd htag1 (by decide)
              rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps] at htag1 ⊢
              rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps]
              exact hv.slab_bwd P hP htag1
            act_fwd := fun b' hb' hne => by
              dsimp only at hb' hne ⊢
              by_cases hbeS : b' = bp.blkMeta1 S
              · subst hbeS; rw [set1_self, set1_self, set1_self]
                exact ⟨hD_lt, rfl, rfl⟩
              · rw [set1_of_ne _ _ _ _ hbeS]
                obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
                have hneS : bp.actBlk b' ≠ S := fun he => by
                  rw [he] at h3; exact hbeS h3.symm
                have hneD : bp.actBlk b' ≠ D := fun he => by
                  rw [he, hD_tag0] at h2; exact absurd h2 (by decide)
                rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                  set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                exact ⟨h1, h2, h3⟩
            act_bwd := fun P hP htag2 => by
              dsimp only at hP htag2 ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self, set1_self]; exact ⟨hbS, hneS_c, rfl⟩
              · rw [set1_of_ne _ _ _ _ pd] at htag2 ⊢
                have ps : P ≠ S := fun he => by
                  rw [he, set1_self] at htag2; exact absurd htag2 (by decide)
                rw [set1_of_ne _ _ _ _ ps] at htag2 ⊢
                obtain ⟨h1, h2, h3⟩ := hv.act_bwd P hP htag2
                have hbeS : bp.blkMeta1 P ≠ bp.blkMeta1 S := fun he => by
                  rw [he, hactS_eq] at h3; exact ps h3.symm
                rw [set1_of_ne _ _ _ _ hbeS]
                exact ⟨h1, h2, h3⟩
            tb_fwd := fun P hP hor => by
              dsimp only at hP hor ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self, set1_self]; exact ⟨htbS_lt, rfl⟩
              · rw [set1_of_ne _ _ _ _ pd] at hor ⊢
                by_cases ps : P = S
                · subst ps; rw [set1_self, set1_of_ne _ _ _ _ htb_ne.symm, set1_self]
                  exact ⟨htbD_lt, rfl⟩
                · rw [set1_of_ne _ _ _ _ ps] at hor ⊢
                  obtain ⟨h1, h2⟩ := hv.tb_fwd P hP hor
                  have hm_neS : bp.blkMeta2 P ≠ bp.blkMeta2 S := fun he =>
                    ps (h2.symm.trans ((congrArg _ he).trans htbS_eq))
                  have hm_neD : bp.blkMeta2 P ≠ bp.blkMeta2 D := fun he =>
                    pd (h2.symm.trans ((congrArg _ he).trans htbD_eq))
                  rw [set1_of_ne _ _ _ _ hm_neS, set1_of_ne _ _ _ _ hm_neD]
                  exact ⟨h1, h2⟩
            freeTb_valid := fun i hi => by
              obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
              refine ⟨h1, fun P hP hor => ?_⟩
              dsimp only at hP hor ⊢
              by_cases pd : P = D
              · subst pd; rw [set1_self]; exact h2 S hS_lt.le (Or.inr htagS2)
              · rw [set1_of_ne _ _ _ _ pd] at hor ⊢
                by_cases ps : P = S
                · subst ps; rw [set1_self]; exact h2 D hD_lt.le (Or.inl hD_tag0)
                · rw [set1_of_ne _ _ _ _ ps] at hor ⊢; exact h2 P hP hor
            freeTb_inj := hv.freeTb_inj
            tbHighWater_supply := by
              have hBf_eq : ({ bp with
                topSwapAct := 0, topSwapCur := 0,
                blkTag := set1 (set1 bp.blkTag S 0) D 2,
                blkMeta1 := set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S),
                blkMeta2 := set1 (set1 bp.blkMeta2 S (bp.blkMeta2 D)) D (bp.blkMeta2 S),
                actBlk := set1 bp.actBlk (bp.blkMeta1 S) D,
                unresStack := set1 bp.unresStack (bp.blkMeta1 D) S,
                tbPhysBlk := set1 (set1 bp.tbPhysBlk (bp.blkMeta2 D) S) (bp.blkMeta2 S) D } :
                BlockPoolState).B_full = bp.B_full := rfl
              dsimp only; rw [hBf_eq]
              have hcard := filter_tail_card_swap (N := bp.B_full + 1) (t := bp.blkTag)
                (by omega : S < bp.B_full + 1) (by omega : D < bp.B_full + 1) hSD
              rw [hD_tag0, htagS2] at hcard
              rw [hcard]; exact hv.tbHighWater_supply
            tbHighWater_le_max := hv.tbHighWater_le_max
            topSwap_act_le := Nat.zero_le 1
            topSwap_valid := fun h => by simp at h
            tail_fwd := fun b' hb' k hk_ge hk_lt => by
              have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
              dsimp only at htf ⊢
              obtain ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩ := htf
              set t := bp.tailRing b' ((bp.head b' + k) % (6 * bp.K))
              by_cases htS : t / bp.K = bp.blkMeta2 S
              · rw [htS, set1_self, set1_self, set1_self, set1_self]
                rcases hkind with ⟨ht0, _⟩ | ⟨_, _, hge_m⟩
                · rw [htS, htbS_eq, htagS2] at ht0; exact absurd ht0 (by decide)
                · rw [htS, htbS_eq] at hge_m
                  exact ⟨ha, hD_lt.le, rfl, Or.inr ⟨hD_lt, rfl, hge_m⟩, hob, hor⟩
              · rw [set1_of_ne _ _ _ _ htS]
                by_cases htD : t / bp.K = bp.blkMeta2 D
                · rw [htD, set1_self, set1_of_ne _ _ _ _ hSD, set1_self,
                    set1_of_ne _ _ _ _ hSD, set1_self]
                  exact ⟨ha, hS_lt.le, rfl, Or.inl ⟨rfl, Or.inl hS_lt⟩, hob, hor⟩
                · rw [set1_of_ne _ _ _ _ htD]
                  have hneS : bp.tbPhysBlk (t / bp.K) ≠ S := fun he =>
                    htS (hc_m2.symm.trans (congrArg _ he))
                  have hneD : bp.tbPhysBlk (t / bp.K) ≠ D := fun he =>
                    htD (hc_m2.symm.trans (congrArg _ he))
                  rw [set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                    set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS,
                    set1_of_ne _ _ _ _ hneD, set1_of_ne _ _ _ _ hneS]
                  exact ⟨ha, hb_le, hc_m2, hkind, hob, hor⟩
            tail_bwd := fun P hP_le off hoff hlt hor => by
              dsimp only at hP_le hoff hlt hor ⊢
              by_cases pd : P = D
              · subst pd
                rw [set1_self, set1_self] at hor
                rw [set1_self]
                have hge_m : bp.actCur (bp.blkMeta1 S) ≤ off := by
                  rcases hor with h0 | ⟨_, hge⟩
                  · exact absurd h0 (by decide)
                  · exact hge
                exact hv.tail_bwd S hS_lt.le off hoff (Or.inl hS_lt) (Or.inr ⟨htagS2, hge_m⟩)
              · rw [set1_of_ne _ _ _ _ pd] at hor ⊢
                by_cases ps : P = S
                · subst ps; rw [set1_self]
                  exact hv.tail_bwd D hD_lt.le off hoff (Or.inl hD_lt) (Or.inl hD_tag0)
                · rw [set1_of_ne _ _ _ _ ps] at hor ⊢
                  rw [set1_of_ne _ _ _ _ pd, set1_of_ne _ _ _ _ ps] at hor
                  exact hv.tail_bwd P hP_le off hoff hlt hor }
      exact ⟨hcv', by rw [hbp'_def], fun _ => by rw [hbp'_def]; rfl, htp_eq⟩

/-- `topSwapStepOne` preserves `CoreValid`, keeps swap indices `< nSide`, preserves `bktCount`, and
preserves every `(b', loc')` item lookup across `applyOptSwap`. -/
theorem CoreValid.topSwapStepOne_spec {bp : BlockPoolState} (hv : bp.CoreValid) :
    let (bp', osw) := bp.topSwapStepOne
    bp'.CoreValid ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' : ℕ) (loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap osw arr (bp'.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  have hK := hv.K_pos
  have hn := hv.nSide_eq
  unfold topSwapStepOne
  by_cases ha0 : bp.topSwapAct = 0
  · rw [ite_eq_left ha0]
    exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
  · rw [ite_eq_right ha0]
    have ha1 : bp.topSwapAct = 1 := by have := hv.topSwap_act_le; omega
    obtain ⟨hcur_lt, hS_lt, hD_lt, hD_tag0, hSD⟩ := hv.topSwap_valid ha1
    have hpS_lt : bp.topSwapSrc * bp.K + bp.topSwapCur < bp.nSide := by
      have h1 : (bp.topSwapSrc + 1) * bp.K ≤ bp.B_full * bp.K := Nat.mul_le_mul_right _ hS_lt
      rw [Nat.add_one_mul] at h1; linarith
    have hpD_lt : bp.topSwapDst * bp.K + bp.topSwapCur < bp.nSide := by
      have h1 : (bp.topSwapDst + 1) * bp.K ≤ bp.B_full * bp.K := Nat.mul_le_mul_right _ hD_lt
      rw [Nat.add_one_mul] at h1; linarith
    by_cases hmid : bp.topSwapCur + 1 < bp.K
    · rw [ite_eq_left hmid]; dsimp only
      have hcv' : ({ bp with topSwapCur := bp.topSwapCur + 1 } : BlockPoolState).CoreValid :=
        { hv with
          topSwap_valid := fun _ => ⟨hmid, hS_lt, hD_lt, hD_tag0, hSD⟩ }
      refine ⟨hcv', rfl, fun _ => rfl, fun sw hsw => ?_, fun arr b' loc' hb' hloc' => ?_⟩
      · injection hsw with he; rw [← he]; exact ⟨hpS_lt, hpD_lt⟩
      · exact hv.topSwap_mid_toPhys ha1 arr hb' hloc'
    · rw [ite_eq_right hmid]; dsimp only
      have hcur_top : bp.topSwapCur + 1 = bp.K := by omega
      obtain ⟨hcv', hn', hbc', htp_c⟩ := hv.commitTopSwap_spec ha1
      refine ⟨hcv', hn', hbc', fun sw hsw => ?_, fun arr b' loc' hb' hloc' => ?_⟩
      · injection hsw with he; rw [← he]; exact ⟨hpS_lt, hpD_lt⟩
      · have hmid_eq : ({ bp with topSwapCur := bp.K } : BlockPoolState) =
            { bp with topSwapCur := bp.topSwapCur + 1 } := by
          congr 1; exact hcur_top.symm
        dsimp only [applyOptSwap]
        rw [htp_c b' hb' loc' hloc', hmid_eq]
        exact hv.topSwap_mid_toPhys ha1 arr hb' hloc'

/-- `topCleanOne` preserves `CoreValid`, keeps swap indices `< nSide`, preserves `bktCount`, and
preserves every `(b', loc')` item lookup across `applyOptSwap`. -/
theorem CoreValid.topCleanOne_spec {bp : BlockPoolState} (hv : bp.CoreValid)
    (hprom_q : ∀ b < bp.M, bp.actCode b = bp.K → bp.q b < bp.maxSlabs) :
    let (bp', osw) := bp.topCleanOne
    bp'.CoreValid ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' : ℕ) (loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap osw arr (bp'.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  have hK := hv.K_pos
  unfold topCleanOne
  by_cases hlt2 : bp.B_full < 2
  · rw [ite_eq_left hlt2]
    exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
  · rw [ite_eq_right hlt2]; dsimp only
    set P := bp.B_full - 2
    by_cases ha1 : bp.topSwapAct = 1
    · rw [ite_eq_left ha1]
      split_ifs
      · exact hv.topSwapStepOne_spec
      · exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
    · rw [ite_eq_right ha1]
      by_cases ht0 : bp.blkTag P = 0
      · rw [ite_eq_left ht0]
        exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩
      · rw [ite_eq_right ht0]
        by_cases ht2 : bp.blkTag P = 2
        · rw [ite_eq_left ht2]
          have hP_lt : P < bp.B_full := by dsimp only [P]; omega
          obtain ⟨hb_m, _, _⟩ := hv.act_bwd P hP_lt ht2
          exact hv.actStepOne_spec hb_m (hprom_q _ hb_m)
        · rw [ite_eq_right ht2]
          by_cases h3 : 3 ≤ bp.unresLen
          · rw [ite_eq_left h3]
            obtain ⟨_, hidx_lt, hD_add3⟩ := hv.findTopSwapIdx_spec h3
            obtain ⟨hD_lt, hD_tag0, _⟩ := hv.unres_fwd bp.findTopSwapIdx hidx_lt
            set D := bp.unresStack bp.findTopSwapIdx
            have hP_lt : P < bp.B_full := by dsimp only [P]; omega
            have hPD : P ≠ D := by dsimp only [P, D] at hD_add3 ⊢; omega
            set bp_s : BlockPoolState :=
              { bp with topSwapAct := 1, topSwapSrc := P, topSwapDst := D, topSwapCur := 0 }
            have hv_s : bp_s.CoreValid :=
              { hv with
                topSwap_act_le := le_rfl
                topSwap_valid := fun _ => ⟨hK, hP_lt, hD_lt, hD_tag0, hPD⟩ }
            have htp_s : ∀ b' loc', bp_s.toPhys b' loc' = bp.toPhys b' loc' := fun b' loc' => by
              have heff_s : ∀ E o, bp_s.effBlk E o = bp.effBlk E o := fun E o => by
                unfold effBlk
                have ha0 : bp.topSwapAct = 0 := by have := hv.topSwap_act_le; omega
                rw [show bp_s.topSwapAct = 1 from rfl, show bp_s.topSwapCur = 0 from rfl, ha0]
                simp
              unfold toPhys physOfTail
              simp only [show bp_s.K = bp.K from rfl, show bp_s.q = bp.q from rfl,
                show bp_s.slabOf = bp.slabOf from rfl,
                show bp_s.actCur b' = bp.actCur b' from rfl,
                show bp_s.actBlk = bp.actBlk from rfl,
                show bp_s.tailRing = bp.tailRing from rfl,
                show bp_s.head = bp.head from rfl,
                show bp_s.tbPhysBlk = bp.tbPhysBlk from rfl, heff_s]
            have hspec := hv_s.topSwapStepOne_spec
            rcases hstep : bp_s.topSwapStepOne with ⟨bp', osw⟩
            rw [hstep] at hspec
            obtain ⟨hcv', hn', hbc', hsw', harr'⟩ := hspec
            exact ⟨hcv', hn', hbc', hsw', fun arr b' loc' hb' hloc' =>
              (harr' arr b' loc' hb' hloc').trans (congrArg arr (htp_s b' loc'))⟩
          · rw [ite_eq_right h3]
            exact ⟨hv, rfl, fun _ => rfl, fun _ h => by simp at h, fun _ _ _ _ _ => rfl⟩

end BlockPoolState

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
