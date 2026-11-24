/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.LeafSubroutines
import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.MinSep
import Mathlib.Tactic.Linarith

/-!
# Soundness and completeness of `leafProg` and `compressProg`

This module combines `MinSep` and `LeafSubroutines` to prove `leafProg_spec` (soundness),
`leafProg_complete_at` (completeness via the base-3 odometer digit bijection), and the overall
`compressProg_spec` theorem.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctStateAt`: inductive invariant on `sepBase` and
  `colBase` for `prefixGraph G m`.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.compressProg_spec`: `compressProg` returns `1` and
  materializes an odd cycle transversal of size `≤ k` iff `prefixGraph G m` admits one.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph SimpleGraph.OddCycleTransversal
open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write clientState_map

/-- Invariant asserting a valid transversal of `prefixGraph G m` of size `≤ k` at `sepBase` and
proper `2`-colouring off it at `colBase`. -/
@[expose] def OctStateAt {n : ℕ} (G : SimpleGraph (Fin n)) (m k : ℕ) (t : Memory.State) : Prop :=
  (∀ v : Fin n, t.mem (sepBase n + v.1) ≤ 1 ∧ t.mem (colBase n + v.1) ≤ 1) ∧
    let S := Finset.univ.filter fun v : Fin n => t.mem (sepBase n + v.1) = 1
    S.card ≤ k ∧
      ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ S → v ∉ S →
        (t.mem (colBase n + u.1) == 1) ≠ (t.mem (colBase n + v.1) == 1)

theorem OctStateAt.congr {n : ℕ} {G : SimpleGraph (Fin n)} {m k : ℕ}
    {s₁ s₂ : Memory.State} (h : OctStateAt G m k s₁)
    (heq : ∀ a, sepBase n ≤ a → a < wBase n → s₂.mem a = s₁.mem a) :
    OctStateAt G m k s₂ := by
  have hsep : ∀ v : Fin n, s₂.mem (sepBase n + v.1) = s₁.mem (sepBase n + v.1) :=
    fun v => heq _ (by omega) (by dsimp only [sepBase, wBase]; omega)
  have hcol : ∀ v : Fin n, s₂.mem (colBase n + v.1) = s₁.mem (colBase n + v.1) :=
    fun v => heq _ (by dsimp only [sepBase, colBase]; omega) (by dsimp only [colBase, wBase]; omega)
  have hS : (Finset.univ.filter fun v : Fin n => s₂.mem (sepBase n + v.1) = 1) =
      (Finset.univ.filter fun v : Fin n => s₁.mem (sepBase n + v.1) = 1) := by
    ext v; simp [hsep v]
  refine ⟨fun v => ⟨(hsep v).trans_le (h.1 v).1, (hcol v).trans_le (h.1 v).2⟩, ?_⟩
  dsimp only
  rw [hS]
  refine ⟨h.2.1, fun u v hadj hu hv => ?_⟩
  rw [hcol u, hcol v]
  exact h.2.2 u v hadj hu hv

private theorem cap_lt_succ_of_cutCapacity_le {n : ℕ} {N : Network (Fin (splitCount n))}
    {C : Finset (Fin (splitCount n))} (hcap : N.cutCapacity C ≤ n)
    {x y : Fin (splitCount n)} (hx : x ∈ C) (hy : y ∉ C) :
    N.cap x y < n + 1 := by
  have hy' : y ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
  have h1 : N.cap x y ≤ ∑ z ∈ Finset.univ \ C, N.cap x z :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy'
  have h2 : ∑ z ∈ Finset.univ \ C, N.cap x z ≤ N.cutCapacity C := by
    unfold Network.cutCapacity
    exact Finset.single_le_sum (f := fun u => ∑ z ∈ Finset.univ \ C, N.cap u z)
      (fun _ _ => Nat.zero_le _) hx
  omega

private theorem leafProg_spec {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1)) :
    let res := (Memory.spec 0).clientResult s (leafProg (((n, k), m), L))
    let t := (Memory.spec 0).clientState s (leafProg (((n, k), m), L))
    res ≤ 1 ∧
      (∀ a, (a < sepBase n ∨ (wBase n ≤ a ∧ a < guessBase n)) → t.mem a = s.mem a) ∧
      (res = 0 → ∀ a < guessBase n, t.mem a = s.mem a) ∧
      (res = 1 → OctStateAt G m k t) := by
  intro res t
  have hpres_base : ∀ a, (a < sepBase n ∨ (wBase n ≤ a ∧ a < guessBase n)) → t.mem a = s.mem a :=
    fun a ha => preservesAt_leafProg ha s
  set s1 := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
  obtain ⟨hs1_low, hg_eq, _, hg_le⟩ := unpackGuessProg_spec hW hdig
  have hG1 : MatrixLoaded G s1 := fun u v =>
    (hs1_low _ (by dsimp only [guessBase]; nlinarith [u.2, v.2])).trans (hG u v)
  have hW1 : WListSpec Wset L s1 :=
    hW.congr fun a _ ha => hs1_low a (by dsimp only [digitBase, guessBase] at ha ⊢; omega)
  have hg_eq1 : ∀ j : Fin L,
      s1.mem (guessBase n + s1.mem (wListBase n + j.1)) = s1.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs1_low (wListBase n + j.1) (by dsimp only [wListBase, guessBase]; omega),
      hs1_low (digitBase n + j.1) (by dsimp only [digitBase, guessBase]; omega)]
    exact hg_eq j
  have hcol01_1 : ∀ v : Fin n, s1.mem (colBase n + v.1) ≤ 1 := fun v =>
    (hs1_low _ (by dsimp only [colBase, guessBase]; omega)).trans_le (hcol01 v)
  have hchk := checkProperProg_spec (m := m) hG1 hW1 hg_eq1 hg_le
  set s2 := (Memory.spec 0).clientState s1 (checkProperProg ((n, m), L))
  have hs2_eq : ∀ a, s2.mem a = s1.mem a := fun a => preservesAt_checkProperProg a _ s1
  by_cases hprop : ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
      u ∉ delSet Wset s1 → v ∉ delSet Wset s1 → guessCol n s1 u ≠ guessCol n s1 v
  · have hok1 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 1 := by
      rw [hchk, ite_eq_left hprop]
    have hG2 : MatrixLoaded G s2 := fun u v => (hs2_eq _).trans (hG1 u v)
    have hW2 : WListSpec Wset L s2 := hW1.congr fun a _ _ => hs2_eq a
    have hcol01_2 : ∀ v : Fin n, s2.mem (colBase n + v.1) ≤ 1 :=
      fun v => (hs2_eq _).trans_le (hcol01_1 v)
    have hg_eq2 : ∀ j : Fin L,
        s2.mem (guessBase n + s2.mem (wListBase n + j.1)) = s2.mem (digitBase n + j.1) := by
      intro j; simp only [hs2_eq]; exact hg_eq1 j
    have hg_le2 : ∀ v : Fin n, s2.mem (guessBase n + v.1) ≤ 2 :=
      fun v => (hs2_eq _).trans_le (hg_le v)
    set s3 := (Memory.spec 0).clientState s2 (buildTerminalsProg ((n, m), L))
    obtain ⟨hs3_low, hs3_keep, hs3_flip⟩ :=
      buildTerminalsProg_spec (m := m) hG2 hW2 hcol01_2 hg_eq2 hg_le2
    have hG3 : MatrixLoaded G s3 := fun u v =>
      (hs3_low _ (by dsimp only [keepBase]; nlinarith [u.2, v.2])).trans (hG2 u v)
    set sepCnt := (Memory.spec 0).clientResult s3 (minSepProg (n, m))
    set s4 := (Memory.spec 0).clientState s3 (minSepProg (n, m))
    obtain ⟨hs4_low, C, hmin, hcapC_le, hdist_iff, hsepOut, hsepCnt_eq, _⟩ :=
      minSepProg_spec (m := m) hG3
    change ∀ x : Fin (splitCount n), s4.mem (distBase n + x.1) < splitCount n ↔ x ∈ C at hdist_iff
    change ∀ v : Fin n, s4.mem (sepOutBase n + v.1) = _ at hsepOut
    change sepCnt = (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card
      at hsepCnt_eq
    have hs4_s1 : ∀ a < keepBase n, s4.mem a = s1.mem a := fun a ha =>
      (hs4_low a (by dsimp only [keepBase, flowBase] at ha ⊢; omega)).trans
        ((hs3_low a ha).trans (hs2_eq a))
    have hW4 : WListSpec Wset L s4 :=
      hW1.congr fun a _ ha => hs4_s1 a (by dsimp only [digitBase, keepBase] at ha ⊢; omega)
    have hg_eq4 : ∀ j : Fin L,
        s4.mem (guessBase n + s4.mem (wListBase n + j.1)) = s4.mem (digitBase n + j.1) := by
      intro j
      have hL_le := hW.card_le_n
      rw [hs4_s1 (wListBase n + j.1) (by dsimp only [wListBase, keepBase]; omega),
        hs4_s1 (digitBase n + j.1) (by dsimp only [digitBase, keepBase]; omega),
        hs4_s1 (guessBase n + s1.mem (wListBase n + j.1))
          (by dsimp only [guessBase, keepBase]; have := hW1.entry_lt j.1 j.2; omega)]
      exact hg_eq1 j
    have hdelCnt : (Memory.spec 0).clientResult s4 (countDelProg (n, L)) =
        (delSet Wset s4).card := countDelProg_spec hW4 hg_eq4
    set s5 := (Memory.spec 0).clientState s4 (countDelProg (n, L))
    have hs5_eq : ∀ a, s5.mem a = s4.mem a := fun a => preservesAt_countDelProg a _ s4
    have hsepCnt_le : sepCnt ≤ n := by
      rw [hsepCnt_eq]
      exact (Finset.card_le_univ _).trans (by simp)
    have hdel_le : (delSet Wset s4).card ≤ n :=
      (Finset.card_le_univ _).trans (by simp)
    by_cases hsum_le : (delSet Wset s4).card + sepCnt ≤ k
    · have hcond_acc : sepCnt ≤ n ∧ (delSet Wset s4).card ≤ n ∧
          (delSet Wset s4).card + sepCnt ≤ k := ⟨hsepCnt_le, hdel_le, hsum_le⟩
      have hres1 : res = 1 := by
        change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 1
        unfold leafProg
        dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
        rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
          clientResult_bind, clientResult_bind, hdelCnt,
          ite_eq_left hcond_acc, clientResult_bind, clientResult_pure]
      have ht_eq : t = (Memory.spec 0).clientState s5 (commitLeafProg n) := by
        change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = _
        unfold leafProg
        dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
        rw [clientState_bind, clientState_bind, hok1, ite_eq_left rfl, clientState_bind,
          clientState_bind, clientState_bind, hdelCnt,
          ite_eq_left hcond_acc, clientState_bind, clientState_pure]
      refine ⟨by omega, hpres_base, fun h0 => absurd hres1 (by omega), fun _ => ?_⟩
      rw [ht_eq]
      have hW5 : WListSpec Wset L s5 := hW4.congr fun a _ _ => hs5_eq a
      have hcol01_5 : ∀ v : Fin n, s5.mem (colBase n + v.1) ≤ 1 := fun v => by
        rw [hs5_eq, hs4_s1 _ (by dsimp only [colBase, keepBase]; omega)]; exact hcol01_1 v
      obtain ⟨_, hsep_t, hcol01_t, hcW_t, hcW'_t⟩ :=
        commitLeafProg_spec hW5 hcol01_5
      set s6 := (Memory.spec 0).clientState s5 (commitLeafProg n)
      let X : Finset (Fin n) := Finset.univ.filter fun v => s5.mem (sepOutBase n + v.1) = 1
      change ∀ v : Fin n, s6.mem (sepBase n + v.1) =
        if v ∈ delSet Wset s5 ∪ X then 1 else 0 at hsep_t
      have hX_iff : ∀ v : Fin n, v ∈ X ↔ v ∉ Wset ∧ inIdx v ∈ C ∧ outIdx v ∉ C := by
        intro v
        have hv_lt := v.2
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        rw [hs5_eq, hsepOut v,
          hs3_low (wBase n + v.1) (by dsimp only [wBase, keepBase]; omega), hs2_eq,
          hs1_low (wBase n + v.1) (by dsimp only [wBase, guessBase]; omega), hW.w_mem v]
        by_cases hvW : v ∈ Wset <;> by_cases hC : inIdx v ∈ C ∧ outIdx v ∉ C <;> simp [hvW, hC]
      have hdel_eq : delSet Wset s5 = delSet Wset s1 := by
        ext w
        simp only [delSet, Finset.mem_filter, hs5_eq,
          hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
      have hgcol_eq : guessCol n s5 = guessCol n s1 := by
        funext w
        unfold guessCol
        rw [hs5_eq,
          hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
      have hS6 : (Finset.univ.filter fun v : Fin n => s6.mem (sepBase n + v.1) = 1) =
          delSet Wset s5 ∪ X := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsep_t v]
        by_cases h : v ∈ delSet Wset s5 ∪ X <;> simp [h]
      have hX_card : X.card = sepCnt := by
        rw [hsepCnt_eq]
        congr 1
        ext v
        simp [X, hs5_eq]
      have hdel5_card : (delSet Wset s5).card = (delSet Wset s4).card := by
        congr 1; ext w; simp [delSet, hs5_eq]
      refine ⟨fun v => ⟨by rw [hsep_t v]; split_ifs <;> decide, hcol01_t v⟩, ?_⟩
      dsimp only
      rw [hS6]
      refine ⟨(Finset.card_union_le _ _).trans (by omega), ?_⟩
      let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.1) == 1
      let side : Fin n → Bool := fun v => decide (outIdx v ∈ C)
      let c' : Fin n → Bool := fun v => s6.mem (colBase n + v.1) == 1
      have hc₀_s2 : (fun v : Fin n => s2.mem (colBase n + v.1) == 1) = c₀ := by
        funext v
        dsimp only [c₀]
        rw [hs2_eq, hs1_low _ (by dsimp only [colBase, guessBase]; omega)]
      have hdel_s2 : delSet Wset s2 = delSet Wset s1 := by
        ext w; simp [delSet, hs2_eq]
      have hgcol_s2 : guessCol n s2 = guessCol n s1 := by
        funext w; unfold guessCol; rw [hs2_eq]
      have hside_edges : ∀ ⦃u v : Fin n⦄, (prefixGraph G m).Adj u v →
          u ∉ (Wset : Set (Fin n)) → v ∉ (Wset : Set (Fin n)) →
          u ∉ (X : Set (Fin n)) → v ∉ (X : Set (Fin n)) → side u = side v := by
        have hdir : ∀ ⦃u v : Fin n⦄, (prefixGraph G m).Adj u v →
            u ∉ Wset → v ∉ Wset → v ∉ X → outIdx u ∈ C → outIdx v ∈ C := by
          intro u v hadj _ hvW hvX hout_u
          have hcap_uv : (splitNet G m s3).cap (outIdx u) (inIdx v) = n + 1 := by
            unfold splitNet
            dsimp only [outIdx, inIdx]
            have h4 : n + 2 ≤ v.1 + 2 + n ∧ v.1 + 2 + n < splitCount n ∧
                2 ≤ v.1 + 2 ∧ v.1 + 2 < n + 2 := by dsimp only [splitCount]; omega
            have h4' : n + 2 ≤ u.1 + n + 2 ∧ u.1 + n + 2 < splitCount n ∧
                2 ≤ v.1 + 2 ∧ v.1 + 2 < n + 2 := by dsimp only [splitCount]; omega
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              dite_eq_left h4']
            have hu_eq : (⟨u.1 + n + 2 - (n + 2), by dsimp only [splitCount] at h4'; omega⟩ :
                Fin n) = u := Fin.ext (by dsimp only; omega)
            have hv_eq : (⟨v.1 + 2 - 2, by omega⟩ : Fin n) = v := Fin.ext (by dsimp only; omega)
            simp only [hu_eq, hv_eq, hadj, ↓reduceIte]
          have hin_v : inIdx v ∈ C := by
            by_contra hnin
            have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hout_u hnin
            omega
          by_contra hnout
          exact hvX ((hX_iff v).mpr ⟨hvW, hin_v, hnout⟩)
        intro u v hadj huW hvW huX hvX
        dsimp only [side]
        exact decide_eq_decide.mpr ⟨hdir hadj huW hvW hvX, hdir hadj.symm hvW huW huX⟩
      have hkeep_side : ∀ v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
          (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀,
          v ∉ (X : Set (Fin n)) → side v = true := by
        intro v hv hvX
        have hvW : v ∉ Wset := (mem_keepTerminals.mp hv).1
        have hkeep1 : s3.mem (keepBase n + v.1) = 1 := by
          rw [(hs3_keep v).2, hdel_s2, hgcol_s2, hc₀_s2]
          exact hv
        have hcap_0v : (splitNet G m s3).cap (splitNet G m s3).s (inIdx v) = n + 1 := by
          unfold splitNet
          dsimp only [inIdx]
          rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel,
            ite_eq_left hkeep1]
        have hin_v : inIdx v ∈ C := by
          by_contra hnin
          have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hmin.1.1 hnin
          omega
        have hout_v : outIdx v ∈ C := by
          by_contra hnout
          exact hvX ((hX_iff v).mpr ⟨hvW, hin_v, hnout⟩)
        exact decide_eq_true hout_v
      have hflip_side : ∀ v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
          (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀,
          v ∉ (X : Set (Fin n)) → side v = false := by
        intro v hv _
        have hflip1 : s3.mem (flipBase n + v.1) = 1 := by
          rw [(hs3_flip v).2, hdel_s2, hgcol_s2, hc₀_s2]
          exact hv
        have hcap_v1 : (splitNet G m s3).cap (outIdx v) (splitNet G m s3).t = n + 1 := by
          unfold splitNet
          dsimp only [outIdx]
          rw [ite_eq_right (by omega), ite_eq_left rfl,
            ite_eq_left ⟨by omega, by dsimp only [splitCount]; omega⟩]
          have hsub : v.1 + n + 2 - (n + 2) = v.1 := by omega
          rw [hsub, ite_eq_left hflip1]
        have hout_v : outIdx v ∉ C := fun hout => by
          have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hout hmin.1.2
          omega
        exact decide_eq_false hout_v
      have hc'_W : ∀ v ∈ (Wset : Set (Fin n)), c' v = guessCol n s1 v := by
        intro v hvW
        rw [← hgcol_eq]
        exact hcW_t v hvW
      have hc'_notW : ∀ v ∉ (Wset : Set (Fin n)), c' v = (c₀ v == side v) := by
        intro v hvW
        have h := hcW'_t v hvW
        dsimp only [c', c₀, side]
        rw [h]
        simp only [hs5_eq]
        rw [hs4_s1 (colBase n + v.1) (by dsimp only [colBase, keepBase]; have := v.2; omega),
          hs1_low (colBase n + v.1) (by dsimp only [colBase, guessBase]; have := v.2; omega)]
        congr 1
        exact decide_eq_decide.mpr (hdist_iff (outIdx v))
      have hproper := proper_of_side (G := prefixGraph G m)
        (W := (Wset : Set (Fin n))) (D := (delSet Wset s1 : Set (Fin n)))
        (X := (X : Set (Fin n))) (c₀ := c₀) (σ := guessCol n s1) (side := side) (c := c')
        (fun u v hadj hu hv => hc₀_prop u v hadj hu hv)
        (fun u v hadj hu hv huD hvD => hprop u hu v hv hadj huD hvD)
        hside_edges hkeep_side hflip_side hc'_W hc'_notW
      intro u v hadj hu hv
      rw [hdel_eq] at hu hv
      exact hproper hadj (by simpa [Finset.coe_union] using hu)
        (by simpa [Finset.coe_union] using hv)
    · have hcond_rej : ¬ (sepCnt ≤ n ∧ (delSet Wset s4).card ≤ n ∧
          (delSet Wset s4).card + sepCnt ≤ k) := fun h => hsum_le h.2.2
      have hres0 : res = 0 := by
        change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 0
        unfold leafProg
        dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
        rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
          clientResult_bind, clientResult_bind, hdelCnt,
          ite_eq_right hcond_rej]
        rfl
      have ht_eq : t = s5 := by
        change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = s5
        unfold leafProg
        dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
        rw [clientState_bind, clientState_bind, hok1, ite_eq_left rfl, clientState_bind,
          clientState_bind, clientState_bind, hdelCnt,
          ite_eq_right hcond_rej]
        rfl
      refine ⟨by omega, hpres_base, fun _ a ha => ?_, fun h1 => absurd hres0 (by omega)⟩
      rw [ht_eq, hs5_eq, hs4_s1 a (by dsimp only [guessBase, keepBase] at ha ⊢; omega),
        hs1_low a ha]
  · have hok0 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 0 := by
      rw [hchk, ite_eq_right hprop]
    have hres0 : res = 0 := by
      change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 0
      unfold leafProg
      dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
      rw [clientResult_bind, clientResult_bind, hok0, ite_eq_right (by decide : ¬ (0 = 1))]
      rfl
    have ht_eq : t = s2 := by
      change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = s2
      unfold leafProg
      dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
      rw [clientState_bind, clientState_bind, hok0, ite_eq_right (by decide : ¬ (0 = 1))]
      rfl
    refine ⟨by omega, hpres_base, fun _ a ha => ?_, fun h1 => absurd hres0 (by omega)⟩
    rw [ht_eq, hs2_eq, hs1_low a ha]

private theorem leafProg_complete_at {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset T : Finset (Fin n)} {cT : Fin n → Bool} {s : Memory.State}
    (hG : MatrixLoaded G s) (hW : WListSpec Wset L s)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1))
    (hTk : T.card ≤ k)
    (hcT : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ T → v ∉ T → cT u ≠ cT v)
    (hdig_T : ∀ j : Fin L, s.mem (digitBase n + j.1) =
      if (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
      else if cT ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ then 2 else 1) :
    (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 1 := by
  have hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2 := by
    intro j hj
    rw [hdig_T ⟨j, hj⟩]
    split_ifs <;> decide
  set s1 := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
  obtain ⟨hs1_low, hg_eq, _, hg_le⟩ := unpackGuessProg_spec hW hdig
  have hG1 : MatrixLoaded G s1 := fun u v =>
    (hs1_low _ (by dsimp only [guessBase]; nlinarith [u.2, v.2])).trans (hG u v)
  have hW1 : WListSpec Wset L s1 :=
    hW.congr fun a _ ha => hs1_low a (by dsimp only [digitBase, guessBase] at ha ⊢; omega)
  have hg_eq1 : ∀ j : Fin L,
      s1.mem (guessBase n + s1.mem (wListBase n + j.1)) = s1.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs1_low (wListBase n + j.1) (by dsimp only [wListBase, guessBase]; omega),
      hs1_low (digitBase n + j.1) (by dsimp only [digitBase, guessBase]; omega)]
    exact hg_eq j
  have hcol01_1 : ∀ v : Fin n, s1.mem (colBase n + v.1) ≤ 1 := fun v =>
    (hs1_low _ (by dsimp only [colBase, guessBase]; omega)).trans_le (hcol01 v)
  have hgw : ∀ w ∈ Wset, s1.mem (guessBase n + w.1) =
      if w ∈ T then 0 else if cT w then 2 else 1 := by
    intro w hwW
    obtain ⟨j, hj⟩ := (hW.mem_iff_exists w).mp hwW
    have hjw : (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) = w := Fin.ext hj
    rw [← hj, hg_eq j, hdig_T j, hjw]
  have hdel_T : delSet Wset s1 = T ∩ Wset := by
    ext w
    simp only [delSet, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hwW, hg0⟩
      rw [hgw w hwW] at hg0
      by_cases hwT : w ∈ T
      · exact ⟨hwT, hwW⟩
      · rw [ite_eq_right hwT] at hg0; split_ifs at hg0
    · rintro ⟨hwT, hwW⟩
      exact ⟨hwW, by rw [hgw w hwW, ite_eq_left hwT]⟩
  have hσ_T : ∀ w ∈ Wset, w ∉ T → guessCol n s1 w = cT w := by
    intro w hwW hwT
    unfold guessCol
    rw [hgw w hwW, ite_eq_right hwT]
    cases cT w <;> rfl
  have hprop : ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
      u ∉ delSet Wset s1 → v ∉ delSet Wset s1 → guessCol n s1 u ≠ guessCol n s1 v := by
    intro u huW v hvW hadj huD hvD
    have huT : u ∉ T := fun h => huD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, huW⟩)
    have hvT : v ∉ T := fun h => hvD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hvW⟩)
    rw [hσ_T u huW huT, hσ_T v hvW hvT]
    exact hcT u v hadj huT hvT
  have hok1 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 1 := by
    rw [checkProperProg_spec (m := m) hG1 hW1 hg_eq1 hg_le, ite_eq_left hprop]
  set s2 := (Memory.spec 0).clientState s1 (checkProperProg ((n, m), L))
  have hs2_eq : ∀ a, s2.mem a = s1.mem a := fun a => preservesAt_checkProperProg a _ s1
  have hG2 : MatrixLoaded G s2 := fun u v => (hs2_eq _).trans (hG1 u v)
  have hW2 : WListSpec Wset L s2 := hW1.congr fun a _ _ => hs2_eq a
  have hcol01_2 : ∀ v : Fin n, s2.mem (colBase n + v.1) ≤ 1 :=
    fun v => (hs2_eq _).trans_le (hcol01_1 v)
  have hg_eq2 : ∀ j : Fin L,
      s2.mem (guessBase n + s2.mem (wListBase n + j.1)) = s2.mem (digitBase n + j.1) := by
    intro j; simp only [hs2_eq]; exact hg_eq1 j
  have hg_le2 : ∀ v : Fin n, s2.mem (guessBase n + v.1) ≤ 2 :=
    fun v => (hs2_eq _).trans_le (hg_le v)
  set s3 := (Memory.spec 0).clientState s2 (buildTerminalsProg ((n, m), L))
  obtain ⟨hs3_low, hs3_keep, hs3_flip⟩ :=
    buildTerminalsProg_spec (m := m) hG2 hW2 hcol01_2 hg_eq2 hg_le2
  have hG3 : MatrixLoaded G s3 := fun u v =>
    (hs3_low _ (by dsimp only [keepBase]; nlinarith [u.2, v.2])).trans (hG2 u v)
  set sepCnt := (Memory.spec 0).clientResult s3 (minSepProg (n, m))
  set s4 := (Memory.spec 0).clientState s3 (minSepProg (n, m))
  obtain ⟨hs4_low, C, hmin, _, _, _, hsepCnt_eq, hsepCnt_cap⟩ :=
    minSepProg_spec (m := m) hG3
  change sepCnt = (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card
    at hsepCnt_eq
  change sepCnt ≤ (splitNet G m s3).cutCapacity C at hsepCnt_cap
  have hs4_s1 : ∀ a < keepBase n, s4.mem a = s1.mem a := fun a ha =>
    (hs4_low a (by dsimp only [keepBase, flowBase] at ha ⊢; omega)).trans
      ((hs3_low a ha).trans (hs2_eq a))
  have hW4 : WListSpec Wset L s4 :=
    hW1.congr fun a _ ha => hs4_s1 a (by dsimp only [digitBase, keepBase] at ha ⊢; omega)
  have hg_eq4 : ∀ j : Fin L,
      s4.mem (guessBase n + s4.mem (wListBase n + j.1)) = s4.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs4_s1 (wListBase n + j.1) (by dsimp only [wListBase, keepBase]; omega),
      hs4_s1 (digitBase n + j.1) (by dsimp only [digitBase, keepBase]; omega),
      hs4_s1 (guessBase n + s1.mem (wListBase n + j.1))
        (by dsimp only [guessBase, keepBase]; have := hW1.entry_lt j.1 j.2; omega)]
    exact hg_eq1 j
  have hdelCnt : (Memory.spec 0).clientResult s4 (countDelProg (n, L)) =
      (delSet Wset s4).card := countDelProg_spec hW4 hg_eq4
  have hdel4_eq : delSet Wset s4 = T ∩ Wset := by
    rw [← hdel_T]
    ext w
    simp [delSet,
      hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
  let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.1) == 1
  have hc₀_s2 : (fun v : Fin n => s2.mem (colBase n + v.1) == 1) = c₀ := by
    funext v
    dsimp only [c₀]
    rw [hs2_eq, hs1_low (colBase n + v.1) (by dsimp only [colBase, guessBase]; have := v.2; omega)]
  have hdel_s2 : delSet Wset s2 = delSet Wset s1 := by ext w; simp [delSet, hs2_eq]
  have hgcol_s2 : guessCol n s2 = guessCol n s1 := by funext w; unfold guessCol; rw [hs2_eq]
  let N := splitNet G m s3
  let K : Finset (Fin (splitCount n)) := Finset.univ.filter fun x =>
    x.1 = 0 ∨
      (∃ v : Fin n, x = inIdx v ∧ (v ∈ Wset ∨ v ∈ T ∨ cT v = c₀ v)) ∨
      (∃ v : Fin n, x = outIdx v ∧ v ∉ Wset ∧ v ∉ T ∧ cT v = c₀ v)
  have hK_cut : N.IsCut K := by
    refine ⟨?_, ?_⟩
    · simp [K, N, splitNet]
    · intro h1K
      obtain ⟨_, h1_or⟩ := Finset.mem_filter.mp h1K
      dsimp only [N, splitNet, inIdx, outIdx] at h1_or
      rcases h1_or with h | ⟨v, hv, _⟩ | ⟨v, hv, _⟩
      · omega
      · have := congrArg Fin.val hv; dsimp only at this; omega
      · have := congrArg Fin.val hv; dsimp only at this; omega
  have hK_arcs : ∀ x ∈ K, ∀ y ∈ Finset.univ \ K,
      N.cap x y ≤ if ∃ v ∈ T \ Wset, x = inIdx v ∧ y = outIdx v then 1 else 0 := by
    intro x hx y hy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [K, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases hcap0 : N.cap x y = 0
    · rw [hcap0]; exact Nat.zero_le _
    · unfold N splitNet at hcap0 ⊢
      dsimp only at hcap0 ⊢
      by_cases hx0 : x.1 = 0
      · rw [ite_eq_left hx0] at hcap0 ⊢
        by_cases hy_in : 2 ≤ y.1 ∧ y.1 < n + 2
        · rw [ite_eq_left hy_in] at hcap0
          by_cases hk1 : s3.mem (keepBase n + (y.1 - 2)) = 1
          · exfalso
            let v : Fin n := ⟨y.1 - 2, by omega⟩
            have hy_eq : y = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
            have hkeep_v : v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
                (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀ := by
              have hk1' : s3.mem (keepBase n + v.1) = 1 := hk1
              rwa [(hs3_keep v).2, hdel_s2, hgcol_s2, hc₀_s2] at hk1'
            obtain ⟨hvW, w, hwW, hwD, hadj, hne⟩ := mem_keepTerminals.mp hkeep_v
            have hwT : w ∉ T := fun h =>
              hwD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hwW⟩)
            rw [hσ_T w hwW hwT] at hne
            by_cases hvT : v ∈ T
            · exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inl hvT)⟩))
            · have hc_ne := hcT w v hadj hwT hvT
              have hv_eq_c : cT v = c₀ v := by
                revert hne hc_ne
                cases cT w <;> cases cT v <;> cases c₀ v <;> decide
              exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inr hv_eq_c)⟩))
          · rw [ite_eq_right hk1] at hcap0; exact absurd rfl hcap0
        · rw [ite_eq_right hy_in] at hcap0; exact absurd rfl hcap0
      · rw [ite_eq_right hx0] at hcap0 ⊢
        by_cases hy1 : y.1 = 1
        · exfalso
          rw [ite_eq_left hy1] at hcap0
          by_cases hx_out : n + 2 ≤ x.1 ∧ x.1 < splitCount n
          · rw [ite_eq_left hx_out] at hcap0
            let v : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at hx_out; omega⟩
            have hx_eq : x = outIdx v := Fin.ext (by dsimp only [v, outIdx]; omega)
            have hxK : v ∉ Wset ∧ v ∉ T ∧ cT v = c₀ v := by
              rcases hx with h0 | ⟨u, hu, _⟩ | ⟨u, hu, hu_p⟩
              · exact absurd h0 hx0
              · have := congrArg Fin.val hu; dsimp only [inIdx] at this; omega
              · have huv : u = v := Fin.ext (by
                  have := congrArg Fin.val (hx_eq.symm.trans hu)
                  dsimp only [outIdx] at this; omega)
                rwa [← huv]
            by_cases hf1 : s3.mem (flipBase n + v.1) = 1
            · have hflip_v : v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
                  (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀ := by
                rwa [(hs3_flip v).2, hdel_s2, hgcol_s2, hc₀_s2] at hf1
              obtain ⟨_, w, hwW, hwD, hadj, heq⟩ := mem_flipTerminals.mp hflip_v
              have hwT : w ∉ T := fun h =>
                hwD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hwW⟩)
              rw [hσ_T w hwW hwT] at heq
              exact hcT w v hadj hwT hxK.2.1 (heq.trans hxK.2.2.symm)
            · exact hcap0 (ite_eq_right hf1)
          · rw [ite_eq_right hx_out] at hcap0; exact absurd rfl hcap0
        · rw [ite_eq_right hy1] at hcap0 ⊢
          by_cases hx_in : 2 ≤ x.1 ∧ x.1 < n + 2
          · rw [ite_eq_left hx_in] at hcap0 ⊢
            by_cases hy_add : y.1 = x.1 + n
            · rw [ite_eq_left hy_add] at hcap0 ⊢
              let v : Fin n := ⟨x.1 - 2, by omega⟩
              have hx_eq : x = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
              have hy_eq : y = outIdx v := Fin.ext (by dsimp only [v, outIdx]; omega)
              by_cases hw0 : s3.mem (wBase n + v.1) = 0
              · rw [ite_eq_left hw0]
                have hvW : v ∉ Wset := by
                  rw [hs3_low _ (by dsimp only [wBase, keepBase]; omega), hs2_eq,
                    hs1_low _ (by dsimp only [wBase, guessBase]; omega), hW.w_mem v] at hw0
                  by_cases h : v ∈ Wset <;> simp [h] at hw0 ⊢
                have hxK : v ∈ Wset ∨ v ∈ T ∨ cT v = c₀ v := by
                  rcases hx with h0 | ⟨u, hu, hu_p⟩ | ⟨u, hu, _⟩
                  · exact absurd h0 hx0
                  · have huv : u = v := inIdx_injective n (hu.symm.trans hx_eq)
                    rwa [← huv]
                  · have := congrArg Fin.val hu; dsimp only [outIdx] at this; omega
                have hvT : v ∈ T := by
                  rcases hxK with hW' | hT' | hc_eq
                  · exact absurd hW' hvW
                  · exact hT'
                  · by_contra hvT'
                    exact hy (Or.inr (Or.inr ⟨v, hy_eq, hvW, hvT', hc_eq⟩))
                have hex : ∃ u ∈ T \ Wset, x = inIdx u ∧ y = outIdx u :=
                  ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvW⟩, hx_eq, hy_eq⟩
                rw [ite_eq_left hex]
              · exact absurd (ite_eq_right hw0) hcap0
            · rw [ite_eq_right hy_add] at hcap0; exact absurd rfl hcap0
          · exfalso
            rw [ite_eq_right hx_in] at hcap0
            by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2
            · rw [dite_eq_left h4] at hcap0
              let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h4; omega⟩
              let v : Fin n := ⟨y.1 - 2, by omega⟩
              have hx_eq : x = outIdx u := Fin.ext (by dsimp only [u, outIdx]; omega)
              have hy_eq : y = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
              by_cases hadj : (prefixGraph G m).Adj u v
              · have huK : u ∉ Wset ∧ u ∉ T ∧ cT u = c₀ u := by
                  rcases hx with h0 | ⟨z, hz, _⟩ | ⟨z, hz, hz_p⟩
                  · exact absurd h0 hx0
                  · have := congrArg Fin.val hz; dsimp only [inIdx] at this; omega
                  · have hzu : z = u := Fin.ext (by
                      have := congrArg Fin.val (hx_eq.symm.trans hz)
                      dsimp only [outIdx] at this; omega)
                    rwa [← hzu]
                have hvW : v ∉ Wset := fun h => hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inl h⟩))
                have hvT : v ∉ T := fun h => hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inl h)⟩))
                have hc0_ne := hc₀_prop u v hadj huK.1 hvW
                have hcT_ne := hcT u v hadj huK.2.1 hvT
                have hv_eq_c : cT v = c₀ v := by
                  have hcu := huK.2.2
                  change c₀ u ≠ c₀ v at hc0_ne
                  revert hcu hc0_ne hcT_ne
                  cases cT u <;> cases c₀ u <;> cases cT v <;> cases c₀ v <;> decide
                exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inr hv_eq_c)⟩))
              · exact hcap0 (ite_eq_right hadj)
            · rw [dite_eq_right h4] at hcap0; exact absurd rfl hcap0
  have hK_row : ∀ x ∈ K,
      (∑ y ∈ Finset.univ \ K, N.cap x y) ≤ if ∃ v ∈ T \ Wset, x = inIdx v then 1 else 0 := by
    intro x hx
    by_cases hex : ∃ v ∈ T \ Wset, x = inIdx v
    · rw [ite_eq_left hex]
      obtain ⟨v, hv, rfl⟩ := hex
      calc ∑ y ∈ Finset.univ \ K, N.cap (inIdx v) y
          ≤ ∑ y ∈ Finset.univ \ K,
              (if ∃ u ∈ T \ Wset, inIdx v = inIdx u ∧ y = outIdx u then 1 else 0) :=
            Finset.sum_le_sum fun y hy => hK_arcs (inIdx v) hx y hy
        _ ≤ ∑ _y ∈ ({outIdx v} : Finset (Fin (splitCount n))), 1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_zero, add_zero,
              Finset.card_singleton]
            refine Finset.card_le_one.mpr fun y₁ hy₁ y₂ hy₂ => ?_
            obtain ⟨_, u₁, _, hu₁, rfl⟩ := Finset.mem_filter.mp hy₁
            obtain ⟨_, u₂, _, hu₂, rfl⟩ := Finset.mem_filter.mp hy₂
            rw [← inIdx_injective n hu₁, ← inIdx_injective n hu₂]
        _ = 1 := by simp
    · rw [ite_eq_right hex]
      refine le_of_eq (Finset.sum_eq_zero fun y hy => ?_)
      have hle := hK_arcs x hx y hy
      have hno : ¬ ∃ v ∈ T \ Wset, x = inIdx v ∧ y = outIdx v :=
        fun ⟨v, hv, hx_eq, _⟩ => hex ⟨v, hv, hx_eq⟩
      rw [ite_eq_right hno] at hle
      omega
  have hK_cap : N.cutCapacity K ≤ (T \ Wset).card := by
    calc N.cutCapacity K
        ≤ ∑ x ∈ K, (if ∃ v ∈ T \ Wset, x = inIdx v then 1 else 0) :=
          Finset.sum_le_sum hK_row
      _ = (K.filter fun x => ∃ v ∈ T \ Wset, x = inIdx v).card := by
          rw [Finset.sum_ite]; simp
      _ ≤ ((T \ Wset).image (inIdx (n := n))).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨_, v, hv, rfl⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      _ = (T \ Wset).card := Finset.card_image_of_injective _ (inIdx_injective n)
  have hsep_le_sdiff : sepCnt ≤ (T \ Wset).card :=
    hsepCnt_cap.trans ((hmin.2 K hK_cut).trans hK_cap)
  have hsum_T : (delSet Wset s4).card + sepCnt ≤ k := by
    rw [hdel4_eq, Finset.inter_comm]
    have hpart := Finset.card_inter_add_card_sdiff T Wset
    have : Wset ∩ T = T ∩ Wset := Finset.inter_comm Wset T
    rw [Finset.inter_comm] at hpart
    omega
  have hsep_le_n : sepCnt ≤ n := by
    rw [hsepCnt_eq]; exact (Finset.card_le_univ _).trans (by simp)
  have hdel_le_n : (delSet Wset s4).card ≤ n := (Finset.card_le_univ _).trans (by simp)
  unfold leafProg
  dsimp only [CompressCfg.n, CompressCfg.k, CompressCfg.m]
  rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
    clientResult_bind, clientResult_bind, hdelCnt,
    ite_eq_left ⟨hsep_le_n, hdel_le_n, hsum_T⟩, clientResult_bind, clientResult_pure]

private theorem eq_of_base3At_eq {m₁ m₂ : ℕ → ℕ} {base : ℕ} :
    ∀ {L : ℕ}, (∀ j < L, m₁ (base + j) ≤ 2) → (∀ j < L, m₂ (base + j) ≤ 2) →
      base3At m₁ base L = base3At m₂ base L →
      ∀ j < L, m₁ (base + j) = m₂ (base + j)
  | 0, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | L + 1, h1, h2, heq, j, hj => by
    rw [base3At, base3At] at heq
    have hm1 : min (m₁ (base + L)) 2 = m₁ (base + L) := Nat.min_eq_left (h1 L (by omega))
    have hm2 : min (m₂ (base + L)) 2 = m₂ (base + L) := Nat.min_eq_left (h2 L (by omega))
    rw [hm1, hm2] at heq
    have hlt1 := base3At_lt m₁ base L
    have hlt2 := base3At_lt m₂ base L
    have hd1 := h1 L (by omega)
    have hd2 := h2 L (by omega)
    have hd_eq : m₁ (base + L) = m₂ (base + L) := by
      rcases lt_trichotomy (m₁ (base + L)) (m₂ (base + L)) with hlt | hEq | hgt
      · exfalso
        have hmul : (m₁ (base + L) + 1) * 3 ^ L ≤ m₂ (base + L) * 3 ^ L :=
          Nat.mul_le_mul_right (3 ^ L) hlt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      · exact hEq
      · exfalso
        have hmul : (m₂ (base + L) + 1) * 3 ^ L ≤ m₁ (base + L) * 3 ^ L :=
          Nat.mul_le_mul_right (3 ^ L) hgt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
    have hpre_eq : base3At m₁ base L = base3At m₂ base L := by
      rw [hd_eq] at heq
      exact Nat.add_right_cancel heq
    by_cases hjL : j = L
    · subst hjL; exact hd_eq
    · exact eq_of_base3At_eq (fun i hi => h1 i (by omega)) (fun i hi => h2 i (by omega))
        hpre_eq j (by omega)

private theorem preservesAt_incOdomProg {a : ℕ} {d : ℕ × ℕ}
    (ha : a < digitBase d.1 ∨ digitBase d.1 + d.2 ≤ a) :
    PreservesAt a (incOdomProg d) := by
  unfold incOdomProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_fst 1 fun j hj carry => ⟨?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold incOdomStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
    refine preservesAt_ite _ ?_ ?_ <;>
      exact preservesAt_bind
        (preservesAt_write _ (by dsimp only [LoopAccArgs.idx, LoopAccArgs.acc] at ha hj ⊢; omega))
        fun _ => preservesAt_pure _ _
  · exact clientResult_incOdomStep_fst _ s

private theorem incOdomProg_digits_le (n L : ℕ) {s : Memory.State}
    (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2) :
    ∀ j < L, ((Memory.spec 0).clientState s (incOdomProg (n, L))).mem (digitBase n + j) ≤ 2 := by
  unfold incOdomProg
  rw [clientState_bind_read, clientState_bind, clientState_pure]
  have hinv := iterate_invariant_of incOdomStep n
    (fun rem (jc : ℕ × ℕ) st =>
      jc.1 + rem = L ∧ ∀ i < L, st.mem (digitBase n + i) ≤ 2)
    (fun rem jc st ⟨hjsum, hle⟩ => by
      unfold incOdomStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hc : jc.2 = 1
      · rw [ite_eq_left hc]
        by_cases hlt : st.mem (digitBase n + jc.1) < 2
        · rw [ite_eq_left hlt, clientResult_bind_write, clientState_bind_write]
          simp only [client_simps]
          refine ⟨by omega, fun i hi => ?_⟩
          by_cases hij : i = jc.1
          · subst hij; rw [Function.update_self]; omega
          · rw [Function.update_of_ne (by omega)]; exact hle i hi
        · rw [ite_eq_right hlt, clientResult_bind_write, clientState_bind_write]
          simp only [client_simps]
          refine ⟨by omega, fun i hi => ?_⟩
          by_cases hij : i = jc.1
          · subst hij; rw [Function.update_self]; decide
          · rw [Function.update_of_ne (by omega)]; exact hle i hi
      · rw [ite_eq_right hc]
        simp only [client_simps]
        exact ⟨by omega, hle⟩)
    (n := L) (a := (0, 1)) (s := s)
    ⟨Nat.zero_add _, hdig⟩
  exact hinv.2

/-- Soundness and completeness of the base-3 odometer compression search `compressProg`. -/
theorem compressProg_spec {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1)) :
    let res := (Memory.spec 0).clientResult s (compressProg (((n, k), m), L))
    let t := (Memory.spec 0).clientState s (compressProg (((n, k), m), L))
    (∀ a < sepBase n, t.mem a = s.mem a) ∧
      res ≤ 1 ∧
      (res = 1 → OctStateAt G m k t) ∧
      ((∃ T : Finset (Fin n), (prefixGraph G m).IsOddCycleTransversal (T : Set (Fin n)) ∧
        T.card ≤ k) → res = 1) := by
  intro res t
  set s1 := (Memory.spec 0).clientState s (fillRange ((digitBase n, 0), L))
  have hs1 := fillRange_spec (digitBase n) 0 L s
  have hbase3_s1 : base3At s1.mem (digitBase n) L = 0 := by
    have hzero_mem : ∀ k, base3At (fun _ => 0) (digitBase n) k = 0 := fun k => by
      induction k with
      | zero => rfl
      | succ j ih => unfold base3At; rw [ih]; simp
    exact (base3At_congr fun j hj => hs1.1 j hj).trans (hzero_mem L)
  have hs1_pre : ∀ a < digitBase n, s1.mem a = s.mem a := fun a ha => hs1.2 a (Or.inl ha)
  have hleaf_step : ∀ (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      (∀ a < wBase n, u.mem a = s.mem a) →
      let f' := (Memory.spec 0).clientResult u (leafProg (((n, k), m), L))
      let u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
      let u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
      MatrixLoaded G u ∧
        (∀ v : Fin n, u.mem (colBase n + v.1) ≤ 1) ∧
        (∀ x y : Fin n, (prefixGraph G m).Adj x y → x ∉ Wset → y ∉ Wset →
          (u.mem (colBase n + x.1) == 1) ≠ (u.mem (colBase n + y.1) == 1)) ∧
        f' ≤ 1 ∧
        (∀ a < sepBase n, u_odom.mem a = s.mem a) ∧
        WListSpec Wset L u_odom ∧
        (∀ j < L, u_odom.mem (digitBase n + j) ≤ 2) ∧
        (∀ a < digitBase n, u_odom.mem a = u_leaf.mem a) ∧
        base3At u_leaf.mem (digitBase n) L = base3At u.mem (digitBase n) L ∧
        (f' = 0 → ∀ a < digitBase n, u_leaf.mem a = u.mem a) ∧
        (f' = 1 → OctStateAt G m k u_odom) := by
    intro u hlow huW hdig hzero
    have huG : MatrixLoaded G u := fun x y =>
      (hlow _ (by dsimp only [sepBase]; nlinarith [x.2, y.2])).trans (hG x y)
    have hu_col01 : ∀ v : Fin n, u.mem (colBase n + v.1) ≤ 1 := fun v =>
      (hzero _ (by dsimp only [colBase, wBase]; omega)).trans_le (hcol01 v)
    have hu_c0 : ∀ x y : Fin n, (prefixGraph G m).Adj x y → x ∉ Wset → y ∉ Wset →
        (u.mem (colBase n + x.1) == 1) ≠ (u.mem (colBase n + y.1) == 1) := by
      intro x y hadj hx hy
      rw [hzero _ (by dsimp only [colBase, wBase]; omega),
        hzero _ (by dsimp only [colBase, wBase]; omega)]
      exact hc₀_prop x y hadj hx hy
    obtain ⟨hleaf_le, hleaf_pres, hleaf_0, hleaf_1⟩ :=
      leafProg_spec (k := k) huG huW hdig hu_col01 hu_c0
    set u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
    set u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
    have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u_leaf.mem a :=
      fun a ha => preservesAt_incOdomProg (Or.inl ha) u_leaf
    have hL_le := hW.card_le_n
    have hdig_eq : ∀ j < L, u_leaf.mem (digitBase n + j) = u.mem (digitBase n + j) := fun j hj =>
      hleaf_pres _ (Or.inr ⟨by dsimp only [wBase, digitBase]; omega,
        by dsimp only [digitBase, guessBase]; omega⟩)
    have hdig_leaf : ∀ j < L, u_leaf.mem (digitBase n + j) ≤ 2 := fun j hj =>
      (hdig_eq j hj).trans_le (hdig j hj)
    exact ⟨huG, hu_col01, hu_c0, hleaf_le,
      fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
        ((hleaf_pres a (Or.inl ha)).trans (hlow a ha)),
      huW.congr fun a ha1 ha2 => (hodom_pre a ha2).trans
        (hleaf_pres a (Or.inr ⟨ha1, by dsimp only [digitBase, guessBase] at ha2 ⊢; omega⟩)),
      incOdomProg_digits_le n L hdig_leaf,
      hodom_pre,
      base3At_congr hdig_eq,
      fun hf0 a ha => hleaf_0 hf0 a (by dsimp only [digitBase, guessBase] at ha ⊢; omega),
      fun hf1 => (hleaf_1 hf1).congr fun a _ ha2 =>
        hodom_pre a (by dsimp only [wBase, digitBase] at ha2 ⊢; omega)⟩
  have hloop_sound : ∀ rem (st : ℕ × ℕ) (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      st.2 ≤ 1 →
      (st.2 = 0 → ∀ a < wBase n, u.mem a = s.mem a) →
      (st.2 = 1 → OctStateAt G m k u) →
      let r_end := (Memory.spec 0).clientResult u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)
      let u_end := (Memory.spec 0).clientState u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)
      (∀ a < sepBase n, u_end.mem a = s.mem a) ∧
        r_end.2 ≤ 1 ∧
        (r_end.2 = 1 → OctStateAt G m k u_end) := by
    intro rem
    induction rem with
    | zero =>
      intro st u hlow huW _ hst2 _ hoct
      simp only [boundedWhile]
      exact ⟨hlow, hst2, hoct⟩
    | succ rem ih =>
      intro st u hlow huW hdig hst2 hzero_mem hoct
      unfold boundedWhile
      by_cases hg : st.1 = 0
      · simp only [hg, ↓reduceIte]
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
        dsimp only [guessStep, GuessStepArgs.n, GuessStepArgs.L, GuessStepArgs.found]
        rw [clientResult_bind_read, clientState_bind_read]
        by_cases hst2_0 : st.2 = 0
        · rw [ite_eq_left hst2_0, clientResult_bind, clientState_bind,
            clientResult_bind, clientResult_pure, clientState_bind, clientState_pure]
          obtain ⟨_, _, _, hleaf_le, hlow', huW', hdig', hodom_pre, _, hleaf_0, hoct'⟩ :=
            hleaf_step u hlow huW hdig (hzero_mem hst2_0)
          exact ih _ _ hlow' huW' hdig' hleaf_le
            (fun hf0 a ha => (hodom_pre a (by dsimp only [wBase, digitBase] at ha ⊢; omega)).trans
              ((hleaf_0 hf0 a (by dsimp only [wBase, digitBase] at ha ⊢; omega)).trans
                (hzero_mem hst2_0 a ha)))
            hoct'
        · have hst2_1 : st.2 = 1 := by omega
          rw [ite_eq_right hst2_0, pure_bind,
            clientResult_bind, clientResult_pure, clientState_bind, clientState_pure]
          set u_odom := (Memory.spec 0).clientState u (incOdomProg (n, L))
          have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u.mem a :=
            fun a ha => preservesAt_incOdomProg (Or.inl ha) u
          exact ih _ u_odom
            (fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
              (hlow a ha))
            (huW.congr fun a _ ha2 => hodom_pre a ha2)
            (incOdomProg_digits_le n L hdig)
            hst2
            (fun h0 => absurd hst2_1 (by omega))
            (fun _ => (hoct hst2_1).congr fun a _ ha2 =>
              hodom_pre a (by dsimp only [wBase, digitBase] at ha2 ⊢; omega))
      · simp only [hg, ↓reduceIte]
        exact ⟨hlow, hst2, hoct⟩
  have hs1_W : WListSpec Wset L s1 := hW.congr fun a _ ha => hs1_pre a ha
  have hs1_dig : ∀ j < L, s1.mem (digitBase n + j) ≤ 2 := fun j hj => by
    rw [hs1.1 j hj]; decide
  obtain ⟨hlow_fin, hres_le, hres_sound⟩ := hloop_sound (3 ^ L) (0, 0) s1
    (fun a ha => hs1_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega))
    hs1_W hs1_dig (by decide)
    (fun _ a ha => hs1_pre a (by dsimp only [wBase, digitBase] at ha ⊢; omega))
    (fun h => absurd h (by decide))
  have ht_eq : t = (Memory.spec 0).clientState s1
      (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) (3 ^ L) (0, 0)) := by
    change (Memory.spec 0).clientState s (compressProg (((n, k), m), L)) = _
    unfold compressProg
    dsimp only [CompressCfg.n]
    rw [StateTransitionSpec.clientState_bind, clientState_bind, clientState_pure]
  have hres_eq : res = ((Memory.spec 0).clientResult s1
      (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L)
        (3 ^ L) (0, 0))).2 := by
    change (Memory.spec 0).clientResult s (compressProg (((n, k), m), L)) = _
    unfold compressProg
    dsimp only [CompressCfg.n]
    rw [StateTransitionSpec.clientResult_bind, clientResult_bind, clientResult_pure]
  rw [ht_eq, hres_eq]
  refine ⟨hlow_fin, hres_le, hres_sound, ?_⟩
  rintro ⟨T, hToct, hTk⟩
  obtain ⟨cT, hcT⟩ := isOddCycleTransversal_iff_exists_bool.mp hToct
  let dgTarget : ℕ → ℕ := fun a =>
    if h : digitBase n ≤ a ∧ a - digitBase n < L then
      let w : Fin n := ⟨s.mem (wListBase n + (a - digitBase n)), hW.entry_lt _ h.2⟩
      if w ∈ T then 0 else if cT w then 2 else 1
    else 0
  have hdgTarget_at : ∀ j : Fin L, dgTarget (digitBase n + j.1) =
      if (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
      else if cT ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ then 2 else 1 := by
    intro j
    dsimp only [dgTarget]
    have hcond : digitBase n ≤ digitBase n + j.1 ∧ digitBase n + j.1 - digitBase n < L :=
      ⟨by omega, by have := j.2; omega⟩
    rw [dite_eq_left hcond]
    have hsub : digitBase n + j.1 - digitBase n = j.1 := Nat.add_sub_cancel_left _ _
    have hw_eq : (⟨s.mem (wListBase n + (digitBase n + j.1 - digitBase n)),
        hW.entry_lt _ hcond.2⟩ : Fin n) =
        ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ :=
      Fin.ext (by dsimp only; rw [hsub])
    rw [hw_eq]
  have hdgTarget_le : ∀ j < L, dgTarget (digitBase n + j) ≤ 2 := by
    intro j hj
    rw [hdgTarget_at ⟨j, hj⟩]
    split_ifs <;> decide
  let targetVal := base3At dgTarget (digitBase n) L
  have htarget_lt : targetVal < 3 ^ L := base3At_lt dgTarget (digitBase n) L
  have hloop_comp : ∀ rem (st : ℕ × ℕ) (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      st.2 ≤ 1 →
      (st.2 = 0 → ∀ a < digitBase n, u.mem a = s.mem a) →
      (st.1 = 0 → 3 ^ L ≤ base3At u.mem (digitBase n) L + rem) →
      (st.2 = 1 ∨ (st.1 = 0 ∧ base3At u.mem (digitBase n) L ≤ targetVal)) →
      ((Memory.spec 0).clientResult u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)).2 = 1 := by
    intro rem
    induction rem with
    | zero =>
      intro st u _ _ _ _ _ hbudget hor
      rcases hor with hfound1 | ⟨hg0, _⟩
      · unfold boundedWhile; simp only [client_simps]; exact hfound1
      · have hlt := base3At_lt u.mem (digitBase n) L
        have := hbudget hg0
        omega
    | succ rem ih =>
      intro st u hlow huW hdig hst2 hzero_mem hbudget hor
      unfold boundedWhile
      by_cases hg : st.1 = 0
      · simp only [hg, ↓reduceIte]
        rw [StateTransitionSpec.clientResult_bind]
        dsimp only [guessStep, GuessStepArgs.n, GuessStepArgs.L, GuessStepArgs.found]
        rw [clientResult_bind_read, clientState_bind_read]
        by_cases hst2_0 : st.2 = 0
        · rw [ite_eq_left hst2_0, clientResult_bind, clientState_bind,
            clientResult_bind, clientResult_pure, clientState_bind, clientState_pure]
          obtain ⟨huG, hu_col01, hu_c0, hleaf_le, hlow', huW', hdig', hodom_pre, hbase_leaf,
              hleaf_0, _⟩ :=
            hleaf_step u hlow huW hdig
              (fun a ha => hzero_mem hst2_0 a (by dsimp only [wBase, digitBase] at ha ⊢; omega))
          set u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
          set f' := (Memory.spec 0).clientResult u (leafProg (((n, k), m), L))
          set done' := (Memory.spec 0).clientResult u_leaf (incOdomProg (n, L))
          set u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
          have hodom := incOdomProg_base3At n L u_leaf
          change done' ≤ 1 ∧ base3At u_odom.mem (digitBase n) L + done' * 3 ^ L =
              base3At u_leaf.mem (digitBase n) L + 1 at hodom
          obtain ⟨hdone_le, hodom_eq⟩ := hodom
          rw [hbase_leaf] at hodom_eq
          have hbud := hbudget hg
          have hle_tar : base3At u.mem (digitBase n) L ≤ targetVal :=
            (hor.resolve_left (by omega)).2
          refine ih (done', f') u_odom hlow' huW' hdig' hleaf_le
            (fun hf0 a ha => (hodom_pre a ha).trans
              ((hleaf_0 hf0 a ha).trans (hzero_mem hst2_0 a ha)))
            (fun hd0 => by dsimp only at hd0; rw [hd0, zero_mul, add_zero] at hodom_eq; omega)
            ?_
          dsimp only
          by_cases hf1 : f' = 1
          · exact Or.inl hf1
          · have hf0 : f' = 0 := by omega
            by_cases heq_tar : base3At u.mem (digitBase n) L = targetVal
            · exfalso
              have hdig_eq := eq_of_base3At_eq hdig hdgTarget_le heq_tar
              have hdig_u : ∀ j : Fin L, u.mem (digitBase n + j.1) =
                  if (⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
                  else if cT ⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ then 2 else 1 := by
                intro j
                have hL_le := hW.card_le_n
                have hwl_u : u.mem (wListBase n + j.1) = s.mem (wListBase n + j.1) :=
                  hzero_mem hst2_0 _ (by dsimp only [wListBase, digitBase]; omega)
                have hfin_eq : (⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ : Fin n) =
                    ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ := Fin.ext hwl_u
                rw [hdig_eq j.1 j.2, hdgTarget_at j, hfin_eq]
              have hf1' : f' = 1 :=
                leafProg_complete_at (k := k) huG huW hu_col01 hu_c0 hTk hcT hdig_u
              omega
            · have hlt_tar : base3At u.mem (digitBase n) L < targetVal := by omega
              have hd0 : done' = 0 := by
                by_contra hne0
                have hd1 : done' = 1 := by omega
                rw [hd1, one_mul] at hodom_eq
                dsimp only [targetVal] at hlt_tar htarget_lt
                omega
              refine Or.inr ⟨hd0, ?_⟩
              rw [hd0, zero_mul, add_zero] at hodom_eq
              dsimp only [targetVal] at hlt_tar ⊢
              omega
        · have hst2_1 : st.2 = 1 := by omega
          rw [ite_eq_right hst2_0, pure_bind,
            clientResult_bind, clientResult_pure, clientState_bind, clientState_pure]
          set done' := (Memory.spec 0).clientResult u (incOdomProg (n, L))
          set u_odom := (Memory.spec 0).clientState u (incOdomProg (n, L))
          have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u.mem a :=
            fun a ha => preservesAt_incOdomProg (Or.inl ha) u
          have hodom := incOdomProg_base3At n L u
          change done' ≤ 1 ∧ base3At u_odom.mem (digitBase n) L + done' * 3 ^ L =
              base3At u.mem (digitBase n) L + 1 at hodom
          obtain ⟨_, hodom_eq⟩ := hodom
          have hbud := hbudget hg
          exact ih (done', st.2) u_odom
            (fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
              (hlow a ha))
            (huW.congr fun a _ ha2 => hodom_pre a ha2)
            (incOdomProg_digits_le n L hdig)
            hst2
            (fun h0 => absurd hst2_1 (by omega))
            (fun hd0 => by dsimp only at hd0; rw [hd0, zero_mul, add_zero] at hodom_eq; omega)
            (Or.inl hst2_1)
      · rcases hor with hfound1 | ⟨hg0, _⟩
        · simp only [hg, ↓reduceIte, client_simps]; exact hfound1
        · exact absurd hg0 hg
  exact hloop_comp (3 ^ L) (0, 0) s1
    (fun a ha => hs1_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega))
    hs1_W hs1_dig (by decide)
    (fun _ a ha => hs1_pre a ha)
    (fun _ => by rw [hbase3_s1, zero_add])
    (Or.inr ⟨rfl, by rw [hbase3_s1]; exact Nat.zero_le _⟩)

end Cslib.Algorithms.WordRAM.OddCycleTransversal
