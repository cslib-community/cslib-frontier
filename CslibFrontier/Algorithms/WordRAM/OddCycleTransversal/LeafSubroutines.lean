/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.CompressProg
import Mathlib.Tactic.Linarith

/-!
# Functional specifications for the compression-leaf subroutines

This module certifies each step invoked inside `leafProg` (`buildWProg`, `unpackGuessProg`,
`checkProperProg`, `buildTerminalsProg`, `countDelProg`, `commitLeafProg`). It does not depend on
`MinSep` or `Validity`, so all three verification modules build in parallel.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.WListSpec`: compacted candidate-set invariant.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.delSet`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.guessCol`: decoded deletion set and colouring.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.buildWProg_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.unpackGuessProg_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.checkProperProg_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.buildTerminalsProg_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.countDelProg_spec`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.commitLeafProg_spec`: functional specifications of
  the compression-leaf subroutines.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph SimpleGraph.OddCycleTransversal
open Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write StateTransitionSpec.clientState_map

/-! ### Compression leaf, base-3 odometer, and iterative compression correctness -/

/-- Invariant relating indicator array `wBase` to the sorted compacted list `wListBase`. -/
structure WListSpec {n : ℕ} (Wset : Finset (Fin n)) (L : ℕ) (s : Memory.State) : Prop where
  /-- Compacted list length equals `Wset.card`. -/
  card_eq : L = Wset.card
  /-- Indicator word at `wBase n + v.1` matches membership `v ∈ Wset`. -/
  w_mem : ∀ v : Fin n, s.mem (wBase n + v.val) = if v ∈ Wset then 1 else 0
  /-- Every `wListBase` entry is a valid vertex index `< n`. -/
  entry_lt : ∀ j < L, s.mem (wListBase n + j) < n
  /-- Every `wListBase` entry belongs to `Wset`. -/
  entry_mem : ∀ j : Fin L, ⟨s.mem (wListBase n + j.val), entry_lt j.val j.isLt⟩ ∈ Wset
  /-- Entries of `wListBase` are strictly increasing. -/
  entry_strictMono : ∀ i j, i < j → j < L → s.mem (wListBase n + i) < s.mem (wListBase n + j)
  /-- Every `w ∈ Wset` appears in `wListBase` at some index `j : Fin L`. -/
  mem_iff_exists : ∀ w : Fin n, w ∈ Wset ↔ ∃ j : Fin L, s.mem (wListBase n + j.val) = w.val

theorem WListSpec.congr {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s₁ s₂ : Memory.State}
    (hW : WListSpec Wset L s₁)
    (heq : ∀ a, wBase n ≤ a → a < digitBase n → s₂.mem a = s₁.mem a) :
    WListSpec Wset L s₂ := by
  have hL_le : L ≤ n := by
    rw [hW.card_eq]
    exact Wset.card_le_univ.trans (by simp)
  have hw_eq : ∀ v : Fin n, s₂.mem (wBase n + v.val) = s₁.mem (wBase n + v.val) :=
    fun v => heq _ (by dsimp only [wBase]; omega) (by dsimp only [wBase, digitBase]; omega)
  have hwl_eq : ∀ j < L, s₂.mem (wListBase n + j) = s₁.mem (wListBase n + j) :=
    fun j hj => heq _ (by dsimp only [wBase, wListBase]; omega)
      (by dsimp only [wListBase, digitBase]; omega)
  refine ⟨hW.card_eq, fun v => (hw_eq v).trans (hW.w_mem v),
    fun j hj => (hwl_eq j hj).symm ▸ hW.entry_lt j hj,
    fun j => ?_,
    fun i j hij hj => by
      rw [hwl_eq i (hij.trans hj), hwl_eq j hj]
      exact hW.entry_strictMono i j hij hj,
    fun w => ?_⟩
  · have hm := hW.entry_mem j
    have he := hwl_eq j.val j.isLt
    convert hm using 1
    exact Fin.ext he
  · rw [hW.mem_iff_exists]
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (hwl_eq j.val j.isLt).trans hj⟩,
      fun ⟨j, hj⟩ => ⟨j, (hwl_eq j.val j.isLt).symm.trans hj⟩⟩

theorem WListSpec.card_le_n {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s : Memory.State}
    (hW : WListSpec Wset L s) : L ≤ n := by
  rw [hW.card_eq]
  exact Wset.card_le_univ.trans (by simp)

private theorem WListSpec.entry_inj {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s : Memory.State}
    (hW : WListSpec Wset L s) {i j : Fin L}
    (h : s.mem (wListBase n + i.val) = s.mem (wListBase n + j.val)) : i = j := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd h (ne_of_lt (hW.entry_strictMono i.val j.val hlt j.isLt))
  · exact Fin.ext heq
  · exact absurd h.symm (ne_of_lt (hW.entry_strictMono j.val i.val hgt i.isLt))

private theorem preservesAt_buildWProg {a : ℕ} {d : ℕ × ℕ} (ha : a < wBase d.1) :
    PreservesAt a (buildWProg d) := by
  unfold buildWProg
  refine preservesAt_bind (preservesAt_copyRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun vL => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold buildWListStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind (preservesAt_write _ (by dsimp only [wBase, wListBase] at ha ⊢; omega))
    fun _ => preservesAt_pure _ _

/-- `buildWProg` forms `W = S ∪ {m}` and compacts it into `wListBase` satisfying `WListSpec`. -/
theorem buildWProg_spec {n m : ℕ} (hm : m < n) {s : Memory.State}
    (hsep01 : ∀ v : Fin n, s.mem (sepBase n + v.val) ≤ 1) :
    let S : Finset (Fin n) := Finset.univ.filter fun v => s.mem (sepBase n + v.val) = 1
    let Wset : Finset (Fin n) := insert ⟨m, hm⟩ S
    let L := (Memory.spec 0).clientResult s (buildWProg (n, m))
    let t := (Memory.spec 0).clientState s (buildWProg (n, m))
    (∀ a < wBase n, t.mem a = s.mem a) ∧ WListSpec Wset L t := by
  intro S Wset L t
  refine ⟨fun a ha => preservesAt_buildWProg ha s, ?_⟩
  set s1 := (Memory.spec 0).clientState s (copyRange ((sepBase n, wBase n), n))
  have hs1 := copyRange_spec (srcB := sepBase n) (dstB := wBase n) (len := n)
    (by dsimp only [sepBase, wBase]; omega) s
  set s2 : Memory.State := ⟨Function.update s1.mem (wBase n + m) 1, s1.frontier⟩
  have hs2_w : ∀ v : Fin n, s2.mem (wBase n + v.val) = if v ∈ Wset then 1 else 0 := by
    intro v
    dsimp only [s2]
    by_cases hvm : v.val = m
    · have hvW : v ∈ Wset := by
        have hveq : v = ⟨m, hm⟩ := Fin.ext hvm
        subst hveq
        exact Finset.mem_insert_self _ _
      rw [hvm, Function.update_self, ite_eq_left hvW]
    · have hne_m : v ≠ ⟨m, hm⟩ := fun h => hvm (congrArg Fin.val h)
      rw [Function.update_of_ne (by omega), hs1.1 v.val v.isLt]
      have hv01 := hsep01 v
      have hmemW : v ∈ Wset ↔ s.mem (sepBase n + v.val) = 1 := by
        simp [Wset, S, hne_m]
      by_cases h1 : s.mem (sepBase n + v.val) = 1
      · rw [h1, ite_eq_left (hmemW.mpr h1)]
      · rw [ite_eq_right (fun h => h1 (hmemW.mp h))]; omega
  have hiter := iterate_invariant_of buildWListStep n
    (fun rem (vL : ℕ × ℕ) st =>
      vL.1 + rem = n ∧
      (∀ a < wListBase n, st.mem a = s2.mem a) ∧
      vL.2 = (Wset.filter fun w => w.val < vL.1).card ∧
      (∀ j < vL.2, st.mem (wListBase n + j) < vL.1 ∧
        ∃ w ∈ Wset, st.mem (wListBase n + j) = w.val) ∧
      (∀ i j, i < j → j < vL.2 → st.mem (wListBase n + i) < st.mem (wListBase n + j)) ∧
      (∀ w ∈ Wset, w.val < vL.1 → ∃ j < vL.2, st.mem (wListBase n + j) = w.val))
    (fun rem vL st ⟨hvsum, hlow, hcard, hlt_mem, hmono, hex⟩ => by
      have hv_lt : vL.1 < n := by omega
      let vFin : Fin n := ⟨vL.1, hv_lt⟩
      have hwv : st.mem (wBase n + vL.1) = if vFin ∈ Wset then 1 else 0 :=
        (hlow _ (by dsimp only [wBase, wListBase]; omega)).trans (hs2_w vFin)
      have hL_le_v : vL.2 ≤ vL.1 := by
        rw [hcard]
        calc (Wset.filter fun w => w.val < vL.1).card
            ≤ ((Finset.univ : Finset (Fin n)).filter fun w => w.val < vL.1).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
          _ = ((Finset.range vL.1).attach.image
                fun x => (⟨x.val, (Finset.mem_range.mp x.property).trans hv_lt⟩ : Fin n)).card := by
              congr 1
              ext w
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                Finset.mem_attach]
              exact ⟨fun hw => ⟨⟨w.val, Finset.mem_range.mpr hw⟩, Fin.ext rfl⟩,
                fun ⟨⟨x, hx⟩, hwx⟩ => by subst hwx; exact Finset.mem_range.mp hx⟩
          _ ≤ (Finset.range vL.1).attach.card := Finset.card_image_le
          _ = vL.1 := by simp
      unfold buildWListStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      rw [clientResult_bind_read, clientState_bind_read, hwv]
      by_cases hvW : vFin ∈ Wset
      · rw [ite_eq_left hvW, ite_eq_left rfl, clientResult_bind_write, clientState_bind_write,
        clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, ?_, fun j hj => ?_,
          fun i j hij hj => ?_, fun w hw hlt => ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hlow a ha
        · have hfilt : (Wset.filter fun w => w.val < vL.1 + 1) =
              insert vFin (Wset.filter fun w => w.val < vL.1) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hwlt⟩
              by_cases hweq : w.val = vL.1
              · exact Or.inl (Fin.ext hweq)
              · exact Or.inr ⟨hw, by omega⟩
            · rintro (rfl | ⟨hw, hwlt⟩)
              · exact ⟨hvW, by dsimp only [vFin]; omega⟩
              · exact ⟨hw, by omega⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [vFin]), hcard]
        · by_cases hjL : j = vL.2
          · subst hjL
            rw [Function.update_self]
            exact ⟨by omega, vFin, hvW, rfl⟩
          · obtain ⟨hlt, w, hwW, hweq⟩ := hlt_mem j (by omega)
            rw [Function.update_of_ne (by omega)]
            exact ⟨by omega, w, hwW, hweq⟩
        · rw [Function.update_of_ne (by omega)]
          by_cases hjL : j = vL.2
          · subst hjL
            rw [Function.update_self]
            exact (hlt_mem i hij).1
          · rw [Function.update_of_ne (by omega)]
            exact hmono i j hij (by omega)
        · by_cases hweq : w.val = vL.1
          · exact ⟨vL.2, by omega, by rw [Function.update_self, hweq]⟩
          · obtain ⟨j, hj, hjw⟩ := hex w hw (by omega)
            exact ⟨j, by omega, (Function.update_of_ne (by omega) _ _).trans hjw⟩
      · rw [ite_eq_right hvW, ite_eq_right (by decide : ¬ (0 = 1)), clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, hlow, ?_,
          fun j hj => ⟨(hlt_mem j hj).1.trans (by omega), (hlt_mem j hj).2⟩, hmono,
          fun w hw hlt => ?_⟩
        · rw [hcard]
          symm
          congr 1
          ext w
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hw, hwlt⟩
            refine ⟨hw, ?_⟩
            by_cases hweq : w.val = vL.1
            · have : w = vFin := Fin.ext hweq; subst this; exact absurd hw hvW
            · omega
          · rintro ⟨hw, hwlt⟩
            exact ⟨hw, by omega⟩
        · by_cases hweq : w.val = vL.1
          · have : w = vFin := Fin.ext hweq; subst this; exact absurd hw hvW
          · exact hex w hw (by omega))
    (n := n) (a := (0, 0)) (s := s2)
    ⟨Nat.zero_add _, fun _ _ => rfl, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hvsum_end, hlow_end, hcard_end, hlt_mem_end, hmono_end, hex_end⟩ := hiter
  set s3 := (Memory.spec 0).clientState s2 (iterate buildWListStep n n (0, 0))
  set vL_end := (Memory.spec 0).clientResult s2 (iterate buildWListStep n n (0, 0))
  have hv1 : vL_end.1 = n := by omega
  rw [hv1] at hcard_end hlt_mem_end hex_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (buildWProg (n, m)) = s3
    unfold buildWProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind_write, clientState_bind,
      clientState_pure]
  have hL_eq : L = vL_end.2 := by
    change (Memory.spec 0).clientResult s (buildWProg (n, m)) = vL_end.2
    unfold buildWProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, clientResult_bind_write, clientResult_bind,
      clientResult_pure]
  rw [ht_eq, hL_eq]
  have hfilt_univ : (Wset.filter fun w => w.val < n) = Wset :=
    Finset.filter_eq_self.mpr fun w _ => w.isLt
  rw [hfilt_univ] at hcard_end
  refine ⟨hcard_end,
    fun v => (hlow_end _ (by dsimp only [wBase, wListBase]; omega)).trans (hs2_w v),
    fun j hj => (hlt_mem_end j hj).1,
    fun j => ?_,
    hmono_end,
    fun w => ⟨fun hw => ?_, fun ⟨j, hj⟩ => ?_⟩⟩
  · obtain ⟨w, hwW, hweq⟩ := (hlt_mem_end j.val j.isLt).2
    have hfin : (⟨s3.mem (wListBase n + j.val), (hlt_mem_end j.val j.isLt).1⟩ : Fin n) = w :=
      Fin.ext hweq
    rwa [hfin]
  · obtain ⟨j, hj, hjw⟩ := hex_end w hw w.isLt
    exact ⟨⟨j, hj⟩, hjw⟩
  · obtain ⟨w', hw'W, hw'eq⟩ := (hlt_mem_end j.val j.isLt).2
    have hweq : w = w' := Fin.ext (hj.symm.trans hw'eq)
    rwa [hweq]

/-- Deleted subset `D ⊆ W` encoded by the unpacked guess digits. -/
@[expose] def delSet {n : ℕ} (Wset : Finset (Fin n)) (s : Memory.State) : Finset (Fin n) :=
  Wset.filter fun w => s.mem (guessBase n + w.val) = 0

/-- Candidate `Bool` colouring encoded by the unpacked guess digits on `W \ D`. -/
@[expose] def guessCol (n : ℕ) (s : Memory.State) (w : Fin n) : Bool :=
  s.mem (guessBase n + w.val) == 2

theorem unpackGuessProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s) (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2) :
    let t := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
    (∀ a < guessBase n, t.mem a = s.mem a) ∧
      (∀ j : Fin L, t.mem (guessBase n + s.mem (wListBase n + j.val)) =
          s.mem (digitBase n + j.val)) ∧
      (∀ v : Fin n, v ∉ Wset → t.mem (guessBase n + v.val) = 0) ∧
      (∀ v : Fin n, t.mem (guessBase n + v.val) ≤ 2) := by
  intro t
  have hlow_all : ∀ a < guessBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_unpackGuessProg ha s
  refine ⟨hlow_all, ?_⟩
  set s1 := (Memory.spec 0).clientState s (fillRange ((guessBase n, 0), n))
  have hs1 := fillRange_spec (guessBase n) 0 n s
  have hiter := iterate_invariant_of unpackStep n
    (fun rem (j : ℕ) st =>
      j + rem = L ∧
      (∀ a < guessBase n, st.mem a = s.mem a) ∧
      (∀ i : Fin L, i.val < j →
        st.mem (guessBase n + s.mem (wListBase n + i.val)) = s.mem (digitBase n + i.val)) ∧
      (∀ v : Fin n, (∀ i : Fin L, i.val < j → s.mem (wListBase n + i.val) ≠ v.val) →
        st.mem (guessBase n + v.val) = 0) ∧
      (∀ v : Fin n, st.mem (guessBase n + v.val) ≤ 2))
    (fun rem j st ⟨hjsum, hst_low, hset, hzero, hle2⟩ => by
      have hj_lt : j < L := by omega
      let jFin : Fin L := ⟨j, hj_lt⟩
      have hL_le : L ≤ n := hW.card_le_n
      have hwv_eq : st.mem (wListBase n + j) = s.mem (wListBase n + j) :=
        hst_low _ (by dsimp only [wListBase, guessBase]; omega)
      have hdg_eq : st.mem (digitBase n + j) = s.mem (digitBase n + j) :=
        hst_low _ (by dsimp only [digitBase, guessBase]; omega)
      have hwv_lt : s.mem (wListBase n + j) < n := hW.entry_lt j hj_lt
      have hdg_le : s.mem (digitBase n + j) ≤ 2 := hdig j hj_lt
      unfold unpackStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hwv_eq, hdg_eq,
        ite_eq_left ⟨hwv_lt, hdg_le⟩, clientResult_bind_write, clientState_bind_write]
      simp only [client_simps]
      refine ⟨by omega, fun a ha => ?_, fun i hi => ?_, fun v hv => ?_, fun v => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hst_low a ha
      · by_cases hij : i.val = j
        · rw [hij, Function.update_self]
        · have hne_w : s.mem (wListBase n + i.val) ≠ s.mem (wListBase n + j) :=
            fun h => hij (congrArg Fin.val (hW.entry_inj (j := jFin) h))
          rw [Function.update_of_ne (fun h => hne_w (by omega))]
          exact hset i (by omega)
      · have hne_j : s.mem (wListBase n + j) ≠ v.val := hv jFin (Nat.lt_succ_self j)
        rw [Function.update_of_ne (fun h => hne_j (by omega))]
        exact hzero v fun i hi => hv i (by omega)
      · by_cases hv_eq : v.val = s.mem (wListBase n + j)
        · rw [hv_eq, Function.update_self]; exact hdg_le
        · rw [Function.update_of_ne (by omega)]; exact hle2 v)
    (n := L) (a := 0) (s := s1)
    ⟨Nat.zero_add _, fun a ha => hs1.2 a (Or.inl ha),
      fun _ h => absurd h (Nat.not_lt_zero _),
      fun v _ => hs1.1 v.val v.isLt,
      fun v => by rw [hs1.1 v.val v.isLt]; decide⟩
  obtain ⟨hjsum_end, _, hset_end, hzero_end, hle2_end⟩ := hiter
  set s2 := (Memory.spec 0).clientState s1 (iterate unpackStep n L 0)
  have hj_end : (Memory.spec 0).clientResult s1 (iterate unpackStep n L 0) = L := by omega
  rw [hj_end] at hset_end hzero_end
  have ht_eq : t = s2 := by
    change (Memory.spec 0).clientState s (unpackGuessProg (n, L)) = s2
    unfold unpackGuessProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind, clientState_pure]
  rw [ht_eq]
  refine ⟨fun j => hset_end j j.isLt, fun v hv => hzero_end v fun i _ h => hv ?_, hle2_end⟩
  exact (hW.mem_iff_exists v).mpr ⟨i, h⟩

theorem checkProperProg_spec {n m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.val)) = s.mem (digitBase n + j.val))
    (hg_le : ∀ v : Fin n, s.mem (guessBase n + v.val) ≤ 2) :
    (Memory.spec 0).clientResult s (checkProperProg ((n, m), L)) =
      if ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
          u ∉ delSet Wset s → v ∉ delSet Wset s → guessCol n s u ≠ guessCol n s v
      then 1 else 0 := by
  let BadPair (i j : Fin L) : Prop :=
    let u : Fin n := ⟨s.mem (wListBase n + i.val), hW.entry_lt i.val i.isLt⟩
    let v : Fin n := ⟨s.mem (wListBase n + j.val), hW.entry_lt j.val j.isLt⟩
    0 < s.mem (digitBase n + i.val) ∧ 0 < s.mem (digitBase n + j.val) ∧
      s.mem (digitBase n + i.val) = s.mem (digitBase n + j.val) ∧ (prefixGraph G m).Adj u v
  unfold checkProperProg
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]
  have hout := iterate_invariant_of properOuterStep ((n, m), L)
    (fun rem (iok : ℕ × ℕ) st =>
      iok.1 + rem = L ∧
      (∀ a, st.mem a = s.mem a) ∧
      iok.2 = if ∀ i j : Fin L, i.val < iok.1 → ¬ BadPair i j then 1 else 0)
    (fun rem iok st ⟨hisum, hmem_eq, hok_eq⟩ => by
      have hi_lt : iok.1 < L := by omega
      let iFin : Fin L := ⟨iok.1, hi_lt⟩
      let uFin : Fin n := ⟨s.mem (wListBase n + iok.1), hW.entry_lt iok.1 hi_lt⟩
      unfold properOuterStep
      dsimp only [ProperOuterArgs.n, ProperOuterArgs.m, ProperOuterArgs.L,
        ProperOuterArgs.i, ProperOuterArgs.ok]
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hmem_eq, hmem_eq]
      by_cases hdu : 0 < s.mem (digitBase n + iok.1)
      · rw [ite_eq_left ⟨uFin.isLt, hdu⟩, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        have hinn := iterate_invariant_of properInnerStep
          (((n, m), s.mem (wListBase n + iok.1)), s.mem (digitBase n + iok.1))
          (fun jrem (jok : ℕ × ℕ) st' =>
            jok.1 + jrem = L ∧
            (∀ a, st'.mem a = s.mem a) ∧
            jok.2 = if (∀ i j : Fin L, i.val < iok.1 → ¬ BadPair i j) ∧
              (∀ j : Fin L, j.val < jok.1 → ¬ BadPair iFin j) then 1 else 0)
          (fun jrem jok st' ⟨hjsum, hmem', hjok_eq⟩ => by
            have hj_lt : jok.1 < L := by omega
            let jFin : Fin L := ⟨jok.1, hj_lt⟩
            let vFin : Fin n := ⟨s.mem (wListBase n + jok.1), hW.entry_lt jok.1 hj_lt⟩
            unfold properInnerStep
            dsimp only [ProperInnerArgs.n, ProperInnerArgs.m, ProperInnerArgs.u,
              ProperInnerArgs.du, ProperInnerArgs.j, ProperInnerArgs.ok]
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
              clientState_bind_read, hmem', hmem']
            by_cases hcond : s.mem (wListBase n + iok.1) < n ∧
                s.mem (wListBase n + jok.1) < n ∧
                s.mem (wListBase n + iok.1) < m ∧
                s.mem (wListBase n + jok.1) < m ∧
                0 < s.mem (digitBase n + jok.1) ∧
                s.mem (digitBase n + iok.1) = s.mem (digitBase n + jok.1)
            · rw [ite_eq_left hcond, clientResult_bind_read, clientState_bind_read, hmem']
              have hmat := hG uFin vFin
              dsimp only [uFin, vFin] at hmat
              rw [hmat]
              by_cases hadj : G.Adj uFin vFin
              · have hbad : BadPair iFin jFin :=
                  ⟨hdu, hcond.2.2.2.2.1, hcond.2.2.2.2.2, hadj, hcond.2.2.1, hcond.2.2.2.1⟩
                have hnot_all : ¬ ((∀ i j : Fin L, i.val < iok.1 → ¬ BadPair i j) ∧
                    (∀ j : Fin L, j.val < jok.1 + 1 → ¬ BadPair iFin j)) :=
                  fun h => h.2 jFin (by dsimp only [jFin]; omega) hbad
                rw [ite_eq_left hadj, ite_eq_left rfl]
                simp only [client_simps]
                exact ⟨by omega, hmem', (ite_eq_right hnot_all).symm⟩
              · have hnot_bad : ¬ BadPair iFin jFin := fun hb => hadj hb.2.2.2.1
                rw [ite_eq_right hadj, ite_eq_right (by decide : ¬ (0 = 1))]
                simp only [client_simps]
                refine ⟨by omega, hmem', ?_⟩
                rw [hjok_eq]
                congr 1
                exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, fun j hj => by
                    by_cases hjeq : j.val = jok.1
                    · have : j = jFin := Fin.ext hjeq; subst this; exact hnot_bad
                    · exact h2 j (by omega)⟩,
                  fun ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (by omega)⟩⟩
            · rw [ite_eq_right hcond]
              have hnot_bad : ¬ BadPair iFin jFin := fun hb =>
                hcond ⟨uFin.isLt, vFin.isLt, hb.2.2.2.2.1, hb.2.2.2.2.2, hb.2.1, hb.2.2.1⟩
              simp only [client_simps]
              refine ⟨by omega, hmem', ?_⟩
              rw [hjok_eq]
              congr 1
              exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, fun j hj => by
                  by_cases hjeq : j.val = jok.1
                  · have : j = jFin := Fin.ext hjeq; subst this; exact hnot_bad
                  · exact h2 j (by omega)⟩,
                fun ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (by omega)⟩⟩)
          (n := L) (a := (0, iok.2)) (s := st)
          ⟨Nat.zero_add _, hmem_eq, by
            rw [hok_eq]
            congr 1
            exact propext ⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, And.left⟩⟩
        obtain ⟨hjsum_end, hmem_end, hjok_end⟩ := hinn
        set res_in := (Memory.spec 0).clientResult st
          (iterate properInnerStep
            (((n, m), s.mem (wListBase n + iok.1)), s.mem (digitBase n + iok.1)) L (0, iok.2))
        have hj1 : res_in.1 = L := by omega
        rw [hj1] at hjok_end
        refine ⟨by omega, hmem_end, ?_⟩
        rw [hjok_end]
        congr 1
        exact propext ⟨fun ⟨h1, h2⟩ i j hi => by
            by_cases hieq : i.val = iok.1
            · have : i = iFin := Fin.ext hieq; subst this; exact h2 j j.isLt
            · exact h1 i j (by omega),
          fun h => ⟨fun i j hi => h i j (by omega),
            fun j _ => h iFin j (by dsimp only [iFin]; omega)⟩⟩
      · have hnot_cond : ¬ (s.mem (wListBase n + iok.1) < n ∧ 0 < s.mem (digitBase n + iok.1)) :=
          fun h => hdu h.2
        rw [ite_eq_right hnot_cond]
        simp only [client_simps]
        refine ⟨by omega, hmem_eq, ?_⟩
        rw [hok_eq]
        congr 1
        exact propext ⟨fun h i j hi => by
            by_cases hieq : i.val = iok.1
            · have : i = iFin := Fin.ext hieq; subst this; exact fun hb => hdu hb.1
            · exact h i j (by omega),
          fun h i j hi => h i j (by omega)⟩)
    (n := L) (a := (0, 1)) (s := s)
    ⟨Nat.zero_add _, fun _ => rfl, by simp⟩
  obtain ⟨hisum_end, _, hok_fin⟩ := hout
  set res_out := (Memory.spec 0).clientResult s (iterate properOuterStep ((n, m), L) L (0, 1))
  have hi1 : res_out.1 = L := by omega
  rw [hi1] at hok_fin
  rw [hok_fin]
  congr 1
  apply propext
  constructor
  · intro hno u huW v hvW hadj huD hvD hcol_eq
    obtain ⟨i, hi⟩ := (hW.mem_iff_exists u).mp huW
    obtain ⟨j, hj⟩ := (hW.mem_iff_exists v).mp hvW
    have hui : (⟨s.mem (wListBase n + i.val), hW.entry_lt i.val i.isLt⟩ : Fin n) = u := Fin.ext hi
    have hvj : (⟨s.mem (wListBase n + j.val), hW.entry_lt j.val j.isLt⟩ : Fin n) = v := Fin.ext hj
    have hgu : s.mem (digitBase n + i.val) = s.mem (guessBase n + u.val) := by
      rw [← hg_eq i, hi]
    have hgv : s.mem (digitBase n + j.val) = s.mem (guessBase n + v.val) := by
      rw [← hg_eq j, hj]
    have hdu0 : s.mem (guessBase n + u.val) ≠ 0 := fun h =>
      huD (Finset.mem_filter.mpr ⟨huW, h⟩)
    have hdv0 : s.mem (guessBase n + v.val) ≠ 0 := fun h =>
      hvD (Finset.mem_filter.mpr ⟨hvW, h⟩)
    have hdu_le := hg_le u
    have hdv_le := hg_le v
    have hdeq : s.mem (guessBase n + u.val) = s.mem (guessBase n + v.val) := by
      unfold guessCol at hcol_eq
      rcases (by omega : s.mem (guessBase n + u.val) = 1 ∨ s.mem (guessBase n + u.val) = 2)
          with h1 | h1 <;>
        rcases (by omega : s.mem (guessBase n + v.val) = 1 ∨ s.mem (guessBase n + v.val) = 2)
          with h2 | h2 <;>
        simp [h1, h2] at hcol_eq ⊢
    exact hno i j i.isLt ⟨by omega, by omega, by omega, by rwa [hui, hvj]⟩
  · intro hprop i j _ ⟨hdi, hdj, hdeq, hadj⟩
    let u : Fin n := ⟨s.mem (wListBase n + i.val), hW.entry_lt i.val i.isLt⟩
    let v : Fin n := ⟨s.mem (wListBase n + j.val), hW.entry_lt j.val j.isLt⟩
    have huW : u ∈ Wset := hW.entry_mem i
    have hvW : v ∈ Wset := hW.entry_mem j
    have hgu : s.mem (guessBase n + u.val) = s.mem (digitBase n + i.val) := hg_eq i
    have hgv : s.mem (guessBase n + v.val) = s.mem (digitBase n + j.val) := hg_eq j
    have huD : u ∉ delSet Wset s := fun h => by
      have := (Finset.mem_filter.mp h).2; omega
    have hvD : v ∉ delSet Wset s := fun h => by
      have := (Finset.mem_filter.mp h).2; omega
    exact hprop u huW v hvW hadj huD hvD (by unfold guessCol; rw [hgu, hgv, hdeq])

theorem buildTerminalsProg_spec {n m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.val) ≤ 1)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.val)) = s.mem (digitBase n + j.val))
    (hg_le : ∀ v : Fin n, s.mem (guessBase n + v.val) ≤ 2) :
    let t := (Memory.spec 0).clientState s (buildTerminalsProg ((n, m), L))
    let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.val) == 1
    (∀ a < keepBase n, t.mem a = s.mem a) ∧
      (∀ v : Fin n, t.mem (keepBase n + v.val) ≤ 1 ∧
        (t.mem (keepBase n + v.val) = 1 ↔
          v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
            (delSet Wset s : Set (Fin n)) (guessCol n s) c₀)) ∧
      (∀ v : Fin n, t.mem (flipBase n + v.val) ≤ 1 ∧
        (t.mem (flipBase n + v.val) = 1 ↔
          v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
            (delSet Wset s : Set (Fin n)) (guessCol n s) c₀)) := by
  intro t c₀
  have hlow_all : ∀ a < keepBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_buildTerminalsProg ha s
  refine ⟨hlow_all, ?_⟩
  set s1 := (Memory.spec 0).clientState s (fillRange ((keepBase n, 0), n))
  have hs1 := fillRange_spec (keepBase n) 0 n s
  set s2 := (Memory.spec 0).clientState s1 (fillRange ((flipBase n, 0), n))
  have hs2 := fillRange_spec (flipBase n) 0 n s1
  have hs2_low : ∀ a < keepBase n, s2.mem a = s.mem a := fun a ha =>
    (hs2.2 a (Or.inl (by dsimp only [keepBase, flipBase] at ha ⊢; omega))).trans
      (hs1.2 a (Or.inl ha))
  have hs2_keep : ∀ v : Fin n, s2.mem (keepBase n + v.val) = 0 := fun v =>
    (hs2.2 _ (Or.inl (by dsimp only [keepBase, flipBase]; omega))).trans (hs1.1 v.val v.isLt)
  have hs2_flip : ∀ v : Fin n, s2.mem (flipBase n + v.val) = 0 := fun v => hs2.1 v.val v.isLt
  let KeepPred (v : Fin n) : Prop :=
    v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
      (delSet Wset s : Set (Fin n)) (guessCol n s) c₀
  let FlipPred (v : Fin n) : Prop :=
    v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
      (delSet Wset s : Set (Fin n)) (guessCol n s) c₀
  have hout := iterate_invariant_of termOuterStep ((n, m), L)
    (fun rem (v : ℕ) st =>
      v + rem = n ∧
      (∀ a < keepBase n, st.mem a = s.mem a) ∧
      (∀ x : Fin n, x.val < v →
        (st.mem (keepBase n + x.val) ≤ 1 ∧ (st.mem (keepBase n + x.val) = 1 ↔ KeepPred x)) ∧
        (st.mem (flipBase n + x.val) ≤ 1 ∧ (st.mem (flipBase n + x.val) = 1 ↔ FlipPred x))) ∧
      (∀ x : Fin n, v ≤ x.val →
        st.mem (keepBase n + x.val) = 0 ∧ st.mem (flipBase n + x.val) = 0))
    (fun rem v st ⟨hvsum, hst_low, hdone, hzero⟩ => by
      have hv_lt : v < n := by omega
      let vFin : Fin n := ⟨v, hv_lt⟩
      have hzv_eq : st.mem (wBase n + v) = s.mem (wBase n + v) :=
        hst_low _ (by dsimp only [wBase, keepBase]; omega)
      have hcv_eq : st.mem (colBase n + v) = s.mem (colBase n + v) :=
        hst_low _ (by dsimp only [colBase, keepBase]; omega)
      have hzv_W : s.mem (wBase n + v) = 0 ↔ vFin ∉ Wset := by
        rw [hW.w_mem vFin]
        by_cases h : vFin ∈ Wset <;> simp [h]
      unfold termOuterStep
      dsimp only [TermOuterArgs.n, TermOuterArgs.m, TermOuterArgs.L]
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hzv_eq, hcv_eq]
      by_cases hcond : s.mem (wBase n + v) = 0 ∧ v < m
      · rw [ite_eq_left hcond, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        have hv_notW : vFin ∉ Wset := hzv_W.mp hcond.1
        let KeepBefore (j : ℕ) : Prop :=
          ∃ idx : Fin L, idx.val < j ∧
            let u : Fin n := ⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩
            0 < s.mem (digitBase n + idx.val) ∧ (prefixGraph G m).Adj u vFin ∧
              guessCol n s u ≠ c₀ vFin
        let FlipBefore (j : ℕ) : Prop :=
          ∃ idx : Fin L, idx.val < j ∧
            let u : Fin n := ⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩
            0 < s.mem (digitBase n + idx.val) ∧ (prefixGraph G m).Adj u vFin ∧
              guessCol n s u = c₀ vFin
        have hinn := iterate_invariant_of termInnerStep ((n, m), (v, s.mem (colBase n + v)))
          (fun jrem (j : ℕ) st' =>
            j + jrem = L ∧
            (∀ a < keepBase n, st'.mem a = s.mem a) ∧
            (∀ x : Fin n, x ≠ vFin →
              st'.mem (keepBase n + x.val) = st.mem (keepBase n + x.val) ∧
              st'.mem (flipBase n + x.val) = st.mem (flipBase n + x.val)) ∧
            (st'.mem (keepBase n + v) ≤ 1 ∧ (st'.mem (keepBase n + v) = 1 ↔ KeepBefore j)) ∧
            (st'.mem (flipBase n + v) ≤ 1 ∧ (st'.mem (flipBase n + v) = 1 ↔ FlipBefore j)))
          (fun jrem j st' ⟨hjsum, hi_low, hi_other, hi_keep, hi_flip⟩ => by
            have hj_lt : j < L := by omega
            let jFin : Fin L := ⟨j, hj_lt⟩
            let uFin : Fin n := ⟨s.mem (wListBase n + j), hW.entry_lt j hj_lt⟩
            unfold termInnerStep
            dsimp only [TermInnerArgs.n, TermInnerArgs.m, TermInnerArgs.v, TermInnerArgs.cv]
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
              clientState_bind_read,
              hi_low _ (by dsimp only [wListBase, keepBase]; have := hW.card_le_n; omega),
              hi_low _ (by dsimp only [digitBase, keepBase]; have := hW.card_le_n; omega)]
            by_cases hicond : s.mem (wListBase n + j) < n ∧ v < n ∧
                s.mem (wListBase n + j) < m ∧ v < m ∧ 0 < s.mem (digitBase n + j)
            · rw [ite_eq_left hicond, clientResult_bind_read, clientState_bind_read,
                hi_low _ (by dsimp only [keepBase]; nlinarith [uFin.isLt, vFin.isLt])]
              have hmat := hG uFin vFin
              dsimp only [uFin, vFin] at hmat
              rw [hmat]
              by_cases hadj : G.Adj uFin vFin
              · have hp_adj : (prefixGraph G m).Adj uFin vFin :=
                  ⟨hadj, hicond.2.2.1, hicond.2.2.2.1⟩
                rw [ite_eq_left hadj, ite_eq_left rfl]
                have hgu : s.mem (guessBase n + uFin.val) = s.mem (digitBase n + j) := hg_eq jFin
                have hdu_le : s.mem (digitBase n + j) ≤ 2 := hgu ▸ hg_le uFin
                have hcv_le : s.mem (colBase n + v) ≤ 1 := hcol01 vFin
                have hcol_iff : s.mem (digitBase n + j) - 1 = s.mem (colBase n + v) ↔
                    guessCol n s uFin = c₀ vFin := by
                  unfold guessCol c₀
                  dsimp only [vFin]
                  rw [hgu]
                  have hdpos := hicond.2.2.2.2
                  rcases (by omega : s.mem (digitBase n + j) = 1 ∨ s.mem (digitBase n + j) = 2)
                      with hd | hd <;>
                    rcases (by omega : s.mem (colBase n + v) = 0 ∨ s.mem (colBase n + v) = 1)
                      with hc | hc <;>
                    simp [hd, hc]
                by_cases hsame : s.mem (digitBase n + j) - 1 = s.mem (colBase n + v)
                · have hsame' := hcol_iff.mp hsame
                  rw [ite_eq_left hsame, clientResult_bind_write, clientState_bind_write]
                  simp only [client_simps]
                  have hflip_succ : FlipBefore (j + 1) :=
                    ⟨jFin, by dsimp only [jFin]; omega, hicond.2.2.2.2, hp_adj, hsame'⟩
                  have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                    ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                        by_cases heq : idx.val = j
                        · have : idx = jFin := Fin.ext heq; subst this; exact absurd hsame' h3
                        · exact ⟨idx, by omega, h1, h2, h3⟩,
                      fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                  refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, ?_, ?_⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase] at ha ⊢; omega)]
                    exact hi_low a ha
                  · have hxv : x.val ≠ v := fun h => hx (Fin.ext h)
                    exact ⟨(Function.update_of_ne
                        (by dsimp only [keepBase, flipBase]; omega) _ _).trans (hi_other x hx).1,
                      (Function.update_of_ne (by omega) _ _).trans (hi_other x hx).2⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase]; omega),
                      hkeep_iff]
                    exact hi_keep
                  · rw [Function.update_self]
                    exact ⟨le_rfl, ⟨fun _ => hflip_succ, fun _ => rfl⟩⟩
                · have hdiff : guessCol n s uFin ≠ c₀ vFin := fun h => hsame (hcol_iff.mpr h)
                  rw [ite_eq_right hsame, clientResult_bind_write, clientState_bind_write]
                  simp only [client_simps]
                  have hkeep_succ : KeepBefore (j + 1) :=
                    ⟨jFin, by dsimp only [jFin]; omega, hicond.2.2.2.2, hp_adj, hdiff⟩
                  have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                    ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                        by_cases heq : idx.val = j
                        · have : idx = jFin := Fin.ext heq; subst this; exact absurd h3 hdiff
                        · exact ⟨idx, by omega, h1, h2, h3⟩,
                      fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                  refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, ?_, ?_⟩
                  · rw [Function.update_of_ne (by omega)]; exact hi_low a ha
                  · have hxv : x.val ≠ v := fun h => hx (Fin.ext h)
                    exact ⟨(Function.update_of_ne (by omega) _ _).trans (hi_other x hx).1,
                      (Function.update_of_ne
                        (by dsimp only [keepBase, flipBase]; omega) _ _).trans (hi_other x hx).2⟩
                  · rw [Function.update_self]
                    exact ⟨le_rfl, ⟨fun _ => hkeep_succ, fun _ => rfl⟩⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase]; omega),
                      hflip_iff]
                    exact hi_flip
              · rw [ite_eq_right hadj, ite_eq_right (by decide : ¬ (0 = 1))]
                simp only [client_simps]
                have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                  ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                      by_cases heq : idx.val = j
                      · have : idx = jFin := Fin.ext heq; subst this; exact absurd h2.1 hadj
                      · exact ⟨idx, by omega, h1, h2, h3⟩,
                    fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                  ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                      by_cases heq : idx.val = j
                      · have : idx = jFin := Fin.ext heq; subst this; exact absurd h2.1 hadj
                      · exact ⟨idx, by omega, h1, h2, h3⟩,
                    fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                refine ⟨by omega, hi_low, hi_other, ?_, ?_⟩
                · rw [hkeep_iff]; exact hi_keep
                · rw [hflip_iff]; exact hi_flip
            · rw [ite_eq_right hicond]
              simp only [client_simps]
              have hno_j : ¬ (0 < s.mem (digitBase n + j) ∧ (prefixGraph G m).Adj uFin vFin) :=
                fun ⟨hpos, hadj⟩ => hicond ⟨uFin.isLt, hv_lt, hadj.2.1, hadj.2.2, hpos⟩
              have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                    by_cases heq : idx.val = j
                    · have : idx = jFin := Fin.ext heq; subst this; exact absurd ⟨h1, h2⟩ hno_j
                    · exact ⟨idx, by omega, h1, h2, h3⟩,
                  fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
              have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                    by_cases heq : idx.val = j
                    · have : idx = jFin := Fin.ext heq; subst this; exact absurd ⟨h1, h2⟩ hno_j
                    · exact ⟨idx, by omega, h1, h2, h3⟩,
                  fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
              refine ⟨by omega, hi_low, hi_other, ?_, ?_⟩
              · rw [hkeep_iff]; exact hi_keep
              · rw [hflip_iff]; exact hi_flip)
          (n := L) (a := 0) (s := st)
          ⟨Nat.zero_add _, hst_low, fun _ _ => ⟨rfl, rfl⟩,
            by
              rw [(hzero vFin le_rfl).1]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide),
                fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩⟩,
            by
              rw [(hzero vFin le_rfl).2]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide),
                fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩⟩⟩
        obtain ⟨hjsum_end, hi_low_end, hi_other_end, hi_keep_end, hi_flip_end⟩ := hinn
        have hj_end : (Memory.spec 0).clientResult st
            (iterate termInnerStep ((n, m), (v, s.mem (colBase n + v))) L 0) = L := by omega
        rw [hj_end] at hi_keep_end hi_flip_end
        have hkeep_eq : KeepBefore L ↔ KeepPred vFin := by
          dsimp only [KeepPred]
          rw [mem_keepTerminals]
          constructor
          · rintro ⟨idx, _, hpos, hadj, hne⟩
            let u : Fin n := ⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩
            have huW : u ∈ Wset := hW.entry_mem idx
            have huD : u ∉ delSet Wset s := fun h => by
              have h0 : s.mem (guessBase n + s.mem (wListBase n + idx.val)) = 0 :=
                (Finset.mem_filter.mp h).2
              rw [hg_eq idx] at h0
              omega
            exact ⟨hv_notW, u, huW, huD, hadj, hne⟩
          · rintro ⟨_, u, huW, huD, hadj, hne⟩
            obtain ⟨idx, hidx⟩ := (hW.mem_iff_exists u).mp huW
            have hui :
                (⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩ : Fin n) = u :=
              Fin.ext hidx
            have hgu := hg_eq idx
            have hpos : 0 < s.mem (digitBase n + idx.val) := by
              rw [← hgu, hidx]
              have : s.mem (guessBase n + u.val) ≠ 0 := fun h =>
                huD (Finset.mem_filter.mpr ⟨huW, h⟩)
              omega
            exact ⟨idx, idx.isLt, hpos, by rwa [hui], by rwa [hui]⟩
        have hflip_eq : FlipBefore L ↔ FlipPred vFin := by
          dsimp only [FlipPred]
          rw [mem_flipTerminals]
          constructor
          · rintro ⟨idx, _, hpos, hadj, heq⟩
            let u : Fin n := ⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩
            have huW : u ∈ Wset := hW.entry_mem idx
            have huD : u ∉ delSet Wset s := fun h => by
              have h0 : s.mem (guessBase n + s.mem (wListBase n + idx.val)) = 0 :=
                (Finset.mem_filter.mp h).2
              rw [hg_eq idx] at h0
              omega
            exact ⟨hv_notW, u, huW, huD, hadj, heq⟩
          · rintro ⟨_, u, huW, huD, hadj, heq⟩
            obtain ⟨idx, hidx⟩ := (hW.mem_iff_exists u).mp huW
            have hui :
                (⟨s.mem (wListBase n + idx.val), hW.entry_lt idx.val idx.isLt⟩ : Fin n) = u :=
              Fin.ext hidx
            have hgu := hg_eq idx
            have hpos : 0 < s.mem (digitBase n + idx.val) := by
              rw [← hgu, hidx]
              have : s.mem (guessBase n + u.val) ≠ 0 := fun h =>
                huD (Finset.mem_filter.mpr ⟨huW, h⟩)
              omega
            exact ⟨idx, idx.isLt, hpos, by rwa [hui], by rwa [hui]⟩
        refine ⟨by omega, hi_low_end, fun x hx => ?_, fun x hx => ?_⟩
        · by_cases hxv : x.val = v
          · have hxeq : x = vFin := Fin.ext hxv
            subst hxeq
            exact ⟨⟨hi_keep_end.1, hi_keep_end.2.trans hkeep_eq⟩,
              ⟨hi_flip_end.1, hi_flip_end.2.trans hflip_eq⟩⟩
          · have hne : x ≠ vFin := fun h => hxv (congrArg Fin.val h)
            obtain ⟨⟨hk_le, hk_iff⟩, ⟨hf_le, hf_iff⟩⟩ := hdone x (by omega)
            obtain ⟨hk_eq, hf_eq⟩ := hi_other_end x hne
            exact ⟨⟨hk_eq.trans_le hk_le, by rw [hk_eq]; exact hk_iff⟩,
              ⟨hf_eq.trans_le hf_le, by rw [hf_eq]; exact hf_iff⟩⟩
        · have hne : x ≠ vFin := fun h => by subst h; dsimp only [vFin] at hx; omega
          exact ⟨(hi_other_end x hne).1.trans (hzero x (by omega)).1,
            (hi_other_end x hne).2.trans (hzero x (by omega)).2⟩
      · rw [ite_eq_right hcond]
        simp only [client_simps]
        have hno_keep : ¬ KeepPred vFin := fun h => by
          obtain ⟨hnW, u, _, _, hadj, _⟩ := mem_keepTerminals.mp h
          exact hcond ⟨hzv_W.mpr hnW, hadj.2.2⟩
        have hno_flip : ¬ FlipPred vFin := fun h => by
          obtain ⟨hnW, u, _, _, hadj, _⟩ := mem_flipTerminals.mp h
          exact hcond ⟨hzv_W.mpr hnW, hadj.2.2⟩
        refine ⟨by omega, hst_low, fun x hx => ?_, fun x hx => hzero x (by omega)⟩
        by_cases hxv : x.val = v
        · have hxeq : x = vFin := Fin.ext hxv
          subst hxeq
          exact ⟨by
              rw [(hzero vFin le_rfl).1]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide), fun h => absurd h hno_keep⟩⟩,
            by
              rw [(hzero vFin le_rfl).2]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide), fun h => absurd h hno_flip⟩⟩⟩
        · exact hdone x (by omega))
    (n := n) (a := 0) (s := s2)
    ⟨Nat.zero_add _, hs2_low, fun _ h => absurd h (Nat.not_lt_zero _),
      fun x _ => ⟨hs2_keep x, hs2_flip x⟩⟩
  obtain ⟨hvsum_end, _, hdone_end, _⟩ := hout
  set s3 := (Memory.spec 0).clientState s2 (iterate termOuterStep ((n, m), L) n 0)
  have hv_end : (Memory.spec 0).clientResult s2 (iterate termOuterStep ((n, m), L) n 0) = n := by
    omega
  rw [hv_end] at hdone_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (buildTerminalsProg ((n, m), L)) = s3
    unfold buildTerminalsProg
    dsimp only [GraphStepArgs.n]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_bind, clientState_pure]
  rw [ht_eq]
  exact ⟨fun v => (hdone_end v v.isLt).1, fun v => (hdone_end v v.isLt).2⟩

theorem countDelProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.val)) = s.mem (digitBase n + j.val)) :
    (Memory.spec 0).clientResult s (countDelProg (n, L)) = (delSet Wset s).card := by
  unfold countDelProg
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]
  have hiter := iterate_invariant_of countDelStep n
    (fun rem (jc : ℕ × ℕ) st =>
      jc.1 + rem = L ∧
      (∀ a, st.mem a = s.mem a) ∧
      jc.2 = ((Finset.univ : Finset (Fin L)).filter fun j =>
        j.val < jc.1 ∧ s.mem (digitBase n + j.val) = 0).card)
    (fun rem jc st ⟨hjsum, hmem_eq, hcnt⟩ => by
      have hj_lt : jc.1 < L := by omega
      let jFin : Fin L := ⟨jc.1, hj_lt⟩
      unfold countDelStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      rw [clientResult_bind_read, clientState_bind_read, hmem_eq]
      by_cases h0 : s.mem (digitBase n + jc.1) = 0
      · rw [ite_eq_left h0, clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, hmem_eq, ?_⟩
        have hfilt : ((Finset.univ : Finset (Fin L)).filter fun j =>
            j.val < jc.1 + 1 ∧ s.mem (digitBase n + j.val) = 0) =
            insert jFin (((Finset.univ : Finset (Fin L)).filter fun j =>
              j.val < jc.1 ∧ s.mem (digitBase n + j.val) = 0)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun ⟨hlt, hd⟩ => by
              by_cases hjeq : j.val = jc.1
              · exact Or.inl (Fin.ext hjeq)
              · exact Or.inr ⟨by omega, hd⟩,
            fun h => h.elim (fun h => by subst h; exact ⟨by dsimp only [jFin]; omega, h0⟩)
              fun ⟨hlt, hd⟩ => ⟨by omega, hd⟩⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp [jFin]), hcnt]
      · rw [ite_eq_right h0, clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, hmem_eq, ?_⟩
        rw [hcnt]
        symm
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨hlt, hd⟩ => by
            by_cases hjeq : j.val = jc.1
            · exact absurd (hjeq ▸ hd) h0
            · exact ⟨by omega, hd⟩,
          fun ⟨hlt, hd⟩ => ⟨by omega, hd⟩⟩)
    (n := L) (a := (0, 0)) (s := s)
    ⟨Nat.zero_add _, fun _ => rfl, by simp⟩
  obtain ⟨hjsum_end, _, hcnt_end⟩ := hiter
  set jc_end := (Memory.spec 0).clientResult s (iterate countDelStep n L (0, 0))
  have hj1 : jc_end.1 = L := by omega
  rw [hj1] at hcnt_end
  rw [hcnt_end]
  let fEmb : Fin L → Fin n := fun j => ⟨s.mem (wListBase n + j.val), hW.entry_lt j.val j.isLt⟩
  have hf_inj : Function.Injective fEmb := fun i j h => hW.entry_inj (congrArg Fin.val h)
  have himg : ((Finset.univ : Finset (Fin L)).filter fun j =>
      j.val < L ∧ s.mem (digitBase n + j.val) = 0).image fEmb = delSet Wset s := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, delSet]
    constructor
    · rintro ⟨j, ⟨_, hd0⟩, rfl⟩
      exact ⟨hW.entry_mem j, (hg_eq j).trans hd0⟩
    · rintro ⟨hwW, hg0⟩
      obtain ⟨j, hj⟩ := (hW.mem_iff_exists w).mp hwW
      exact ⟨j, ⟨j.isLt, (hg_eq j).symm.trans (hj.symm ▸ hg0)⟩, Fin.ext hj⟩
  rw [← himg, Finset.card_image_of_injective _ hf_inj]

theorem commitLeafProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.val) ≤ 1) :
    let t := (Memory.spec 0).clientState s (commitLeafProg n)
    let X : Finset (Fin n) := Finset.univ.filter fun v => s.mem (sepOutBase n + v.val) = 1
    (∀ a, (a < sepBase n ∨ wBase n ≤ a) → t.mem a = s.mem a) ∧
      (∀ v : Fin n, t.mem (sepBase n + v.val) = if v ∈ delSet Wset s ∪ X then 1 else 0) ∧
      (∀ v : Fin n, t.mem (colBase n + v.val) ≤ 1) ∧
      (∀ v ∈ Wset, (t.mem (colBase n + v.val) == 1) = guessCol n s v) ∧
      (∀ v : Fin n, v ∉ Wset →
        (t.mem (colBase n + v.val) == 1) =
          ((s.mem (colBase n + v.val) == 1) ==
            decide (s.mem (distBase n + (outIdx v).val) < splitCount n))) := by
  intro t X
  have hpres : ∀ a, (a < sepBase n ∨ wBase n ≤ a) → t.mem a = s.mem a :=
    fun a ha => preservesAt_commitLeafProg ha s
  refine ⟨hpres, ?_⟩
  let NewCol (v : Fin n) : ℕ :=
    if v ∈ Wset then
      if s.mem (guessBase n + v.val) = 2 then 1 else 0
    else if s.mem (distBase n + (outIdx v).val) < splitCount n then
      if s.mem (colBase n + v.val) = 1 then 1 else 0
    else
      if s.mem (colBase n + v.val) = 1 then 0 else 1
  have hiter := iterate_invariant_of commitStep n
    (fun rem (v : ℕ) st =>
      v + rem = n ∧
      (∀ a, (a < sepBase n ∨ wBase n ≤ a) → st.mem a = s.mem a) ∧
      (∀ u : Fin n, v ≤ u.val → st.mem (colBase n + u.val) = s.mem (colBase n + u.val)) ∧
      (∀ u : Fin n, u.val < v →
        st.mem (sepBase n + u.val) = (if u ∈ delSet Wset s ∪ X then 1 else 0) ∧
        st.mem (colBase n + u.val) = NewCol u))
    (fun rem v st ⟨hvsum, hst_out, hcol_ge, hdone⟩ => by
      have hv_lt : v < n := by omega
      let vFin : Fin n := ⟨v, hv_lt⟩
      have hwv : st.mem (wBase n + v) = s.mem (wBase n + v) :=
        hst_out _ (Or.inr (Nat.le_add_right _ _))
      have hgv : st.mem (guessBase n + v) = s.mem (guessBase n + v) :=
        hst_out _ (Or.inr (by dsimp only [wBase, guessBase]; omega))
      have hxv : st.mem (sepOutBase n + v) = s.mem (sepOutBase n + v) :=
        hst_out _ (Or.inr (by dsimp only [wBase, sepOutBase, parBase, distBase, flowBase]; omega))
      have hcv : st.mem (colBase n + v) = s.mem (colBase n + v) := hcol_ge vFin le_rfl
      have hdout : st.mem (distBase n + (v + n + 2)) = s.mem (distBase n + (outIdx vFin).val) :=
        hst_out _ (Or.inr (by dsimp only [wBase, distBase, flowBase]; omega))
      have hw_iff : s.mem (wBase n + v) = 1 ↔ vFin ∈ Wset := by
        rw [hW.w_mem vFin]; by_cases h : vFin ∈ Wset <;> simp [h]
      have hmem_UX : ((s.mem (wBase n + v) = 1 ∧ s.mem (guessBase n + v) = 0) ∨
          s.mem (sepOutBase n + v) = 1) ↔ vFin ∈ delSet Wset s ∪ X := by
        rw [Finset.mem_union, delSet, Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, hw_iff]
        rfl
      let sepVal : ℕ := if vFin ∈ delSet Wset s ∪ X then 1 else 0
      have hstep1 :
          (Memory.spec 0).clientState st (commitStep (n, v)) =
            ⟨Function.update (Function.update st.mem (sepBase n + v) sepVal)
              (colBase n + v) (NewCol vFin), st.frontier⟩ ∧
          (Memory.spec 0).clientResult st (commitStep (n, v)) = v + 1 := by
        unfold commitStep
        dsimp only [sepVal, NewCol]
        rw [clientState_bind_read, clientResult_bind_read, clientState_bind_read,
          clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
          clientState_bind_read, clientResult_bind_read, clientState_bind_read,
            clientResult_bind_read, hwv, hgv, hxv, hcv, hdout]
        by_cases hux : (s.mem (wBase n + v) = 1 ∧ s.mem (guessBase n + v) = 0) ∨
            s.mem (sepOutBase n + v) = 1 <;>
          by_cases hw1 : s.mem (wBase n + v) = 1
        · rw [ite_eq_left hux, ite_eq_left (hmem_UX.mp hux), clientState_bind_write,
          clientResult_bind_write,
            ite_eq_left hw1, ite_eq_left (hw_iff.mp hw1)]
          by_cases hg2 : s.mem (guessBase n + v) = 2
          · rw [ite_eq_left hg2, ite_eq_left hg2, clientState_bind_write, clientResult_bind_write]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hg2, ite_eq_right hg2, clientState_bind_write,
            clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_left hux, ite_eq_left (hmem_UX.mp hux), clientState_bind_write,
          clientResult_bind_write,
            ite_eq_right hw1, ite_eq_right (fun h => hw1 (hw_iff.mpr h))]
          by_cases hd : s.mem (distBase n + (outIdx vFin).val) < splitCount n <;>
            by_cases hc1 : s.mem (colBase n + v) = 1
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hux, ite_eq_right (fun h => hux (hmem_UX.mpr h)),
            clientState_bind_write, clientResult_bind_write, ite_eq_left hw1,
              ite_eq_left (hw_iff.mp hw1)]
          by_cases hg2 : s.mem (guessBase n + v) = 2
          · rw [ite_eq_left hg2, ite_eq_left hg2, clientState_bind_write, clientResult_bind_write]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hg2, ite_eq_right hg2, clientState_bind_write,
            clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hux, ite_eq_right (fun h => hux (hmem_UX.mpr h)),
            clientState_bind_write, clientResult_bind_write, ite_eq_right hw1,
            ite_eq_right (fun h => hw1 (hw_iff.mpr h))]
          by_cases hd : s.mem (distBase n + (outIdx vFin).val) < splitCount n <;>
            by_cases hc1 : s.mem (colBase n + v) = 1
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
      rw [hstep1.1, hstep1.2]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, fun u hu => ?_⟩
      · rw [Function.update_of_ne (by dsimp only [sepBase, colBase, wBase] at ha ⊢; omega),
          Function.update_of_ne (by dsimp only [sepBase, wBase] at ha ⊢; omega)]
        exact hst_out a ha
      · rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by dsimp only [sepBase, colBase]; omega)]
        exact hcol_ge u (by omega)
      · by_cases huv : u.val = v
        · have hueq : u = vFin := Fin.ext huv
          subst hueq
          dsimp only [vFin]
          exact ⟨by rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              Function.update_self],
            by rw [Function.update_self]⟩
        · refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; have := u.isLt; omega),
              Function.update_of_ne (by omega)]
            exact (hdone u (by omega)).1
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [sepBase, colBase]; have := u.isLt; omega)]
            exact (hdone u (by omega)).2)
    (n := n) (a := 0) (s := s)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hvsum_end, _, _, hdone_end⟩ := hiter
  set s1 := (Memory.spec 0).clientState s (iterate commitStep n n 0)
  have hv_end : (Memory.spec 0).clientResult s (iterate commitStep n n 0) = n := by omega
  rw [hv_end] at hdone_end
  have ht_eq : t = s1 := by
    change (Memory.spec 0).clientState s (commitLeafProg n) = s1
    unfold commitLeafProg
    rw [clientState_bind_read, clientState_bind, clientState_pure]
  rw [ht_eq]
  refine ⟨fun v => (hdone_end v v.isLt).1, fun v => ?_, fun v hvW => ?_, fun v hvW => ?_⟩
  · rw [(hdone_end v v.isLt).2]
    dsimp only [NewCol]
    split_ifs <;> decide
  · rw [(hdone_end v v.isLt).2]
    dsimp only [NewCol]
    rw [ite_eq_left hvW]
    unfold guessCol
    by_cases h : s.mem (guessBase n + v.val) = 2 <;> simp [h]
  · rw [(hdone_end v v.isLt).2]
    dsimp only [NewCol]
    rw [ite_eq_right hvW]
    have hc_le := hcol01 v
    by_cases hd : s.mem (distBase n + (outIdx v).val) < splitCount n <;>
      rcases (by omega : s.mem (colBase n + v.val) = 0 ∨
          s.mem (colBase n + v.val) = 1) with hc | hc <;>
      simp [hd, hc]

end Cslib.Algorithms.WordRAM.OddCycleTransversal
