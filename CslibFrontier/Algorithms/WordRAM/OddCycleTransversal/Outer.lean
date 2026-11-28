/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.CompressSpec
import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Cost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outer iterative-compression loop correctness and cost bound

This module proves the full end-to-end specification and `680 * 3 ^ k * (n + 1) ^ 5` memory-cost
bound (`octProg_spec_and_cost`) for `octProg ()` by induction over the `n` vertex-addition rounds.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.octProg_spec_and_cost`: correctness, memory output
  witness, and exact memory-cost upper bound for `octProg ()`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph SimpleGraph.OddCycleTransversal
open Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write StateTransitionSpec.clientState_map

/-! ### Outer vertex-addition loop and uniform Word-RAM program -/

private theorem memoryCost_buildWProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (buildWProg d) s ≤ 5 * (d.1 + 1) := by
  rcases d with ⟨n, m⟩
  dsimp only
  unfold buildWProg
  dsimp only
  have hstep : ∀ vL t, memoryCost (buildWListStep (n, vL)) t ≤ 2 := fun vL t => by
    unfold buildWListStep
    exact le_trans (memoryCost_bind_le (memoryCost_read _ t).le fun _ t' =>
      memoryCost_ite_le ((le_refl 1)) (Nat.zero_le _)) (by decide)
  have hcopy := memoryCost_copyRange_le ((sepBase n, wBase n), n) s
  exact le_trans (memoryCost_bind_le hcopy fun _ t1 =>
    memoryCost_bind_le (memoryCost_write _ _ t1).le fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of buildWListStep 2 n hstep n (0, 0) t2)
        fun _ t3 => (memoryCost_pure _ t3).le) (by dsimp only; omega)

private theorem iterate_inv_and_cost {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (c : ℕ) (d : δ) (Inv : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ rem a t, Inv (rem + 1) a t →
      memoryCost (body (d, a)) t ≤ c ∧
        Inv rem ((Memory.spec 0).clientResult t (body (d, a)))
          ((Memory.spec 0).clientState t (body (d, a)))) :
    ∀ m a s, Inv m a s →
      memoryCost (iterate body d m a) s ≤ c * m ∧
        Inv 0 ((Memory.spec 0).clientResult s (iterate body d m a))
          ((Memory.spec 0).clientState s (iterate body d m a))
  | 0, a, s, h => ⟨by simp [iterate], h⟩
  | m + 1, a, s, h => by
    obtain ⟨hc1, hinv1⟩ := hstep m a s h
    obtain ⟨hcm, hinvm⟩ := iterate_inv_and_cost body c d Inv hstep m _ _ hinv1
    dsimp only [iterate]
    refine ⟨?_, ?_⟩
    · rw [memoryCost_bind', Nat.mul_succ]
      omega
    · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      exact hinvm

private theorem octProg_cost_arith (n k : ℕ) :
    1 + (1 + ((octScratch n + 1) + (n + (n + 655 * 3 ^ k * (n + 1) ^ 4 * n)))) ≤
      680 * 3 ^ k * (n + 1) ^ 5 := by
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hscr_le : octScratch n + 1 ≤ 22 * (n + 1) ^ 5 := by
    unfold octScratch splitCount
    nlinarith [Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 5)]
  have hn_le : n ≤ (n + 1) ^ 5 := by
    have : n + 1 ≤ (n + 1) ^ 5 := by
      simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 5)
    omega
  have hmul_n : 655 * 3 ^ k * (n + 1) ^ 4 * n ≤ 655 * 3 ^ k * (n + 1) ^ 5 := by
    calc 655 * 3 ^ k * (n + 1) ^ 4 * n
        ≤ 655 * 3 ^ k * (n + 1) ^ 4 * (n + 1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ = 655 * 3 ^ k * (n + 1) ^ 5 := by ring
  have hp5_pos : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow 5 (n + 1) (Nat.succ_pos n)
  nlinarith

/-- End-to-end cost bound and functional correctness specification for `octProg ()`. -/
theorem octProg_spec_and_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) :
    let s₀ := Memory.State.init (encodeInput G k)
    let res := (Memory.spec 0).clientResult s₀ (octProg ())
    let t := (Memory.spec 0).clientState s₀ (octProg ())
    memoryCost (octProg ()) s₀ ≤ 680 * 3 ^ k * (n + 1) ^ 5 ∧
      res ≤ 1 ∧
      (res = 1 ↔ ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k) ∧
      (res = 1 → OctStateAt G n k t) := by
  intro s₀ res t
  have hs₀_1 : s₀.mem 1 = n := by
    change (if (1 : ℕ) = 0 then (encodeInput G k).length
      else (encodeInput G k).getD (1 - 1) 0) = n
    rfl
  have hs₀_2 : s₀.mem 2 = k := by
    change (if (2 : ℕ) = 0 then (encodeInput G k).length
      else (encodeInput G k).getD (2 - 1) 0) = k
    rfl
  have hs₀_fr : s₀.frontier = 3 + n * n := by
    simp only [s₀, Memory.State.init, length_encodeInput]
    omega
  have hG₀ : MatrixLoaded G s₀ := matrixLoaded_init G k
  set s_al := (Memory.spec 0).clientState s₀ (Memory.alloc (octScratch n))
  have hs_al_pre : ∀ a < 3 + n * n, s_al.mem a = s₀.mem a := fun a ha => by
    have ha_fr : a < s₀.frontier := by rw [hs₀_fr]; exact ha
    exact Memory.mem_step_of_lt_frontier s₀ (.alloc (octScratch n)) ha_fr (by simp)
  set s_sep := (Memory.spec 0).clientState s_al (fillRange ((sepBase n, 0), n))
  have hs_sep := fillRange_spec (sepBase n) 0 n s_al
  set s_col := (Memory.spec 0).clientState s_sep (fillRange ((colBase n, 0), n))
  have hs_col := fillRange_spec (colBase n) 0 n s_sep
  have hs_col_G : MatrixLoaded G s_col := fun u v => by
    have ha1 : 3 + u.val * n + v.val < colBase n := by
      dsimp only [colBase]; nlinarith [u.isLt, v.isLt]
    have ha2 : 3 + u.val * n + v.val < sepBase n := by
      dsimp only [sepBase]; nlinarith [u.isLt, v.isLt]
    rw [hs_col.2 _ (Or.inl ha1), hs_sep.2 _ (Or.inl ha2), hs_al_pre _ ha2]
    exact hG₀ u v
  have hoct0 : OctStateAt G 0 k s_col := by
    have hsep0 : ∀ v : Fin n, s_col.mem (sepBase n + v.val) = 0 := fun v =>
      (hs_col.2 _ (Or.inl (by dsimp only [sepBase, colBase]; omega))).trans (hs_sep.1 v.val v.isLt)
    have hcol0 : ∀ v : Fin n, s_col.mem (colBase n + v.val) = 0 := fun v => hs_col.1 v.val v.isLt
    refine ⟨fun v => ⟨by rw [hsep0]; decide, by rw [hcol0]; decide⟩, ?_⟩
    dsimp only
    have hempty : (Finset.univ.filter fun v : Fin n => s_col.mem (sepBase n + v.val) = 1) = ∅ := by
      ext v; simp [hsep0 v]
    rw [hempty]
    exact ⟨Nat.zero_le k, fun u _ hadj => absurd hadj.2.1 (Nat.not_lt_zero _)⟩
  have hp1_4 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  let LoopInv (rem : ℕ) (ma : ℕ × ℕ) (st : Memory.State) : Prop :=
    ma.1 + rem = n ∧
    MatrixLoaded G st ∧
    ma.2 ≤ 1 ∧
    (ma.2 = 1 → OctStateAt G ma.1 k st) ∧
    (ma.2 = 0 → ¬ ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k)
  have hstep : ∀ rem (ma : ℕ × ℕ) st, LoopInv (rem + 1) ma st →
      memoryCost (octStep ((n, k), ma)) st ≤ 655 * 3 ^ k * (n + 1) ^ 4 ∧
        LoopInv rem ((Memory.spec 0).clientResult st (octStep ((n, k), ma)))
          ((Memory.spec 0).clientState st (octStep ((n, k), ma))) := by
    intro rem ⟨m, alive⟩ st ⟨hmsum, hG_st, hal_le, hal1, hal0⟩
    have hm_lt : m < n := by omega
    by_cases hal : alive = 1
    · obtain ⟨h01_st, hS_card, hS_prop⟩ := hal1 hal
      set S : Finset (Fin n) := Finset.univ.filter fun v => st.mem (sepBase n + v.val) = 1
      let Wset : Finset (Fin n) := insert ⟨m, hm_lt⟩ S
      obtain ⟨htW_low, hW⟩ := buildWProg_spec hm_lt fun v => (h01_st v).1
      set L := (Memory.spec 0).clientResult st (buildWProg (n, m))
      set tW := (Memory.spec 0).clientState st (buildWProg (n, m))
      have hL_le_n : L ≤ n := hW.card_le_n
      have hL_le_k1 : L ≤ k + 1 := by
        rw [hW.card_eq]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hS_card 1)
      have hcW_prop : ∀ u v : Fin n, (prefixGraph G (m + 1)).Adj u v →
          u ∉ Wset → v ∉ Wset →
          (tW.mem (colBase n + u.val) == 1) ≠ (tW.mem (colBase n + v.val) == 1) := by
        intro u v ⟨hadj, hum1, hvm1⟩ huW hvW
        have hum : u.val ≠ m :=
          fun h => huW ((Fin.ext h : u = ⟨m, hm_lt⟩) ▸ Finset.mem_insert_self _ _)
        have hvm : v.val ≠ m :=
          fun h => hvW ((Fin.ext h : v = ⟨m, hm_lt⟩) ▸ Finset.mem_insert_self _ _)
        have huS : u ∉ S := fun h => huW (Finset.mem_insert_of_mem h)
        have hvS : v ∉ S := fun h => hvW (Finset.mem_insert_of_mem h)
        rw [htW_low _ (by dsimp only [colBase, wBase]; omega),
          htW_low _ (by dsimp only [colBase, wBase]; omega)]
        exact hS_prop u v ⟨hadj, by omega, by omega⟩ huS hvS
      have hG_tW : MatrixLoaded G tW := fun u v =>
        (htW_low _ (by dsimp only [wBase]; nlinarith [u.isLt, v.isLt])).trans (hG_st u v)
      have hcost_step : memoryCost (octStep ((n, k), (m, alive))) st ≤
          655 * 3 ^ k * (n + 1) ^ 4 := by
        unfold octStep
        dsimp only [OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive]
        rw [memoryCost_bind', memoryCost_read]
        change 1 + memoryCost (if alive = 1 then _ else _) st ≤ _
        rw [ite_eq_left hal, memoryCost_bind']
        have hbw := memoryCost_buildWProg_le (n, m) st
        dsimp only at hbw
        by_cases hLk : L ≤ k
        · rw [ite_eq_left hLk]
          have hw_mc : memoryCost (do Memory.write (sepBase n + m) 1; pure (m + 1, 1)) tW ≤ 1 :=
            (le_refl 1)
          nlinarith [hp1_4, hpow3]
        · rw [ite_eq_right hLk, ite_eq_left hL_le_n]
          have hcp := memoryCost_compressProg_le (d := (((n, k), m + 1), L)) hL_le_n tW
          dsimp only [CompressCfg.n] at hcp
          have hcp_map : memoryCost
              (do let ok ← compressProg (((n, k), m + 1), L); pure (m + 1, ok)) tW ≤
              215 * 3 ^ L * (n + 1) ^ 4 :=
            le_trans (memoryCost_bind_le hcp fun _ t' => (memoryCost_pure _ t').le) (by omega)
          have hL_eq : L = k + 1 := by omega
          have hpowL : 3 ^ L = 3 * 3 ^ k := by rw [hL_eq, pow_succ, Nat.mul_comm]
          rw [hpowL] at hcp_map
          nlinarith [hp1_4, hpow3]
      refine ⟨hcost_step, ?_⟩
      unfold octStep
      dsimp only [OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive]
      rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hal, clientResult_bind,
        clientState_bind]
      change LoopInv rem ((Memory.spec 0).clientResult tW (if L ≤ k then _ else _))
        ((Memory.spec 0).clientState tW (if L ≤ k then _ else _))
      by_cases hLk : L ≤ k
      · rw [ite_eq_left hLk, clientResult_bind_write, clientState_bind_write, clientResult_pure,
        clientState_pure]
        dsimp only [LoopInv]
        refine ⟨by omega, fun u v => ?_, by decide, fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        · dsimp only
          rw [Function.update_of_ne (by dsimp only [sepBase]; nlinarith [u.isLt, v.isLt])]
          exact hG_tW u v
        · refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
          · dsimp only
            by_cases hvm : v.val = m
            · rw [hvm, Function.update_self]
            · rw [Function.update_of_ne (by omega),
                htW_low _ (by dsimp only [sepBase, wBase]; omega)]
              exact (h01_st v).1
          · dsimp only
            rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              htW_low _ (by dsimp only [colBase, wBase]; omega)]
            exact (h01_st v).2
          · dsimp only
            have hS_new : (Finset.univ.filter fun v : Fin n =>
                Function.update tW.mem (sepBase n + m) 1 (sepBase n + v.val) = 1) = Wset := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Wset, Finset.mem_insert, S]
              by_cases hvm : v.val = m
              · have hveq : v = ⟨m, hm_lt⟩ := Fin.ext hvm
                subst hveq
                dsimp only
                rw [Function.update_self]
                simp
              · have hne : v ≠ ⟨m, hm_lt⟩ := fun h => hvm (congrArg Fin.val h)
                rw [Function.update_of_ne (by omega),
                  htW_low _ (by dsimp only [sepBase, wBase]; omega)]
                simp [hne]
            rw [hS_new, ← hW.card_eq]
            refine ⟨hLk, fun u v hadj huW hvW => ?_⟩
            rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              Function.update_of_ne (by dsimp only [sepBase, colBase]; omega)]
            exact hcW_prop u v hadj huW hvW
      · rw [ite_eq_right hLk, ite_eq_left hL_le_n, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        have hcol01_tW : ∀ v : Fin n, tW.mem (colBase n + v.val) ≤ 1 := fun v =>
          (htW_low _ (by dsimp only [colBase, wBase]; omega)).trans_le (h01_st v).2
        obtain ⟨hcp_low, hcp_le, hcp_sound, hcp_comp⟩ :=
          compressProg_spec (k := k) (m := m + 1) hG_tW hW hcol01_tW hcW_prop
        set ok := (Memory.spec 0).clientResult tW (compressProg (((n, k), m + 1), L))
        set tC := (Memory.spec 0).clientState tW (compressProg (((n, k), m + 1), L))
        dsimp only [LoopInv]
        refine ⟨by omega,
          fun u v => (hcp_low _ (by dsimp only [sepBase]; nlinarith [u.isLt, v.isLt])).trans
            (hG_tW u v),
          hcp_le, hcp_sound, fun hok0 ⟨T, hToct, hTk⟩ => ?_⟩
        have h1 : ok = 1 := hcp_comp ⟨T, hToct.anti (prefixGraph_le G (m + 1)), hTk⟩
        omega
    · have hal_eq0 : alive = 0 := by omega
      have hcost_dead : memoryCost (octStep ((n, k), (m, alive))) st ≤
          655 * 3 ^ k * (n + 1) ^ 4 := by
        unfold octStep
        dsimp only [OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive]
        rw [memoryCost_bind', memoryCost_read]
        change 1 + memoryCost (if alive = 1 then _ else _) st ≤ _
        rw [ite_eq_right hal]
        have : memoryCost (pure (m + 1, 0) : Memory.Prog (ℕ × ℕ)) st = 0 := rfl
        rw [this]
        nlinarith [hp1_4, hpow3]
      refine ⟨hcost_dead, ?_⟩
      unfold octStep
      dsimp only [OctStepArgs.n, OctStepArgs.k, OctStepArgs.m, OctStepArgs.alive]
      rw [clientResult_bind_read, clientState_bind_read, ite_eq_right hal]
      simp only [client_simps]
      dsimp only [LoopInv]
      exact ⟨by omega, hG_st, by decide, fun h => absurd h (by decide), fun _ => hal0 hal_eq0⟩
  obtain ⟨hiter_cost, hinv_end⟩ := iterate_inv_and_cost octStep (655 * 3 ^ k * (n + 1) ^ 4)
    (n, k) LoopInv hstep n (0, 1) s_col
    ⟨Nat.zero_add _, hs_col_G, by decide, fun _ => hoct0, fun h => absurd h (by decide)⟩
  set ma_end := (Memory.spec 0).clientResult s_col (iterate octStep (n, k) n (0, 1))
  set s_end := (Memory.spec 0).clientState s_col (iterate octStep (n, k) n (0, 1))
  obtain ⟨hm_end, _, hal_end_le, hal_end_1, hal_end_0⟩ := hinv_end
  have hm_eq_n : ma_end.1 = n := by omega
  rw [hm_eq_n] at hal_end_1
  have hres_eq : res = ma_end.2 := by
    change (Memory.spec 0).clientResult s₀ (octProg ()) = ma_end.2
    unfold octProg
    rw [clientResult_bind_read, clientResult_bind_read, hs₀_1, hs₀_2, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_bind, clientResult_pure]
  have ht_eq : t = s_end := by
    change (Memory.spec 0).clientState s₀ (octProg ()) = s_end
    unfold octProg
    rw [clientState_bind_read, clientState_bind_read, hs₀_1, hs₀_2, clientState_bind,
      clientState_bind, clientState_bind, clientState_bind, clientState_pure]
  have htotal_cost : memoryCost (octProg ()) s₀ ≤ 680 * 3 ^ k * (n + 1) ^ 5 := by
    unfold octProg
    have hr1 : (Memory.spec 0).clientResult s₀ (Memory.read 1) = n := hs₀_1
    have hcs1 : (Memory.spec 0).clientState s₀ (Memory.read 1) = s₀ := rfl
    have hr2 : (Memory.spec 0).clientResult s₀ (Memory.read 2) = k := hs₀_2
    have hcs2 : (Memory.spec 0).clientState s₀ (Memory.read 2) = s₀ := rfl
    rw [memoryCost_bind', memoryCost_read, hr1, hcs1, memoryCost_bind', memoryCost_read, hr2, hcs2,
      memoryCost_bind', memoryCost_alloc]
    change 1 + (1 + ((octScratch n + 1) +
        memoryCost (do
          fillRange ((sepBase n, 0), n)
          fillRange ((colBase n, 0), n)
          let res ← iterate octStep (n, k) n (0, 1)
          pure res.2) s_al)) ≤ 680 * 3 ^ k * (n + 1) ^ 5
    rw [memoryCost_bind']
    change 1 + (1 + ((octScratch n + 1) +
        (memoryCost (fillRange ((sepBase n, 0), n)) s_al +
          memoryCost (do
            fillRange ((colBase n, 0), n)
            let res ← iterate octStep (n, k) n (0, 1)
            pure res.2) s_sep))) ≤ 680 * 3 ^ k * (n + 1) ^ 5
    rw [memoryCost_bind']
    change 1 + (1 + ((octScratch n + 1) +
        (memoryCost (fillRange ((sepBase n, 0), n)) s_al +
          (memoryCost (fillRange ((colBase n, 0), n)) s_sep +
            memoryCost (do let res ← iterate octStep (n, k) n (0, 1); pure res.2) s_col)))) ≤
      680 * 3 ^ k * (n + 1) ^ 5
    have hc_sep := memoryCost_fillRange_le ((sepBase n, 0), n) s_al
    have hc_col := memoryCost_fillRange_le ((colBase n, 0), n) s_sep
    dsimp only at hc_sep hc_col
    have hc_pure : memoryCost (do let res ← iterate octStep (n, k) n (0, 1); pure res.2) s_col ≤
        655 * 3 ^ k * (n + 1) ^ 4 * n :=
      le_trans (memoryCost_bind_le hiter_cost fun _ u => (memoryCost_pure _ u).le) (by omega)
    exact le_trans (by omega) (octProg_cost_arith n k)
  rw [hres_eq, ht_eq]
  refine ⟨htotal_cost, hal_end_le, ⟨fun h1 => ?_, fun hex => ?_⟩, hal_end_1⟩
  · obtain ⟨_, hcard, hprop⟩ := hal_end_1 h1
    let S := Finset.univ.filter fun v : Fin n => s_end.mem (sepBase n + v.val) = 1
    refine ⟨S,
        isOddCycleTransversal_iff_exists_bool.mpr ⟨fun v => s_end.mem (colBase n + v.val) == 1,
      fun u v hadj hu hv => ?_⟩, hcard⟩
    rw [← prefixGraph_of_le G (le_refl n)] at hadj
    exact hprop u v hadj hu hv
  · by_cases h1 : ma_end.2 = 1
    · exact h1
    · exact absurd hex (hal_end_0 (by omega))

end Cslib.Algorithms.WordRAM.OddCycleTransversal
