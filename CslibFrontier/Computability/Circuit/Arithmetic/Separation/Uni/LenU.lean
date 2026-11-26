/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Trace
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Total tape lengths of matched runs

Computes the exact total emitted tape length of a matched sorting run `IMU` (`Uni.imu_length`)
and of a matched universal pointer-machine run `MX` (`Uni.MX.total`), yielding the closed-form
bound `Uni.tU b T L` in terms of the alphabet size `b = Fintype.card (Bl K)`, step count `T`,
and bit-width `L`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.LenU`.

## Main definitions

* `Uni.tU`: exact total length formula over all tapes for `T` steps, bit-width `L`, and
  `b = card (Bl K)` record key letters.

## Main results

* `Uni.length_encW`, `Uni.length_encW_recs`, `Uni.canon_length`, `Uni.length_bws`.
* `Uni.imu_length`: total tape length of the sorting and comparison tapes under `IMU`.
* `Uni.MX.total`: exact total read-side tape length of a matched universal-program run `MX`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset List.RadixSort

private theorem sum_const_map {ι : Type*} (l : List ι) (f : ι → ℕ) (c : ℕ)
    (h : ∀ i ∈ l, f i = c) : (l.map f).sum = l.length * c := by
  rw [List.map_congr_left h, List.map_const', List.sum_replicate, smul_eq_mul]

private theorem sum_Tp {K : Type} [Fintype K] (f : Tp K → ℕ) :
    ∑ s, f s =
      (∑ i, f (.rg i)) + f .md + f .cp + f .fr + f .lk + f .ls +
        (∑ b, f (.bk b)) + ∑ k, f (.cm k) := by
  let e : Tp K ≃ (Fin 5 ⊕ (Bl K ⊕ Bool)) ⊕ Fin 5 :=
    { toFun := fun s => match s with
        | .rg i => .inl (.inl i)
        | .bk b => .inl (.inr (.inl b))
        | .cm k => .inl (.inr (.inr k))
        | .md => .inr 0
        | .cp => .inr 1
        | .fr => .inr 2
        | .lk => .inr 3
        | .ls => .inr 4
      invFun := fun y => match y with
        | .inl (.inl i) => .rg i
        | .inl (.inr (.inl b)) => .bk b
        | .inl (.inr (.inr k)) => .cm k
        | .inr 0 => .md
        | .inr 1 => .cp
        | .inr 2 => .fr
        | .inr 3 => .lk
        | .inr 4 => .ls
      left_inv := fun s => by cases s <;> rfl
      right_inv := fun y => by
        rcases y with (i | b | k) | j
        · rfl
        · rfl
        · rfl
        · fin_cases j <;> rfl }
  rw [← e.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_five (fun j => f (e.symm (.inr j)))]
  change (∑ i, f (.rg i)) + ((∑ b, f (.bk b)) + ∑ k, f (.cm k)) +
    (f .md + f .cp + f .fr + f .lk + f .ls) = _
  ring

theorem length_rw' {M K : Type} (f : Bool) (w : List (Option (Bl K))) :
    (rw' f w : List (Sy M K)).length = w.length + 2 := by
  simp [rw']

theorem length_encW {M K : Type} {l : List (Bool × List (Option (Bl K)))} {n : ℕ}
    (h : ∀ r ∈ l, r.2.length = n) :
    (encW l : List (Sy M K)).length = l.length * (n + 2) := by
  induction l with
  | nil => simp [encW]
  | cons r l ih =>
    rw [encW_cons, List.length_append, length_rw', h r (by simp),
      ih fun r hr => h r (by simp [hr]), List.length_cons]; ring

theorem length_rot {K : Type} {n j : ℕ} (hj : j ≤ n) (x : Fin n → Bl K) :
    (rot j x).length = n + 1 := by
  simp [rot]; omega

theorem length_encW_recs {M K : Type} {n j : ℕ} (hj : j ≤ n) (l : List (Rc n (Bl K))) :
    (encW (recs j l) : List (Sy M K)).length = l.length * (n + 3) := by
  rw [length_encW (n := n + 1)]
  · simp [recs]
  · intro r hr
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hr
    exact length_rot hj _

theorem canon_length {M K : Type} [Fintype K] [DecidableEq K] {n : ℕ}
    (l : List (Rc n (Bl K))) (k j : ℕ) (hjk : j + k = n) :
    (canon l k j : List (Ps M K)).length = k ∧
      ∀ p ∈ (canon l k j : List (Ps M K)),
        (encW (dIn p.1) : List (Sy M K)).length = l.length * (n + 3) ∧
          ∑ b, ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length = l.length * (n + 3) := by
  induction k generalizing j with
  | zero => simp [canon]
  | succ k ih =>
    have hj : j < n := by omega
    obtain ⟨h1, h2⟩ := ih (j + 1) (by omega)
    have hl : (srt (bsl K) l j).length = l.length := length_srt mem_bsl bsl_nodup l j
    rw [canon]
    simp only [hj, ↓reduceDIte]
    refine ⟨by rw [List.length_cons, h1], fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨by rw [cps, dIn_dl, length_encW_recs hj.le, hl], ?_⟩
      have h3 (b) :
          (((cps j hj (srt (bsl K) l j) : Ps M K).2 b).map
            (Subtype.val : NB M K → Sy M K)).length =
          ((srt (bsl K) l j).filter fun r => r.2 ⟨j, hj⟩ = b).length * (n + 3) := by
        rw [cps, toNB_val _ (bar_encW _), dOut_dl, length_encW_recs (by omega)]
      rw [Finset.sum_congr rfl fun b _ => h3 b, ← Finset.sum_mul, List.RadixSort.sum_filter, hl]
    · exact h2 p hp

/-- Exact total emitted length on the sorting, bucket, and comparison tapes under `IMU`. -/
theorem imu_length {M K : Type} [Fintype K] [DecidableEq K] {n : ℕ}
    {l : List (Rc n (Bl K))} (hl : l ≠ []) {x : XU M K} (h : IMU x (encW (recs 0 l))) :
    (emU x lsT).length + ∑ b, (emU x (.tp (.bk b) true)).length +
        ∑ k, (emU x (.tp (.cm k) true)).length =
      (n + 1) * (l.length * (n + 3) + 1) +
        (n * (l.length * (n + 3)) + Fintype.card (Bl K) * n) + 2 * (l.length * (n + 2)) := by
  rw [imu_iff hl] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨c1, c2⟩ := canon_length (M := M) l n 0 (by omega)
  have hfin : (finL l).length = l.length := by simp [finL, length_srt mem_bsl bsl_nodup]
  have hsum := sum_const_map (canon l n 0 : List (Ps M K))
    (List.length ∘ fun p : Ps M K => (encW (dIn p.1) : List (Sy M K)))
    (l.length * (n + 3)) (fun p hp => (c2 p hp).1)
  have e1 : (emU x lsT).length = (n + 1) * (l.length * (n + 3) + 1) := by
    rw [emU_lsT, length_blocks, h1, h2, ← recs_last, List.map_append, List.sum_append,
      List.map_map, hsum, c1, List.length_append, List.length_map, c1]
    simp only [List.map_cons, List.map_nil, List.sum_singleton, List.length_singleton]
    rw [length_encW_recs le_rfl, length_srt mem_bsl bsl_nodup]; ring
  have e2 : ∑ b, (emU x (.tp (.bk b) true)).length =
      n * (l.length * (n + 3)) + Fintype.card (Bl K) * n := by
    have h5 : ∀ b, (emU x (.tp (.bk b) true)).length =
        (x.passes.map fun p => ((p.2 b).map (Subtype.val : NB M K → Sy M K)).length).sum + n := by
      intro b
      rw [emU_bk_true, length_blocks, List.map_map, List.length_map, h1, c1]
      rfl
    rw [Finset.sum_congr rfl fun b _ => h5 b, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    congr 1
    rw [Finset.sum_list_sum_comm, h1,
      sum_const_map _ _ (l.length * (n + 3)) (fun p hp => (c2 p hp).2), c1]
  have e3 : ∀ k, (emU x (.tp (.cm k) true)).length = l.length * (n + 2) := by
    intro k
    rw [emU_cm_true]
    have h7 : (if k then QlG x.cmp else PlG x.cmp) = finL l :=
      Bool.rec (by simpa using h3)
        (by simpa using h4) k
    rw [h7, length_encW (n := n)]
    · rw [fOut, List.length_map, hfin]
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hr'
      simp
  rw [e1, e2, Finset.sum_congr rfl fun k _ => e3 k]
  simp

theorem length_bws {M K : Type} {ws : List (List Bool)} {n : ℕ}
    (h : ∀ w ∈ ws, w.length = n) :
    (bws ws : List (Sy M K)).length = ws.length * (n + 1) := by
  induction ws with
  | nil => simp [bws]
  | cons w ws ih =>
    rw [bws_cons, List.length_append, ih fun w hw => h w (by simp [hw]), List.length_cons]
    simp only [bw, List.length_append, List.length_map, List.length_singleton, h w (by simp)]
    ring

/-- Closed-form total read-side tape length for `T` steps, bit-width `L`, and `b` record-key
letters. -/
@[expose] def tU (b T L : ℕ) : ℕ :=
  5 * ((T + 1) * (L + 1)) + (T + 1) + (T + 1) * (L + 1) + T * (L + 1) + T * (L + 4) +
    ((L + 2) * ((2 * T + 1) * (L + 4) + 1) +
      ((L + 1) * ((2 * T + 1) * (L + 4)) + b * (L + 1)) +
      2 * ((2 * T + 1) * (L + 3)))

theorem MX.total {A M K : Type} [Fintype K] [DecidableEq K] {P : Mach A M K}
    {x : XP P} {bits : List Bool} (hx : MX x bits) :
    ∑ s, (emX P x (.tp s true)).length =
      tU (Fintype.card (Bl K)) x.steps.length (x.init.length + 1) := by
  have hcw (s) (hs : s ∈ x.steps) (i) : (cw s.2 i).length = x.init.length + 1 := by
    rw [cw, List.length_map, hx.len s hs]
  have hend (i : Fin 5) : (x.finalRegs.map fun v => v i).length = x.init.length + 1 := by
    have hm : (x.finalRegs.map fun v => v i) ∈
        x.steps.map (fun s => cw s.2 (rv i)) ++ [x.finalRegs.map fun v => v i] := by simp
    rw [← hx.rg i] at hm
    rcases List.mem_cons.mp hm with h | hm
    · exact h.symm ▸ length_i0 _
    · obtain ⟨s, hs, h⟩ := List.mem_map.mp hm
      exact h ▸ hcw s hs _
  have e1 (i) : (emX P x (.tp (.rg i) true)).length =
      (x.steps.length + 1) * (x.init.length + 2) := by
    rw [emX_rg_true, length_bws (n := x.init.length + 1)]
    · simp
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
        exact hcw s hs _
      · rw [List.mem_singleton.mp hw]
        exact hend i
  have e3 : (emX P x (.tp .cp true)).length = (x.steps.length + 1) * (x.init.length + 2) := by
    rw [emX_cp_true, length_bws (n := x.init.length + 1)]
    · simp [hx.length_eq]
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
        exact hx.len_cn.1 r hr
      · rw [List.mem_singleton.mp hw]
        simpa using hx.len_cn.2
  have e4 : (emX P x (.tp .fr true)).length = x.steps.length * (x.init.length + 2) := by
    rw [emX_fr_true, length_bws (n := x.init.length + 1)]
    · simp
    · intro w hw
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
      exact hcw s hs _
  have e5 : (emX P x (.tp .lk true)).length = x.steps.length * (x.init.length + 5) := by
    rw [emX_lk_true, hx.lk, length_encW (n := x.init.length + 3)]
    · simp [lks]
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
      simp [oc, cont, ldc, hx.len s hs]
  have e6 := imu_length (lsN_ne _ _) (hx.block ▸ hx.ls)
  have hN : (lsN (x.init.length + 1) (x.steps.map nst)).length = 2 * x.steps.length + 1 := by
    simp [lsN, dfN]; ring
  rw [hN] at e6
  rw [sum_Tp (fun s => (emX P x (.tp s true)).length),
    Finset.sum_congr rfl fun i _ => e1 i, emX_md_true, List.length_map, List.length_append,
    List.length_map, List.length_singleton, e3, e4, e5, emX_ls_true,
    Finset.sum_congr rfl fun b _ => congrArg List.length (emX_bk ..),
    Finset.sum_congr rfl fun k _ => congrArg List.length (emX_cm ..)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold tU
  rw [← e6]
  ring

end Cslib.Circuits.Arithmetic.Separation.Uni
