/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Trace
import Mathlib.Data.Nat.Size

/-!
# Every run of the pointer machine yields a matched tape run

Constructs, from any globally valid pointer-machine trace `Mach.GV (σi P bits) tr` whose variable
values are bounded by `tr.length`, a matching run `x : Uni.XP P` with `Uni.MX x bits` and
`x.steps.map Uni.nst = tr` (`Uni.exists_MX`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Exist`.

## Main results

* `Uni.exists_MX`: completeness of the universal tape program for globally valid bounded traces.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Cslib.BitString (binaryValue binaryValue_binaryWord binaryValue_cons binaryValue_lt_two_pow
  binaryWord binaryWord_binaryValue binaryWord_zero exists_carry_cut length_binaryWord)

private theorem bin_of {L : ℕ} {w : List Bool} (hl : w.length = L) :
    w = binaryWord L (binaryValue w % 2 ^ L) := by
  have hlt : binaryValue w < 2 ^ L := by rw [← hl]; exact binaryValue_lt_two_pow w
  rw [Nat.mod_eq_of_lt hlt, ← hl, binaryWord_binaryValue]

/-- Every globally valid bounded pointer-machine trace lifts to a matched run `x : XP P`. -/
theorem exists_MX {A M K : Type} [Fintype K] [DecidableEq K] {P : Mach A M K}
    {tr : List P.Step} {bits : List Bool} (hgv : Mach.GV (σi P bits) tr)
    (hle : ∀ st ∈ tr, ∀ i, st.2 i ≤ tr.length) :
    ∃ x : XP P, MX x bits ∧ x.steps.map nst = tr := by
  let enc (L n : ℕ) : List Bool := binaryWord L (n % 2 ^ L)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hgv
  obtain ⟨k, hk⟩ : ∃ k, Nat.size (tr.length + 1) = k + 1 := by
    have hpos : 0 < Nat.size (tr.length + 1) := Nat.size_pos.2 (by omega)
    exact ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  set L := k + 1 with hL
  have hT1 : tr.length + 1 < 2 ^ L := by
    rw [← hk]
    exact Nat.lt_size_self _
  have hT2 : 2 ^ k ≤ tr.length + 1 := by
    rw [← Nat.lt_size, hk]
    omega
  have henc_len : ∀ n, (enc L n).length = L :=
    fun n => length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos L))
  have henc_val : ∀ {n}, n < 2 ^ L → binaryValue (enc L n) = n := by
    intro n hn
    simp only [enc, Nat.mod_eq_of_lt hn, binaryValue_binaryWord]
  have hlt : ∀ st ∈ tr, ∀ i, st.2 i < 2 ^ L :=
    fun st hst i => lt_of_le_of_lt (hle st hst i) (by omega)
  have hct : ∀ j, ∃ r : List Bool × List Unit, j < tr.length → cn r = enc L (j + 1) := by
    intro j
    by_cases hj : j < tr.length
    · obtain ⟨u, m, e⟩ := exists_carry_cut (w := enc L (j + 1)) (by
        rw [henc_val (by omega), henc_len]
        omega)
      refine ⟨(u, List.replicate m ()), fun _ => ?_⟩
      rw [e, cn, List.length_replicate]
    · exact ⟨([], []), fun h => absurd h hj⟩
  choose ct hct using hct
  choose fin hfin using h2
  let l0 : List Unit := List.replicate k ()
  let cts : List (List Bool × List Unit) := (List.range tr.length).map ct
  let sts : List (P.Rl × List (Fin 9 → Bool)) := tr.map fun st => (st.1, unb L st.2)
  have hnst : ∀ st ∈ tr, nst (P := P) (st.1, unb L st.2) = st := by
    intro st hst
    refine Prod.ext rfl ?_
    funext i
    simp only [nst, cw]
    rw [unb_proj, Nat.mod_eq_of_lt (hlt st hst i), binaryValue_binaryWord]
  have hmap : sts.map nst = tr := by
    simp only [sts, List.map_map]
    conv_rhs => rw [← List.map_id tr]
    exact List.map_congr_left fun st hst => hnst st hst
  have hlen : ∀ s ∈ sts, s.2.length = l0.length + 1 := by
    intro s hs
    obtain ⟨st, -, rfl⟩ := List.mem_map.1 hs
    simp [l0, length_unb, hL]
  let lkw : List (Sy M K) :=
    encW ((sts.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)).map fun c => (true, oc c))
  have hxu : ∃ xu : XU M K, IMU xu (encW (recs 0 (lsN L tr))) := by
    refine (imu_table (M := M) ((dfN tr).map (kyN L)) ((tr.map Mach.ld).map (kyN L))
      (by simp [dfN])).2 ?_
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hy
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hρ
    have h6 := h5 st hst
    refine List.mem_map.2 ⟨Mach.ld st, ?_, rfl⟩
    rw [dfN]
    simpa [σi] using h6
  obtain ⟨xu, hxu⟩ := hxu
  let x : XP P :=
    ⟨l0, cts, sts, unb L fin, (enc L (tr.length + 1)).tail, lkw, xu⟩
  have hl0 : l0.length + 1 = L := by simp [l0, hL]
  have hcts : cts.map cn = (List.range tr.length).map fun j => enc L (j + 1) := by
    simp only [cts, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    exact hct j (List.mem_range.1 hj)
  have hcts1 : cts.map cn1 = (List.range tr.length).map fun j => enc L (j + 2) := by
    simp only [cts, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have e := hct j (List.mem_range.1 hj)
    have hj' := List.mem_range.1 hj
    simp only [Function.comp]
    rw [bin_of (L := L) (w := cn1 (ct j)) (by rw [length_cn, e, henc_len]), bv_cn, e,
      henc_val (by omega)]
  refine ⟨x, ⟨fun i => ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩, hmap⟩
  · have h6 := congrArg (List.map (enc L)) (hfin i)
    rw [List.map_cons, List.map_append, List.map_map, List.map_map] at h6
    have e0 : i0 l0 = enc L 0 := by simp [enc, i0, hl0, binaryWord_zero]
    change i0 l0 :: sts.map (fun s => cw s.2 (P.dr s.1 i)) =
      sts.map (fun s => cw s.2 (rv i)) ++ [(unb L fin).map fun v => v i]
    rw [e0, unb_proj]
    simp only [sts, List.map_map]
    have a1 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 (P.dr s.1 i)) ∘
        fun st : P.Step => (st.1, unb L st.2)) =
        enc L ∘ fun st => st.2 (P.dr st.1 i) := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    have a2 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 (rv i)) ∘
        fun st : P.Step => (st.1, unb L st.2)) =
        enc L ∘ fun st => st.2 (rv i) := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    rw [a1, a2]
    exact h6
  · change P.m0 :: sts.map (fun s => P.dst s.1) = sts.map (fun s => P.src s.1) ++ [P.mh]
    simp only [sts, List.map_map]
    exact h1
  · change i1 l0 :: cts.map cn1 = cts.map cn ++ [true :: (enc L (tr.length + 1)).tail]
    have e1 : i1 l0 = enc L 1 := by
      rw [bin_of (L := L) (w := i1 l0) (by rw [length_i1, hl0]), bv_i1]
    have e2 : true :: (enc L (tr.length + 1)).tail = enc L (tr.length + 1) := by
      have hlenW := henc_len (tr.length + 1)
      have hvalW := henc_val hT1
      rcases hw : enc L (tr.length + 1) with _ | ⟨b, t⟩
      · rw [hw] at hlenW; simp [hL] at hlenW
      · cases b
        · have htlen : t.length = k := by rw [hw] at hlenW; simpa [hL] using hlenW
          have hlt2 := binaryValue_lt_two_pow t
          rw [hw, binaryValue_cons, Bool.toNat_false, zero_mul, zero_add] at hvalW
          rw [htlen] at hlt2
          omega
        · rfl
    rw [e1, e2, hcts, hcts1]
    have e3 : ((List.range tr.length).map fun j => enc L (j + 1)) ++
        [enc L (tr.length + 1)] = (List.range (tr.length + 1)).map fun j => enc L (j + 1) := by
      rw [List.range_succ, List.map_append]
      rfl
    rw [e3, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  · change cts.map cn = sts.map fun s => cw s.2 8
    rw [hcts]
    have h6 := congrArg (List.map (enc L)) h3
    rw [List.map_map, List.map_map] at h6
    simp only [sts, List.map_map]
    have a1 : ((fun s : P.Rl × List (Fin 9 → Bool) => cw s.2 8) ∘
        fun st : P.Step => (st.1, unb L st.2)) =
        enc L ∘ fun st => st.2 8 := by
      funext st
      simp only [Function.comp, cw]
      exact unb_proj L st.2 _
    rw [a1, h6]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp, σi]
    congr 1
    omega
  · have hb := block_of (x := x) hlen
    change IMU xu
      (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
    rw [hb]
    change IMU xu (encW (recs 0 (lsN (l0.length + 1) (sts.map nst))))
    rw [hl0, hmap]
    exact hxu
  · change (sts.flatMap fun s => (P.rd s.1).toList) = bits
    simp only [sts, List.flatMap_map]
    exact h4

end Cslib.Circuits.Arithmetic.Separation.Uni
