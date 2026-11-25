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
  obtain ⟨k, hk⟩ : ∃ k, Nat.size (tr.length + 1) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Nat.size_pos.2 (by omega))).symm⟩
  set L := k + 1 with hL
  have hT1 : tr.length + 1 < 2 ^ L := hk ▸ Nat.lt_size_self _
  have hT2 : 2 ^ k ≤ tr.length + 1 := by rw [← Nat.lt_size, hk]; omega
  have henc_len (n : ℕ) : (enc L n).length = L :=
    length_binaryWord (Nat.mod_lt _ (Nat.two_pow_pos L))
  have henc_val {n : ℕ} (hn : n < 2 ^ L) : binaryValue (enc L n) = n := by
    simp only [enc, Nat.mod_eq_of_lt hn, binaryValue_binaryWord]
  have hct (j : ℕ) : ∃ r : List Bool × List Unit, j < tr.length → cn r = enc L (j + 1) := by
    by_cases hj : j < tr.length
    · obtain ⟨u, m, e⟩ := exists_carry_cut (w := enc L (j + 1)) (by
        rw [henc_val (by omega), henc_len]
        omega)
      exact ⟨(u, List.replicate m ()), fun _ => by rw [e, cn, List.length_replicate]⟩
    · exact ⟨([], []), fun h => absurd h hj⟩
  choose ct hct using hct
  choose fin hfin using h2
  let l0 : List Unit := List.replicate k ()
  let cts : List (List Bool × List Unit) := (List.range tr.length).map ct
  let sts : List (P.Rl × List (Fin 9 → Bool)) := tr.map fun st => (st.1, unb L st.2)
  have hmap : sts.map nst = tr := by
    simp only [sts, List.map_map]
    conv_rhs => rw [← List.map_id tr]
    refine List.map_congr_left fun st hst => Prod.ext rfl (funext fun i => ?_)
    simp only [Function.comp_apply, id_eq, nst, cw, unb_proj,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (hle st hst i) (Nat.lt_of_succ_lt hT1)),
      binaryValue_binaryWord]
  have hlen : ∀ s ∈ sts, s.2.length = l0.length + 1 := fun s hs => by
    obtain ⟨st, -, rfl⟩ := List.mem_map.1 hs
    simp [l0, length_unb, hL]
  let lkw : List (Sy M K) :=
    encW ((sts.map fun s => cont (P.lk s.1) (ldc P s.1 s.2)).map fun c => (true, oc c))
  obtain ⟨xu, hxu⟩ : ∃ xu : XU M K, IMU xu (encW (recs 0 (lsN L tr))) := by
    refine (imu_table (M := M) ((dfN tr).map (kyN L)) ((tr.map Mach.ld).map (kyN L))
      (by simp [dfN])).2 fun y hy => ?_
    obtain ⟨_, hρ, rfl⟩ := List.mem_map.1 hy
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hρ
    refine List.mem_map.2 ⟨Mach.ld st, ?_, rfl⟩
    rw [dfN]
    simpa [σi] using h5 st hst
  let x : XP P := ⟨l0, cts, sts, unb L fin, (enc L (tr.length + 1)).tail, lkw, xu⟩
  have hl0 : l0.length + 1 = L := by simp [l0, hL]
  have hcts : cts.map cn = (List.range tr.length).map fun j => enc L (j + 1) := by
    simp only [cts, List.map_map]
    exact List.map_congr_left fun j hj => hct j (List.mem_range.1 hj)
  have hcts1 : cts.map cn1 = (List.range tr.length).map fun j => enc L (j + 2) := by
    simp only [cts, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.1 hj
    have e := hct j hj'
    simp only [Function.comp]
    rw [bin_of (L := L) (w := cn1 (ct j)) (by rw [length_cn, e, henc_len]), bv_cn, e,
      henc_val (by omega)]
  have hcw (f : P.Rl → Fin 9) :
      sts.map (fun s => cw s.2 (f s.1)) = (tr.map fun st => st.2 (f st.1)).map (enc L) := by
    simp only [sts, enc, List.map_map, Function.comp_def, cw, unb_proj]
  refine ⟨x, ⟨fun i => ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩, hmap⟩
  · change i0 l0 :: sts.map (fun s => cw s.2 (P.dr s.1 i)) =
      sts.map (fun s => cw s.2 (rv i)) ++ [(unb L fin).map fun v => v i]
    have h6 := congrArg (List.map (enc L)) (hfin i)
    simpa only [List.map_cons, List.map_nil, List.map_append, hcw (fun r => P.dr r i),
      hcw (fun _ => rv i), enc, σi, Nat.zero_mod, i0, hl0, binaryWord_zero, unb_proj] using h6
  · simpa only [x, sts, σi, List.map_map, Function.comp_def] using h1
  · change i1 l0 :: cts.map cn1 = cts.map cn ++ [true :: (enc L (tr.length + 1)).tail]
    have e1 : i1 l0 = enc L 1 := by
      rw [bin_of (L := L) (w := i1 l0) (by rw [length_i1, hl0]), bv_i1]
    have e2 : true :: (enc L (tr.length + 1)).tail = enc L (tr.length + 1) := by
      have hlenW := henc_len (tr.length + 1)
      have hvalW := henc_val hT1
      rcases hw : enc L (tr.length + 1) with _ | ⟨_ | _, t⟩
      · rw [hw] at hlenW; simp [hL] at hlenW
      · have hlt2 := binaryValue_lt_two_pow t
        rw [hw] at hlenW hvalW
        simp only [hL, List.length_cons, Nat.add_right_cancel_iff] at hlenW
        simp only [binaryValue_cons, Bool.toNat_false, zero_mul, zero_add] at hvalW
        rw [hlenW] at hlt2; omega
      · rfl
    rw [e1, e2, hcts, hcts1, ← List.map_singleton (f := fun j => enc L (j + 1)),
      ← List.map_append, ← List.range_succ, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  · change cts.map cn = sts.map fun s => cw s.2 8
    rw [hcts, hcw (fun _ => 8), h3, List.map_map]
    exact List.map_congr_left fun j _ => congrArg (enc L) (by dsimp [σi]; omega)
  · have hb := block_of (x := x) hlen
    change IMU xu
      (encW ((dfs x).map (fun c => (false, oc c)) ++ (lks x).map fun c => (true, oc c)))
    rwa [hb, show l0.length + 1 = L from hl0, hmap]
  · simpa only [x, sts, σi, List.flatMap_map] using h4

end Cslib.Circuits.Arithmetic.Separation.Uni
