/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Evict
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.Randomized.UniformLoopExit
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.WramOmega

/-!
# Word-RAM Cuckoo Hashing: Las Vegas Rehashing and Insertion

This module implements full-table Las Vegas rehashing (`rehashLoopCode`) and dictionary insertion
(`insertCode`) for Pagh and Rodler's cuckoo hashing dictionary [PaghRodler2004] on the randomized
Word RAM, building on the layout, lookup, and bounded displacement primitives in
`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Evict`.

When `evictLoopCode` reaches the displacement cap `maxEvictions n_max` during a new-key insertion,
`rehashLoopCode` repeatedly resamples both hash blocks via `resampleAtBaseCode`, clears `T₁` and
`T₂`, and replays `insKeys` in insertion order until all stored keys settle. By
`loopExitPMF_map_eq_uniformOfFinset`, the resulting exit seed is distributed uniformly over
`survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.rehashLoopCode`: Las Vegas full-table
  resampling and insertion-order replay loop.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.RehashLoopInv`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.RehashLoopPost`: loop invariant and exit
  postcondition for `rehashLoopCode`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.insertCode`: dictionary insertion subroutine
  combining two-probe lookup, in-place overwrite, bounded displacement, and Las Vegas rehashing.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.rehashLoopCode_execCodeDist`: geometric Las
  Vegas termination, expected step bound, and exact conditional-uniform exit law for full-table
  rehashing.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.insertCode_execCodeDist`: distributional
  execution specification for `insertCode` maintaining `RepWithKeys` and exact surviving-seed
  transition.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, pp. 6–10).
* [M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence"][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

open Cslib.DataStructure.Dictionary.CuckooHashing
open Cslib.WordRAM
open Cslib.WordRAM.Randomized
open Cslib.Probability
open Cslib.Probability.PMF
open scoped ENNReal

/-! ### Table clearing and insertion-order replay (`clearTablesCode`, `replayLoopCode`) -/

private def zeroRangeLoop : Code .exact 19 :=
  .loop (.lt 16 17)
    (.seq (.op (.store 16 18))
          (.op (.exactBin .add 16 16 15)))

private theorem zeroRangeLoop_exec {w : ℕ} :
    ∀ (rem ptr : ℕ) {x : Data 19}
      (_h16 : x.regs 16 = ptr)
      (_h17 : x.regs 17 = ptr + rem)
      (_h18 : x.regs 18 = 0)
      (_h15 : x.regs 15 = 1)
      (_hfit : Fits w (ptr + rem)),
      ∃ y : Data 19,
        Exec w zeroRangeLoop x y (4 * rem + 2) ∧
        y.regs 0 = x.regs 0 ∧
        (∀ a, ptr ≤ a → a < ptr + rem → y.mem a = 0) ∧
        (∀ a, (a < ptr ∨ ptr + rem ≤ a) → y.mem a = x.mem a)
  | 0, ptr, x, h16, h17, _, _, _ => by
    have hcond : ¬(Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17]
    exact ⟨x, Exec.loop_exit hcond, rfl, fun a hlo hhi => by omega, fun _ _ => rfl⟩
  | rem + 1, ptr, x, h16, h17, h18, h15, hfit => by
    have hcond : (Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17]
    refine WP.Exact.exists_exec (WP.Exact.loop_iter hcond ?_)
    wram_exec [h16, h18, h15]
    wram_call (zeroRangeLoop_exec rem (ptr + 1) (by wram_simp)
      (by rw [show ptr + 1 + rem = ptr + (rem + 1) by omega]; wram_simp [h17])
      (by wram_simp [h18]) (by wram_simp [h15]) (by fits)) with y ⟨hy_0, hy_zero, hy_frame⟩
    refine ⟨by omega, hy_0.trans (by wram_simp), fun a hlo hhi => ?_,
      fun a ha => (hy_frame a (by omega)).trans (by wram_simp)⟩
    by_cases ha : a = ptr
    · subst a
      exact (hy_frame ptr (Or.inl (by omega))).trans (by wram_simp)
    · exact hy_zero a (by omega) (by omega)

/-- Clears both cuckoo sub-tables `T₁` and `T₂` (`mem[t1Base .. keysBase - 1] ← 0`). -/
private def clearTablesCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 7)
  (.seq (loadHeaderCode 17 9)
  (.seq (.op (.const 18 0))
  (.seq (.op (.const 15 1))
        zeroRangeLoop)))

private def clearTablesSteps (n_max : ℕ) : ℕ :=
  8 * tableSize n_max + 10

private theorem clearTablesCode_exec {w base c_exp n_max U : ℕ} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w clearTablesCode x y (clearTablesSteps n_max) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base c_exp n_max U y.mem ∧
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max)
        (PureTable.empty U (2 ^ tableBits n_max)) y.mem ∧
      (∀ a, (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  have ⟨_, _, _, _, _, _, hm7, _, hm9, _⟩ := hhdr
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  have hkb_eq : keysBase base c_exp n_max = t1Base base c_exp n_max + 2 * tableSize n_max := by
    wram_omega
  unfold clearTablesCode clearTablesSteps loadHeaderCode
  wram_exec [h0, hm7, hm9]
  wram_call (zeroRangeLoop_exec (2 * tableSize n_max) (t1Base base c_exp n_max) (by wram_simp)
    (by wram_simp [hkb_eq]) (by wram_simp) (by wram_simp) (by rw [← hkb_eq]; wram_omega))
    with y ⟨hy_0, hy_zero, hy_frame⟩
  rw [← hkb_eq] at hy_zero hy_frame
  exact ⟨by omega, by regs_frame, by struct_frame hhdr,
    ⟨by mem_frame, by mem_frame⟩, by mem_frame⟩

/-- Index-based replay of `rem` remaining keys of `ks` starting at index `i` from `tbl`. -/
private def pureReplayFrom {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (ks : List (Fin U)) :
    ℕ → ℕ → PureTable U m → Option (PureTable U m)
  | 0, _, tbl => some tbl
  | rem + 1, i, tbl =>
    if h : i < ks.length then
      match pureEvict h₁ h₂ maxLoop tbl ⟨ks[i], i⟩ with
      | some tbl' => pureReplayFrom h₁ h₂ maxLoop ks rem (i + 1) tbl'
      | none => none
    else some tbl

private theorem pureReplayFrom_eq_foldlM {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (ks : List (Fin U)) :
    ∀ (sfx pfx : List (Fin U)) (tbl : PureTable U m),
      ks = pfx ++ sfx →
      pureReplayFrom h₁ h₂ maxLoop ks sfx.length pfx.length tbl =
        (sfx.zipIdx pfx.length).foldlM
          (fun t p => pureEvict h₁ h₂ maxLoop t ⟨p.1, p.2⟩) tbl
  | [], pfx, tbl, _ => rfl
  | u :: sfx, pfx, tbl, hks => by
    have hlt : pfx.length < ks.length := by
      rw [hks, List.length_append, List.length_cons]; omega
    have hget : ks[pfx.length] = u := by
      subst hks
      simp
    simp only [List.length_cons, pureReplayFrom, hlt, ↓reduceDIte, hget,
      List.zipIdx_cons, List.foldlM_cons]
    cases hev : pureEvict h₁ h₂ maxLoop tbl ⟨u, pfx.length⟩ with
    | none => rfl
    | some tbl' =>
      have hks' : ks = (pfx ++ [u]) ++ sfx := by
        rw [List.append_assoc, List.singleton_append]; exact hks
      have hlen' : (pfx ++ [u]).length = pfx.length + 1 := by simp
      rw [← hlen']
      exact pureReplayFrom_eq_foldlM h₁ h₂ maxLoop ks sfx (pfx ++ [u]) tbl' hks'

private theorem pureReplayFrom_eq_pureReplay {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (ks : List (Fin U)) :
    pureReplayFrom h₁ h₂ maxLoop ks ks.length 0 (PureTable.empty U m) =
      pureReplay h₁ h₂ maxLoop ks :=
  pureReplayFrom_eq_foldlM h₁ h₂ maxLoop ks ks [] (PureTable.empty U m) rfl

private def syncReplayCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 17)
  (.seq (loadHeaderCode 17 5)
  (.seq (loadHeaderCode 18 16)
  (.seq (.op (.const 15 0))
  (.branch (.eq 18 15)
    (.seq (.op (.const 15 0)) (.op (.const 15 0)))
    (.op (.copy 16 17))))))

private theorem syncReplayCondCode_exec {w base c_exp n_max idx allocCount act : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm5 : x.mem (base + 5) = allocCount)
    (hm16 : x.mem (base + 16) = act)
    (hm17 : x.mem (base + 17) = idx)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w syncReplayCondCode x y 13 ∧
      y.regs 0 = base ∧
      y.regs 16 = (if act = 0 then idx else allocCount) ∧
      y.regs 17 = allocCount ∧
      y.mem = x.mem := by
  have hle_sp := le_space c_exp n_max
  unfold syncReplayCondCode loadHeaderCode
  by_cases hact : act = 0 <;>
    wram_exec [h0, hm5, hm16, hm17, hact] <;>
    exact ⟨by regs_frame, by wram_simp [hact], by wram_simp, rfl⟩

private def replayIterSetupCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 17)
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 18 16))
  (.seq (storeHeaderCode 11 18)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 17 17 15))
  (.seq (storeHeaderCode 17 17)
  (.seq (loadHeaderCode 18 4)
  (.seq (storeHeaderCode 15 18)
        (storeHeaderConstCode 16 1)))))))))))

private theorem replayIterSetupCode_exec {w base c_exp n_max U idx : ℕ}
    {ks : List (Fin U)} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hm17 : x.mem (base + 17) = idx)
    (hlt : idx < ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base c_exp n_max + j) = ks[j].val)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w replayIterSetupCode x y 29 ∧
      y.regs 0 = base ∧
      y.mem (base + 11) = ks[idx].val ∧
      y.mem (base + 12) = idx ∧
      y.mem (base + 15) = maxEvictions n_max ∧
      y.mem (base + 16) = 1 ∧
      y.mem (base + 17) = idx + 1 ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 →
        a ≠ base + 16 → a ≠ base + 17 → y.mem a = x.mem a) := by
  have ⟨_, _, _, _, hm4, _, _, _, hm9, _⟩ := hhdr
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  wram_exec [replayIterSetupCode, loadHeaderCode, storeHeaderConstCode, storeHeaderCode,
    h0, hm17, hm9, hm4, hmem_keys idx hlt]
  exact ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by mem_frame⟩

private def replayLoopInner (c_exp n_max : ℕ) : Code .exact 19 :=
  .loop (.lt 16 17)
    (.seq replayIterSetupCode
    (.seq (evictLoopCode c_exp n_max)
          syncReplayCondCode))

private def replayIterSteps (c_exp n_max U : ℕ) : ℕ :=
  maxEvictions n_max * evictIterSteps c_exp n_max U + 54

private def replayLoopCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (storeHeaderConstCode 17 0)
  (.seq (storeHeaderConstCode 16 0)
  (.seq syncReplayCondCode
        (replayLoopInner c_exp n_max)))

private def replayLoopSteps (c_exp n_max U : ℕ) : ℕ :=
  n_max * replayIterSteps c_exp n_max U + 23

private theorem replayLoopInner_execWithin {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)}
    (hlen_le : ks.length ≤ n_max)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∀ (rem idx : ℕ) {tbl : PureTable U (2 ^ tableBits n_max)} {x : Data 19}
      (_hhdr : HeaderConstsRep base c_exp n_max U x.mem)
      (_hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
      (_hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem)
      (_htiv : TableIdxValid ks tbl)
      (_hidx_rem : idx + rem = ks.length)
      (_hm5 : x.mem (base + 5) = ks.length)
      (_hm16 : x.mem (base + 16) = 0)
      (_hm17 : x.mem (base + 17) = idx)
      (_hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base c_exp n_max + j) = ks[j].val)
      (_h0 : x.regs 0 = base)
      (_h16 : x.regs 16 = idx)
      (_h17 : x.regs 17 = ks.length),
      ∃ y : Data 19,
        ExecWithin w (replayLoopInner c_exp n_max) x y
          (rem * replayIterSteps c_exp n_max U + 2) ∧
        y.regs 0 = base ∧
        HeaderConstsRep base c_exp n_max U y.mem ∧
        HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ y.mem ∧
        (match pureReplayFrom (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks rem idx tbl with
         | some tbl' =>
           y.mem (base + 16) = 0 ∧
           TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl' y.mem ∧
           TableIdxValid ks tbl'
         | none =>
           y.mem (base + 16) = 1) ∧
        (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
          (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a)
  | 0, idx, tbl, x, hhdr, hrep_hash, hslots, htiv, hidx_rem, _, hm16, _, _, h0, h16, h17 => by
    have hidx_eq : idx = ks.length := by omega
    have hcond : ¬(Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17, hidx_eq]
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hcond⟩, h0, hhdr, hrep_hash,
      ⟨hm16, hslots, htiv⟩, fun _ _ _ _ _ _ _ => rfl⟩
  | rem + 1, idx, tbl, x, hhdr, hrep_hash, hslots, htiv, hidx_rem, hm5, hm16, hm17,
      hmem_keys, h0, h16, h17 => by
    have hlt : idx < ks.length := by omega
    have hcond : (Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17, hlt]
    have hle_hp := le_hashPairSpace c_exp n_max
    obtain ⟨s1, he_setup, hs1_0, hs1_11, hs1_12, hs1_15, hs1_16, hs1_17, hs1_frame⟩ :=
      replayIterSetupCode_exec hhdr h0 hm17 hlt hlen_le hmem_keys hfit_end
    obtain ⟨s2, he_ev, hs2_0, hs2_hdr, hs2_hash, hs2_res, hs2_frame⟩ :=
      evictLoopCode_execWithin (e := ⟨ks[idx], idx⟩)
        (by struct_frame hhdr) (hrep_hash.congr_of_ge_hashBase (by mem_frame))
        (by struct_frame hslots) htiv ⟨hlt, List.getElem?_eq_getElem hlt⟩ hlen_le
        (by mem_frame) hs1_0 hs1_11 hs1_12 hs1_15 hs1_16 hfit_ev hw hfit_end
    have hs2_5 : s2.mem (base + 5) = ks.length := by mem_frame
    have hs2_17 : s2.mem (base + 17) = idx + 1 := by mem_frame
    obtain ⟨s3, he_sync, hs3_0, hs3_16, hs3_17, hs3_mem⟩ :=
      syncReplayCondCode_exec (c_exp := c_exp) (n_max := n_max) hs2_0 hs2_5 rfl hs2_17 hfit_end
    have he_body := he_setup.within.seq (he_ev.seq he_sync.within)
    have hbody : 29 + (evictRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl
        ⟨ks[idx], idx⟩ * evictIterSteps c_exp n_max U + 10 + 13) + 2 ≤
        replayIterSteps c_exp n_max U := by
      have := Nat.mul_le_mul_right (evictIterSteps c_exp n_max U)
        (evictRounds_le (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl ⟨ks[idx], idx⟩)
      dsimp only [replayIterSteps]
      omega
    simp only [pureReplayFrom, hlt, ↓reduceDIte]
    cases hev_eq :
        pureEvict (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl ⟨ks[idx], idx⟩ with
    | none =>
      rw [hev_eq] at hs2_res
      have hcond3 : ¬(Cond.lt 16 17 : Cond 19).Holds s3 := by
        simp [Cond.Holds, hs3_16, hs3_17, hs2_res]
      refine ⟨s3, (he_body.loop_iter hcond (ExecWithin.loop_exit hcond3)).mono
        (by rw [Nat.add_mul, Nat.one_mul]; omega), hs3_0, ?_⟩
      rw [hs3_mem]
      exact ⟨hs2_hdr, hs2_hash, hs2_res, by mem_frame⟩
    | some tbl' =>
      rw [hev_eq] at hs2_res
      obtain ⟨hs2_16_0, hs2_slots, hs2_tiv⟩ := hs2_res
      rw [hs2_16_0] at hs3_16
      simp only [↓reduceIte] at hs3_16
      rw [← hs3_mem] at hs2_hdr hs2_hash hs2_slots hs2_5 hs2_16_0 hs2_17
      obtain ⟨y, he_rec, hy_0, hy_hdr, hy_hash, hy_res, hy_frame⟩ :=
        replayLoopInner_execWithin hlen_le hfit_ev hw hfit_end rem (idx + 1) hs2_hdr hs2_hash
          hs2_slots hs2_tiv (by omega) hs2_5 hs2_16_0 hs2_17
          (by mem_frame) hs3_0 hs3_16 hs3_17
      exact ⟨y, (he_body.loop_iter hcond he_rec).mono (by rw [Nat.add_mul, Nat.one_mul]; omega),
        hy_0, hy_hdr, hy_hash, hy_res, by mem_frame⟩

private theorem replayLoopCode_execWithin {w base c_exp n_max U : ℕ}
    {θ : Seed c_exp n_max U (tableBits n_max)} {ks : List (Fin U)} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max)
      (PureTable.empty U (2 ^ tableBits n_max)) x.mem)
    (hm5 : x.mem (base + 5) = ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base c_exp n_max + j) = ks[j].val)
    (h0 : x.regs 0 = base)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (replayLoopCode c_exp n_max) x y (replayLoopSteps c_exp n_max U) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base c_exp n_max U y.mem ∧
      HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ y.mem ∧
      (match pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks with
       | some tbl' =>
         y.mem (base + 16) = 0 ∧
         TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl' y.mem ∧
         TableIdxValid ks tbl'
       | none =>
         y.mem (base + 16) = 1) ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
        (a < t1Base base c_exp n_max ∨ keysBase base c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  unfold replayLoopCode replayLoopSteps storeHeaderConstCode storeHeaderCode
  wram_exec [h0]
  refine WP.name fun s2 hs2 => ?_
  have hs2_16 : s2.mem (base + 16) = 0 := by mem_frame
  have hs2_17 : s2.mem (base + 17) = 0 := by mem_frame
  have hs2_5 : s2.mem (base + 5) = ks.length := by mem_frame
  obtain ⟨s3, he_sync, hs3_0, hs3_16, hs3_17, hs3_mem⟩ :=
    syncReplayCondCode_exec (c_exp := c_exp) (n_max := n_max) (x := s2)
      (by regs_frame) hs2_5 hs2_16 hs2_17 hfit_end
  simp only [↓reduceIte] at hs3_16
  refine WP.of_execWithin he_sync.within ?_
  wram_call (replayLoopInner_execWithin hlen_le hfit_ev hw hfit_end ks.length 0
      (by struct_frame hhdr) (hrep_hash.congr_of_ge_hashBase (by mem_frame))
      (by struct_frame hslots)
      (fun _ h => False.elim (not_entryIn_empty _ h)) (Nat.zero_add _)
      (by mem_frame) (by mem_frame) (by mem_frame)
      (by mem_frame) hs3_0 hs3_16 hs3_17)
    with y ⟨hy_0, hy_hdr, hy_hash, hy_res, hy_frame⟩
  rw [pureReplayFrom_eq_pureReplay] at hy_res
  refine ⟨?_, hy_0, hy_hdr, hy_hash, hy_res, by mem_frame⟩
  have := Nat.mul_le_mul_right (replayIterSteps c_exp n_max U) hlen_le
  omega

/-! ### Las Vegas full-table rehashing (`rehashLoopCode`, `rehashLoopCode_execCodeDist`) -/

private def syncRehashCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 16)
        (.op (.const 18 0))

private theorem syncRehashCondCode_exec {w base c_exp n_max act : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm16 : x.mem (base + 16) = act)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w syncRehashCondCode x y 4 ∧
      y.regs 0 = base ∧
      y.regs 17 = act ∧
      y.regs 18 = 0 ∧
      y.mem = x.mem := by
  have hle_sp := le_space c_exp n_max
  wram_exec [syncRehashCondCode, loadHeaderCode, h0, hm16]
  exact ⟨by regs_frame, by wram_simp, by wram_simp, rfl⟩

private def rehashAttemptCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (resampleAtBaseCode c_exp n_max)
  (.seq clearTablesCode
  (.seq (replayLoopCode c_exp n_max)
        syncRehashCondCode))

private def rehashAttemptSteps (c_exp n_max U : ℕ) : ℕ :=
  resampleAtBaseSteps c_exp n_max + clearTablesSteps n_max + replayLoopSteps c_exp n_max U + 4

/-- Loop invariant for `rehashLoopCode`: machine configuration is word-bounded, `reg 0 = base`,
the header and `HashPairTableRep` are intact, `insKeys` / `insVals` realize `(ks, s)`, and all
memory modifications since `x₀` lie inside `[base, base + space c_exp n_max)`. -/
@[expose]
def RehashLoopInv (w base c_exp n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (x₀ z : Data 19) : Prop :=
  z.Bounded w ∧
  z.regs 0 = base ∧
  HeaderConstsRep base c_exp n_max U z.mem ∧
  HashPairTableRep (hashBase base) c_exp n_max U (tableBits n_max) z.mem ∧
  KeysValsRep base c_exp n_max U V ks s z.mem ∧
  Modifies (Block.mk base (space c_exp n_max)).footprint x₀.mem z.mem

/-- Exit postcondition for `rehashLoopCode`: `RehashLoopInv` holds together with `HashPairRep`
for `θ_mem = extractSeed ... z.mem` and a valid replayed table `tbl` in `T₁, T₂`. -/
@[expose]
def RehashLoopPost (w base c_exp n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (x₀ z : Data 19) : Prop :=
  RehashLoopInv w base c_exp n_max U V ks s x₀ z ∧
  HashPairRep (hashBase base) c_exp n_max U (tableBits n_max)
    (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z.mem) z.mem ∧
  ∃ tbl : PureTable U (2 ^ tableBits n_max),
    pureReplay (evalHash1 (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z.mem))
      (evalHash2 (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z.mem))
      (maxEvictions n_max) ks = some tbl ∧
    TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl z.mem

private theorem rehashDetTail_execWithin {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ z1 : Data 19}
    (hinv : RehashLoopInv w base c_exp n_max U V ks s x₀ z1)
    (hhash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max)
      (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z1.mem) z1.mem)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    let θ₁ := extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z1.mem
    ∃ y : Data 19,
      ExecWithin w (.seq clearTablesCode (.seq (replayLoopCode c_exp n_max) syncRehashCondCode))
        z1 y (clearTablesSteps n_max + replayLoopSteps c_exp n_max U + 4) ∧
      extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem = θ₁ ∧
      LoopStateInv (.lt 18 17)
        (RehashLoopInv w base c_exp n_max U V ks s x₀)
        (RehashLoopPost w base c_exp n_max U V ks s x₀) y ∧
      (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
        θ₁ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) ∧
      (GoodForSet (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) (Dictionary.dom s) →
        ¬(Cond.lt 18 17 : Cond 19).Holds y) := by
  intro θ₁
  obtain ⟨hz1_bdd, hz1_0, hz1_hdr, _, hz1_kv, hz1_mod⟩ := hinv
  obtain ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩ := id hz1_kv
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  obtain ⟨s1, he_clr, hs1_0, hs1_hdr, hs1_slots, hs1_frame⟩ :=
    clearTablesCode_exec hz1_hdr hz1_0 hfit_end
  obtain ⟨s2, he_rep, hs2_0, hs2_hdr, hs2_hash, hs2_res, hs2_frame⟩ :=
    replayLoopCode_execWithin hs1_hdr (hhash.congr_of_footprint (by mem_frame)) hs1_slots
      (by mem_frame) hlen_le (fun j hj => by have := (hkv_idx j hj).1; mem_frame)
      hs1_0 hfit_ev hw hfit_end
  obtain ⟨y, he_sync, hy_0, hy_17, hy_18, hy_mem⟩ :=
    syncRehashCondCode_exec (c_exp := c_exp) (n_max := n_max) hs2_0 rfl hfit_end
  have hwithin : ExecWithin w
      (.seq clearTablesCode (.seq (replayLoopCode c_exp n_max) syncRehashCondCode)) z1 y
      (clearTablesSteps n_max + replayLoopSteps c_exp n_max U + 4) :=
    (he_clr.within.seq (he_rep.seq he_sync.within)).mono (by omega)
  rw [← hy_mem] at hs2_hdr hs2_hash hs2_res hs2_frame hy_17
  have hy_seed : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem = θ₁ :=
    extractSeed_congr_of_footprint (by mem_frame)
  have hy_mod : Modifies (Block.mk base (space c_exp n_max)).footprint x₀.mem y.mem := by
    mem_frame
  have hy_kv : KeysValsRep base c_exp n_max U V ks s y.mem := by struct_frame hz1_kv
  have hy_hash : HashPairRep (hashBase base) c_exp n_max U (tableBits n_max)
      (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) y.mem := by
    rw [hy_seed]; exact hs2_hash
  have hy_inv : RehashLoopInv w base c_exp n_max U V ks s x₀ y :=
    ⟨hwithin.bounded hz1_bdd, hy_0, hs2_hdr, hy_hash.1, hy_kv, hy_mod⟩
  have hiff : ¬(Cond.lt 18 17 : Cond 19).Holds y ↔
      θ₁ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks := by
    rw [mem_survivingSeeds]
    cases hrep_eq : pureReplay (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) ks with
    | none =>
      rw [hrep_eq] at hs2_res
      simp [Cond.Holds, hy_17, hy_18, hs2_res]
    | some tbl' =>
      rw [hrep_eq] at hs2_res
      simp [Cond.Holds, hy_17, hy_18, hs2_res.1]
  refine ⟨y, hwithin, hy_seed, ?_, hiff, fun hgood => hiff.mpr
    (mem_survivingSeeds_of_goodForSet hnodup (fun u hu => (hdom_iff u).mp hu) hgood)⟩
  cases hrep_eq : pureReplay (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) ks with
  | none =>
    rw [hrep_eq] at hs2_res
    exact Or.inl ⟨by simp [Cond.Holds, hy_17, hy_18, hs2_res], hy_inv⟩
  | some tbl' =>
    rw [hrep_eq] at hs2_res
    exact Or.inr ⟨by simp [Cond.Holds, hy_17, hy_18, hs2_res.1], hy_inv, hy_hash, tbl',
      by rwa [hy_seed], hs2_res.2.1⟩

/-- Under the `≤ 1 / 2` rehash failure probability bound `hreh`, every duplicate-free key list `ks`
of length at most `n_max` has a nonempty set of surviving seeds of cardinality at least half the
seed space. -/
theorem survivingSeeds_card_and_nonempty {c_exp n_max U : ℕ}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    {ks : List (Fin U)} (hnodup : ks.Nodup) (hlen : ks.length ≤ n_max) :
    Fintype.card (Seed c_exp n_max U (tableBits n_max)) ≤
      2 * (survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max)) evalHash1 evalHash2
        (maxEvictions n_max) ks).card ∧
      (survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max)) evalHash1 evalHash2
        (maxEvictions n_max) ks).Nonempty := by
  classical
  have hcard_S : ks.toFinset.card ≤ n_max := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen
  have hprob :
      (PMF.uniformOfFintype (Seed c_exp n_max U (tableBits n_max))).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks} ≤ 1 / 2 := by
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hreh ks.toFinset hcard_S)
    rintro θ ⟨hnot, -⟩ hgood
    exact hnot (mem_survivingSeeds_of_goodForSet hnodup
      (fun u hu => List.mem_toFinset.mpr hu) hgood)
  exact card_le_two_mul_card_of_uniformOfFintype_compl_le_half hprob

private theorem rehashAttemptCode_execCodeDist {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ z : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hinv : RehashLoopInv w base c_exp n_max U V ks s x₀ z)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ μ_att : PMF (Data 19),
      ExecCodeDist w (rehashAttemptCode c_exp n_max) z μ_att
        (rehashAttemptSteps c_exp n_max U) ∧
      μ_att.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        seedLaw c_exp n_max U (tableBits n_max) ∧
      (∀ y ∈ μ_att.support,
        LoopStateInv (.lt 18 17)
          (RehashLoopInv w base c_exp n_max U V ks s x₀)
          (RehashLoopPost w base c_exp n_max U V ks s x₀) y ∧
        (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
          extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem ∈
            survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks)) ∧
      (1 : ℝ≥0∞) / 2 ≤ μ_att.toOuterMeasure {y | ¬(Cond.lt 18 17 : Cond 19).Holds y} := by
  classical
  obtain ⟨hz_bdd, hz_0, hz_hdr, hz_tab, hz_kv, hz_mod⟩ := hinv
  have hle_sp := le_space c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  obtain ⟨μ_res, hres_dist, hres_law, hres_supp⟩ :=
    resampleAtBaseCode_execCodeDist (w := w) (base := base) (c_exp := c_exp) (n_max := n_max)
      (U := U) (x := z) hz_tab hz_0 hfit_end hfit_q
  have hz1_inv : ∀ z1 ∈ μ_res.support,
      RehashLoopInv w base c_exp n_max U V ks s x₀ z1 ∧
      HashPairRep (hashBase base) c_exp n_max U (tableBits n_max)
        (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) z1.mem) z1.mem := by
    intro z1 hz1
    obtain ⟨hz1_0, hz1_hash, hz1_frame⟩ := hres_supp z1 hz1
    have hle_hp := le_hashPairSpace c_exp n_max
    exact ⟨⟨hres_dist.bounded hz_bdd z1 hz1, hz1_0,
      by struct_frame hz_hdr, hz1_hash.1, by struct_frame hz_kv, by mem_frame⟩, hz1_hash⟩
  choose! tailFn h_exec h_seed h_inv h_iff h_good using fun z1 (hz1 : z1 ∈ μ_res.support) =>
    rehashDetTail_execWithin (hz1_inv z1 hz1).1 (hz1_inv z1 hz1).2 hfit_ev hw hfit_end
  let μ_att : PMF (Data 19) := μ_res.map tailFn
  have hfull :
      ExecCodeDist w (rehashAttemptCode c_exp n_max) z μ_att
        (rehashAttemptSteps c_exp n_max U) := by
    unfold rehashAttemptCode rehashAttemptSteps
    apply WP.Dist.execCodeDist
    wram_rand_call hres_dist with z1 hz1
    · wram_rand_call (h_exec z1 hz1)
      exact ⟨rfl, le_rfl⟩
    · exact ⟨by simp only [μ_att, ← PMF.bind_pure_comp, Function.comp_def], by norm_cast; omega⟩
  have hlaw_att :
      μ_att.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        seedLaw c_exp n_max U (tableBits n_max) := by
    dsimp only [μ_att]
    rw [PMF.map_comp]
    exact (PMF.map_congr_on_support _ _ _ fun z1 hz1 => h_seed z1 hz1).trans hres_law
  refine ⟨μ_att, hfull, hlaw_att, ?_, ?_⟩
  · intro y hy
    dsimp only [μ_att] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z1, hz1, rfl⟩ := hy
    exact ⟨h_inv z1 hz1, by rw [h_seed z1 hz1]; exact h_iff z1 hz1⟩
  · let G : Set (Seed c_exp n_max U (tableBits n_max)) :=
      {θ' | GoodForSet (evalHash1 θ') (evalHash2 θ') (maxEvictions n_max) (Dictionary.dom s)}
    have hcard_le : (Dictionary.dom s).card ≤ n_max := by
      rw [hz_kv.card_dom_eq]; exact hz_kv.2.1
    have hgood_prob :
        (1 : ℝ≥0∞) / 2 ≤ (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure G := by
      refine (ENNReal.add_le_add_iff_right (by norm_num : (1 : ℝ≥0∞) / 2 ≠ ⊤)).mp ?_
      calc (1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 2
        _ = (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure G +
              (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure Gᶜ :=
            (ENNReal.add_halves 1).trans (toOuterMeasure_add_compl_ennreal _ G).symm
        _ ≤ (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure G + (1 : ℝ≥0∞) / 2 :=
            add_le_add le_rfl (hreh (Dictionary.dom s) hcard_le)
    rw [← hlaw_att, PMF.toOuterMeasure_map_apply] at hgood_prob
    refine le_trans hgood_prob (PMF.toOuterMeasure_mono μ_att ?_)
    rintro y ⟨hyG, hy⟩
    dsimp only [μ_att] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z1, hz1, rfl⟩ := hy
    have hyG' : GoodForSet
        (evalHash1 (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) (tailFn z1).mem))
        (evalHash2 (extractSeed (hashBase base) c_exp n_max U (tableBits n_max) (tailFn z1).mem))
        (maxEvictions n_max) (Dictionary.dom s) := hyG
    rw [h_seed z1 hz1] at hyG'
    exact h_good z1 hz1 hyG'

/-- Las Vegas rehash loop: synchronizes `(Cond.lt 18 17)` from `mem[base + 16]` and repeats
`rehashAttemptCode` while `0 < mem[base + 16]`. -/
def rehashLoopCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq syncRehashCondCode
        (.loop (.lt 18 17) (rehashAttemptCode c_exp n_max))

/-- Expected step bound for `rehashLoopCode`. -/
def rehashLoopSteps (c_exp n_max U : ℕ) : ℕ :=
  2 * rehashAttemptSteps c_exp n_max U + 10

theorem rehashLoopSteps_eq (c_exp n_max U : ℕ) :
    rehashLoopSteps c_exp n_max U =
      2 * (resampleAtBaseSteps c_exp n_max + (8 * tableSize n_max + 10) +
        (n_max * (maxEvictions n_max * evictIterSteps c_exp n_max U + 54) + 23) + 4) + 10 := by
  unfold rehashLoopSteps rehashAttemptSteps clearTablesSteps replayLoopSteps replayIterSteps
  rfl

/-- Geometric Las Vegas termination, expected step bound, and exact conditional-uniform exit law for
`rehashLoopCode`. -/
theorem rehashLoopCode_execCodeDist {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hinv : RehashLoopInv w base c_exp n_max U V ks s x₀ x)
    (hm16 : x.mem (base + 16) = 1)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ (μ_reh : PMF (Data 19))
      (hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty),
      ExecCodeDist w (rehashLoopCode c_exp n_max) x μ_reh (rehashLoopSteps c_exp n_max U) ∧
      μ_reh.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE ∧
      ∀ y ∈ μ_reh.support, RehashLoopPost w base c_exp n_max U V ks s x₀ y := by
  classical
  have hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty :=
    (survivingSeeds_card_and_nonempty hreh hinv.2.2.2.2.1.1 hinv.2.2.2.2.1.2.1).2
  obtain ⟨s1, he_sync, hs1_0, hs1_17, hs1_18, hs1_mem⟩ :=
    syncRehashCondCode_exec (c_exp := c_exp) (n_max := n_max) hinv.2.1 hm16 hfit_end
  have hs1_inv : RehashLoopInv w base c_exp n_max U V ks s x₀ s1 := by
    refine ⟨he_sync.bounded hinv.1, hs1_0, ?_⟩
    rw [hs1_mem]
    exact hinv.2.2
  let I := RehashLoopInv w base c_exp n_max U V ks s x₀
  let Q := RehashLoopPost w base c_exp n_max U V ks s x₀
  choose! μ_body h_dist h_law h_supp h_half using fun z (hz : I z) =>
    rehashAttemptCode_execCodeDist hreh hz hfit_ev hw hfit_end hfit_q
  have hp_pos : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  have hp_top : ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by norm_num
  have hs1_cond : (Cond.lt 18 17 : Cond 19).Holds s1 := by
    simp [Cond.Holds, hs1_17, hs1_18]
  have hs1_loop_inv : LoopStateInv (.lt 18 17) I Q s1 :=
    Or.inl ⟨hs1_cond, hs1_inv⟩
  have hloop := ExecCodeDist.loop_geometric I Q hp_pos hp_top
    (μ_body := μ_body)
    (T_body := fun _ => (rehashAttemptSteps c_exp n_max U : ℝ≥0∞))
    (B_body := (rehashAttemptSteps c_exp n_max U : ℝ≥0∞))
    (x := s1)
    (fun z hz _ => h_dist z hz)
    (fun _ _ _ => le_rfl)
    (fun z hz _ y hy => (h_supp z hz y hy).1)
    (fun z hz _ => h_half z hz)
    hs1_loop_inv
  have hdiv : ((rehashAttemptSteps c_exp n_max U : ℝ≥0∞) + 2) / ((1 : ℝ≥0∞) / 2) ≤
      2 * ((rehashAttemptSteps c_exp n_max U : ℝ≥0∞) + 2) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      two_mul, add_mul, ← mul_add, ENNReal.add_halves 1, mul_one]
  have hseq := (ExecCodeDist.of_exec he_sync).seq_pure hloop
  refine ⟨loopExitPMF (.lt 18 17) μ_body s1, hE, hseq.mono ?_, ?_, ?_⟩
  · calc (4 : ℝ≥0∞) + (((rehashAttemptSteps c_exp n_max U : ℝ≥0∞) + 2) / (1 / 2) + 2)
      _ ≤ 4 + (2 * ((rehashAttemptSteps c_exp n_max U : ℝ≥0∞) + 2) + 2) :=
          add_le_add le_rfl (add_le_add hdiv le_rfl)
      _ = (rehashLoopSteps c_exp n_max U : ℝ≥0∞) := by
          dsimp only [rehashLoopSteps]
          push_cast
          ring
  · exact loopExitPMF_map_eq_uniformOfFinset hE hp_pos hp_top
      (fun z hz _ => h_supp z hz) (fun z hz _ => h_half z hz) (fun z hz _ => h_law z hz)
      hs1_inv hs1_cond
  · intro y hy
    exact (mem_support_loopExitPMF hp_pos hp_top
      (fun z hz _ y hy => (h_supp z hz y hy).1) (fun z hz _ => h_half z hz)
      hs1_loop_inv hy).1.2

/-! ### Dictionary insertion (`insertCode`, `insertCode_execCodeDist`) -/

private theorem KeysValsRep.insert_of_mem {base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {u : Fin U} {v idx : ℕ} {mem mem' : ℕ → ℕ}
    (hkv : KeysValsRep base c_exp n_max U V ks s mem)
    (hv : v < V)
    (hidx_lt : idx < ks.length)
    (hks_idx : ks[idx] = u)
    (h5 : mem' (base + 5) = mem (base + 5))
    (hk : ∀ j < ks.length,
      mem' (keysBase base c_exp n_max + j) = mem (keysBase base c_exp n_max + j))
    (hv_eq : mem' (valsBase base c_exp n_max + idx) = v)
    (hv_other : ∀ j < ks.length, j ≠ idx →
      mem' (valsBase base c_exp n_max + j) = mem (valsBase base c_exp n_max + j)) :
    KeysValsRep base c_exp n_max U V ks (Function.update s u (some v)) mem' := by
  rcases hkv with ⟨hnodup, hlen, hm5, hdom, hkv_idx, hvb⟩
  have hu_mem : u ∈ ks := hks_idx ▸ List.getElem_mem hidx_lt
  have hdom_ins : Dictionary.dom (Function.update s u (some v)) = Dictionary.dom s :=
    Dictionary.dom_insert_of_mem ((hdom u).mp hu_mem) v
  refine ⟨hnodup, hlen, h5.trans hm5, fun u' => ?_, fun j hj => ?_,
    Dictionary.valuesBounded_step_of_valid (n_max := (Dictionary.dom s).card + 1)
      (o := .insert u v) hvb ⟨Or.inl (Nat.lt_succ_self _), hv⟩⟩
  · rw [hdom_ins]; exact hdom u'
  · refine ⟨(hk j hj).trans (hkv_idx j hj).1, ?_⟩
    by_cases hj_eq : j = idx
    · subst hj_eq
      rw [hks_idx, Function.update_self, hv_eq]
    · have hne_key : ks[j] ≠ u := by
        rw [← hks_idx]
        exact (List.Nodup.getElem_inj_iff hnodup).not.mpr hj_eq
      rw [Function.update_of_ne hne_key, hv_other j hj hj_eq]
      exact (hkv_idx j hj).2

private theorem KeysValsRep.insert_of_notMem {base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {u : Fin U} {v : ℕ} {mem mem' : ℕ → ℕ}
    (hkv : KeysValsRep base c_exp n_max U V ks s mem)
    (hv : v < V)
    (hu_notMem : u ∉ ks)
    (hlen_lt : ks.length < n_max)
    (h5 : mem' (base + 5) = ks.length + 1)
    (hk_old : ∀ j < ks.length,
      mem' (keysBase base c_exp n_max + j) = mem (keysBase base c_exp n_max + j))
    (hk_new : mem' (keysBase base c_exp n_max + ks.length) = u.val)
    (hv_old : ∀ j < ks.length,
      mem' (valsBase base c_exp n_max + j) = mem (valsBase base c_exp n_max + j))
    (hv_new : mem' (valsBase base c_exp n_max + ks.length) = v) :
    KeysValsRep base c_exp n_max U V (ks ++ [u]) (Function.update s u (some v)) mem' := by
  rcases hkv with ⟨hnodup, _, _, hdom, hkv_idx, hvb⟩
  have hnodup' : (ks ++ [u]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton u, fun x hx y hy hxy => ?_⟩
    rw [List.mem_singleton] at hy
    subst hy; subst hxy
    exact hu_notMem hx
  have hlen' : (ks ++ [u]).length ≤ n_max := by simp; omega
  have hm5' : mem' (base + 5) = (ks ++ [u]).length := by simp [h5]
  refine ⟨hnodup', hlen', hm5', fun u' => ?_, fun j hj => ?_,
    Dictionary.valuesBounded_step_of_valid (n_max := (Dictionary.dom s).card + 1)
      (o := .insert u v) hvb ⟨Or.inl (Nat.lt_succ_self _), hv⟩⟩
  · rw [List.mem_append, List.mem_singleton, Dictionary.dom_insert, Finset.mem_insert,
      hdom u', or_comm]
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hj_lt : j < ks.length
    · rw [List.getElem_append_left hj_lt]
      have hne_key : ks[j] ≠ u := fun h => hu_notMem (h ▸ List.getElem_mem hj_lt)
      refine ⟨(hk_old j hj_lt).trans (hkv_idx j hj_lt).1, ?_⟩
      rw [Function.update_of_ne hne_key, hv_old j hj_lt]
      exact (hkv_idx j hj_lt).2
    · have hj_eq : j = ks.length := by omega
      subst hj_eq
      simp only [List.getElem_concat_length]
      exact ⟨hk_new, by rw [Function.update_self, hv_new]⟩

/-- Shared state after loading `mem[base + off]` into `reg 16` and `0` into `reg 15` inside
`branchHeaderPosCode`. -/
private def prepHeaderFlagData (base off : ℕ) (x : Data 19) : Data 19 :=
  (((x.set 15 off).set 16 (base + off)).set 16 (x.mem (base + off))).set 15 0

private theorem prepHeaderFlag_exec {w base c_exp n_max off : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base) (hoff : off < 20)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    Exec w (.seq (loadHeaderCode 16 off) (.op (.const 15 0))) x
      (prepHeaderFlagData base off x) 4 := by
  have hle_sp := le_space c_exp n_max
  exact (loadHeaderCode_exec 16 h0 (by fits) (by fits)).seq (Exec.const (by fits))

private theorem branchHeaderPosCode_execCodeDist_zero {w base c_exp n_max off : ℕ}
    {posCode zeroCode : Code .exact 19} {x : Data 19} {μ : PMF (Data 19)} {B : ℝ≥0∞}
    (h0 : x.regs 0 = base) (hoff : off < 20)
    (hm : x.mem (base + off) = 0)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hz : ExecCodeDist w zeroCode (prepHeaderFlagData base off x) μ B) :
    ExecCodeDist w (branchHeaderPosCode off posCode zeroCode) x μ (B + (6 : ℕ)) := by
  have hle_sp := le_space c_exp n_max
  have hnc : ¬(Cond.lt 15 16 : Cond 19).Holds (prepHeaderFlagData base off x) := by
    simp +decide [Cond.Holds, prepHeaderFlagData, hm]
  exact ((ExecCodeDist.of_exec (loadHeaderCode_exec (w := w) (off := off) 16 h0
    (by fits) (by fits))).seq_pure
    ((ExecCodeDist.of_exec (Exec.const (d := (15 : Fin 19)) (v := 0) (by fits))).seq_pure
      (ExecCodeDist.branch_neg hnc hz))).mono
    (le_of_eq (by push_cast; ring))

private theorem branchHeaderPosCode_execCodeDist_pos {w base c_exp n_max off : ℕ}
    {posCode zeroCode : Code .exact 19} {x : Data 19} {μ : PMF (Data 19)} {B : ℝ≥0∞}
    (h0 : x.regs 0 = base) (hoff : off < 20)
    (hm : 0 < x.mem (base + off))
    (hfit_end : Fits w (base + space c_exp n_max))
    (hp : ExecCodeDist w posCode (prepHeaderFlagData base off x) μ B) :
    ExecCodeDist w (branchHeaderPosCode off posCode zeroCode) x μ (B + (5 : ℕ)) := by
  have hle_sp := le_space c_exp n_max
  have hc : (Cond.lt 15 16 : Cond 19).Holds (prepHeaderFlagData base off x) := by
    simp [Cond.Holds, prepHeaderFlagData, hm]
  exact ((ExecCodeDist.of_exec (loadHeaderCode_exec (w := w) (off := off) 16 h0
    (by fits) (by fits))).seq_pure
    ((ExecCodeDist.of_exec (Exec.const (d := (15 : Fin 19)) (v := 0) (by fits))).seq_pure
      (ExecCodeDist.branch_pos hc hp))).mono
    (le_of_eq (by push_cast; ring))

private def insertOverwriteBranchCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 14)
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 18)
  (.seq (.op (.store 16 18))
        (.op (.const 2 0))))))

private theorem insertOverwriteBranchCode_exec {w base c_exp n_max idx v : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm10 : x.mem (base + 10) = valsBase base c_exp n_max)
    (hm14 : x.mem (base + 14) = idx)
    (hm18 : x.mem (base + 18) = v)
    (hidx_lt : idx < n_max)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w insertOverwriteBranchCode x y 12 ∧
      y.regs 0 = base ∧
      y.regs 2 = 0 ∧
      y.mem (valsBase base c_exp n_max + idx) = v ∧
      (∀ a, a ≠ valsBase base c_exp n_max + idx → y.mem a = x.mem a) := by
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  wram_exec [insertOverwriteBranchCode, loadHeaderCode, h0, hm10, hm14, hm18]
  exact ⟨by regs_frame, by wram_simp, by wram_simp, by mem_frame⟩

private def insertNewKeySetupCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 5)
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 11)
  (.seq (.op (.store 16 18))
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 18)
  (.seq (.op (.store 16 18))
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 17 17 15))
  (.seq (storeHeaderCode 5 17)
  (.seq (loadHeaderCode 18 4)
  (.seq (storeHeaderCode 15 18)
        (storeHeaderConstCode 16 1)))))))))))))))

private theorem insertNewKeySetupCode_exec {w base c_exp n_max U idx u_val v : ℕ} {x : Data 19}
    (hhdr : HeaderConstsRep base c_exp n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hm5 : x.mem (base + 5) = idx)
    (hm11 : x.mem (base + 11) = u_val)
    (hm18 : x.mem (base + 18) = v)
    (hidx_lt : idx < n_max)
    (hfit_end : Fits w (base + space c_exp n_max)) :
    ∃ y : Data 19,
      Exec w insertNewKeySetupCode x y 37 ∧
      y.regs 0 = base ∧
      y.mem (base + 5) = idx + 1 ∧
      y.mem (base + 11) = u_val ∧
      y.mem (base + 12) = idx ∧
      y.mem (base + 15) = maxEvictions n_max ∧
      y.mem (base + 16) = 1 ∧
      y.mem (keysBase base c_exp n_max + idx) = u_val ∧
      y.mem (valsBase base c_exp n_max + idx) = v ∧
      (∀ a, a ≠ base + 5 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        a ≠ keysBase base c_exp n_max + idx → a ≠ valsBase base c_exp n_max + idx →
        y.mem a = x.mem a) := by
  have ⟨_, _, _, _, hm4, _, _, _, hm9, hm10⟩ := hhdr
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  wram_exec [insertNewKeySetupCode, loadHeaderCode, storeHeaderConstCode, storeHeaderCode,
    h0, hm5, hm9, hm11, hm10, hm18, hm4]
  exact ⟨by regs_frame, by mem_frame, by mem_frame, by mem_frame, by mem_frame, by mem_frame,
    by mem_frame, by mem_frame, by mem_frame⟩

private def insertNewKeyBranchCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq insertNewKeySetupCode
  (.seq (evictLoopCode c_exp n_max)
        (branchHeaderPosCode 16
          (.seq (rehashLoopCode c_exp n_max) (.op (.const 2 0)))
          (.op (.const 2 0))))

/-- Full `insert` operation (`insertCode`): stores `u.val = reg 3` in `mem[base + 11]` and
`v = reg 4` in `mem[base + 18]`, runs `probeKeyCode`, and branches on `foundFlag = mem[base + 13]`
between in-place value overwrite and new-key insertion with bounded eviction and Las Vegas rehash.
-/
def insertCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (storeHeaderCode 11 3)
  (.seq (storeHeaderCode 18 4)
  (.seq (probeKeyCode c_exp n_max)
        (branchHeaderPosCode 13 insertOverwriteBranchCode (insertNewKeyBranchCode c_exp n_max))))

/-- Base step overhead of `insertCode` outside the eviction and rehash loops. -/
@[expose]
def insertBaseSteps (c_exp n_max U : ℕ) : ℕ :=
  probeKeySteps c_exp n_max U + 66

/-- Worst-case expected step bound of `insertCode` when a rehash may be triggered. -/
@[expose]
def insertWorstSteps (c_exp n_max U : ℕ) : ℕ :=
  insertBaseSteps c_exp n_max U + maxEvictions n_max * evictIterSteps c_exp n_max U +
    rehashLoopSteps c_exp n_max U + 2

/-- State-and-seed-dependent step bound for `insertCode` on insertion-order key list `ks`,
seed `θ`, dictionary state `s`, and key `u`. -/
@[expose]
noncomputable def insertSeedSteps (c_exp n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed c_exp n_max U (tableBits n_max)) (s : Dictionary.State U) (u : Fin U) : ℝ≥0∞ := by
  classical
  exact
    if u ∈ Dictionary.dom s then
      (insertBaseSteps c_exp n_max U : ℝ≥0∞)
    else if θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) ∨
        θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks then
      (insertBaseSteps c_exp n_max U +
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps c_exp n_max U : ℕ)
    else
      (insertWorstSteps c_exp n_max U : ℝ≥0∞)

theorem insertSeedSteps_le_insertWorstSteps (c_exp n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed c_exp n_max U (tableBits n_max)) (s : Dictionary.State U) (u : Fin U) :
    insertSeedSteps c_exp n_max U ks θ s u ≤ (insertWorstSteps c_exp n_max U : ℝ≥0∞) := by
  classical
  dsimp only [insertSeedSteps]
  split_ifs
  · exact_mod_cast (by dsimp only [insertWorstSteps]; omega :
      insertBaseSteps c_exp n_max U ≤ insertWorstSteps c_exp n_max U)
  · have hwalk := cuckooWalkRounds_le_maxLoop (evalHash1 θ) (evalHash2 θ)
      (maxEvictions n_max) (Dictionary.dom s) u
    have hmul :
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps c_exp n_max U ≤
          maxEvictions n_max * evictIterSteps c_exp n_max U :=
      Nat.mul_le_mul_right _ hwalk
    exact_mod_cast (by dsimp only [insertWorstSteps]; omega :
      insertBaseSteps c_exp n_max U +
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps c_exp n_max U ≤ insertWorstSteps c_exp n_max U)
  · exact le_rfl

/-- Insertion-order key list after executing dictionary operation `o` from key list `ks`. -/
@[expose]
def stepKeys {U : ℕ} (ks : List (Fin U)) : Dictionary.Op U → List (Fin U)
  | .query _ => ks
  | .insert u _ => if u ∈ ks then ks else ks ++ [u]

theorem survivingSeeds_stepKeys_subset {U : ℕ} (c_exp n_max : ℕ) (ks : List (Fin U))
    (o : Dictionary.Op U) :
    survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) ⊆
      survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) ks := by
  cases o with
  | query _ => exact Finset.Subset.refl _
  | insert u _ =>
    dsimp only [stepKeys]
    split_ifs
    · exact Finset.Subset.refl _
    · exact survivingSeeds_append_subset _ _ _ _ _

private theorem unpackRepWithKeys {w base c_exp n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {x : Data 19}
    {θ : Seed c_exp n_max U (tableBits n_max)}
    (hrep : RepWithKeys w base c_exp n_max U V ks s x)
    (hθ : θ = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem) :
    x.Bounded w ∧ x.regs 0 = base ∧ HeaderConstsRep base c_exp n_max U x.mem ∧
    HashPairRep (hashBase base) c_exp n_max U (tableBits n_max) θ x.mem ∧
    KeysValsRep base c_exp n_max U V ks s x.mem ∧
    ∃ tbl : PureTable U (2 ^ tableBits n_max),
      pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks = some tbl ∧
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl x.mem := by
  subst hθ; exact hrep

open Classical in
private theorem insertNewKeyBranchCode_execCodeDist {w base c_exp n_max U V v : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    {u : Fin U} {x₀ x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hrep : RepWithKeys w base c_exp n_max U V ks s x)
    (hm11 : x.mem (base + 11) = u.val)
    (hm18 : x.mem (base + 18) = v)
    (hu_notMem : u ∉ ks)
    (hlen_lt : ks.length < n_max)
    (hv : v < V)
    (hmod : Modifies (Block.mk base (space c_exp n_max)).footprint x₀.mem x.mem)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem
    ∃ (μ_br : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u])).Nonempty),
      ExecCodeDist w (insertNewKeyBranchCode c_exp n_max) x μ_br
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) then
          (cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
            (Dictionary.dom s) u * evictIterSteps c_exp n_max U + 54 : ℕ)
         else
          (maxEvictions n_max * evictIterSteps c_exp n_max U + 54 +
            rehashLoopSteps c_exp n_max U + 2 : ℕ)) ∧
      μ_br.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u])) hE') ∧
      ∀ y ∈ μ_br.support,
        y.regs 2 = 0 ∧
        RepWithKeys w base c_exp n_max U V (ks ++ [u]) (Function.update s u (some v)) y ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x₀.mem y.mem := by
  classical
  intro θ_mem
  obtain ⟨hx_bdd, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ :=
    unpackRepWithKeys (θ := θ_mem) hrep rfl
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  have hfit_0 : Fits w 0 := by fits
  obtain ⟨s1, he_setup, hs1_0, hs1_5, hs1_11, hs1_12, hs1_15, hs1_16, hs1_knew, hs1_vnew,
      hs1_frame⟩ :=
    insertNewKeySetupCode_exec hhdr h0 hkv.2.2.1 hm11 hm18 hlen_lt hfit_end
  have hs1_kv :
      KeysValsRep base c_exp n_max U V (ks ++ [u]) (Function.update s u (some v)) s1.mem :=
    hkv.insert_of_notMem hv hu_notMem hlen_lt hs1_5 (by mem_frame) hs1_knew
      (by mem_frame) hs1_vnew
  have hs1_tiv : TableIdxValid (ks ++ [u]) tbl := by
    intro e he
    obtain ⟨hlt, hget⟩ := pureReplay_tableIdxValid hkv.1 hreplay e he
    exact ⟨by simp; omega, by rw [List.getElem?_append_left hlt]; exact hget⟩
  obtain ⟨s2, ⟨t_ev, ht_ev, he_ev⟩, hs2_0, hs2_hdr, hs2_hash, hs2_res, hs2_frame⟩ :=
    evictLoopCode_execWithin (ks := ks ++ [u]) (e := ⟨u, ks.length⟩)
      (by struct_frame hhdr) (hhash.congr_of_footprint (by mem_frame))
      (by struct_frame hslots)
      hs1_tiv ⟨by simp, by simp⟩ hs1_kv.2.1 (fun idx hidx => (hs1_kv.2.2.2.2.1 idx hidx).1)
      hs1_0 hs1_11 hs1_12 hs1_15 hs1_16 hfit_ev hw hfit_end
  set s4 := prepHeaderFlagData base 16 s2
  have hs4_mem : s4.mem = s2.mem := rfl
  have hs4_0 : s4.regs 0 = base := by simp +decide [s4, prepHeaderFlagData, hs2_0]
  have hs4_kv :
      KeysValsRep base c_exp n_max U V (ks ++ [u]) (Function.update s u (some v)) s4.mem := by
    rw [hs4_mem]; struct_frame hs1_kv
  have hs4_mod : Modifies (Block.mk base (space c_exp n_max)).footprint x₀.mem s4.mem := by
    rw [hs4_mem]; mem_frame
  have hs4_seed : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) s4.mem = θ_mem := by
    rw [hs4_mem]; exact extractSeed_congr_of_footprint (by mem_frame)
  have he_pref : Exec w (.seq insertNewKeySetupCode (evictLoopCode c_exp n_max)) x s2
      (37 + t_ev) := he_setup.seq he_ev
  cases hev_eq : pureEvict (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl
      ⟨u, ks.length⟩ with
  | some tbl' =>
    rw [hev_eq] at hs2_res
    obtain ⟨hs2_16_0, hs2_slots, _⟩ := hs2_res
    have hrep_app : pureReplay (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
        (ks ++ [u]) = some tbl' := by
      rw [pureReplay_append_singleton, hreplay]
      simp [hev_eq]
    have hmem_surv :
        θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) := by
      rw [mem_survivingSeeds, hrep_app]
      rfl
    let y₀ := s4.set 2 0
    have hwalk_mul := Nat.mul_le_mul_right (evictIterSteps c_exp n_max U)
      (evictRounds_le_cuckooWalkRounds (maxLoop := maxEvictions n_max)
        (pureReplay_validPlacement hkv.1 (fun x hx => (hkv.2.2.2.1 x).mp hx) hreplay)
        u ks.length)
    have hbr := branchHeaderPosCode_execCodeDist_zero (posCode :=
        .seq (rehashLoopCode c_exp n_max) (.op (.const 2 0))) hs2_0 (by decide) hs2_16_0 hfit_end
      (ExecCodeDist.of_exec (Exec.const (d := 2) hfit_0))
    have hdist : ExecCodeDist w (insertNewKeyBranchCode c_exp n_max) x (PMF.pure y₀)
        (cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
          (Dictionary.dom s) u * evictIterSteps c_exp n_max U + 54 : ℕ) :=
      ((ExecCodeDist.of_exec he_setup).seq_pure
        ((ExecCodeDist.of_exec he_ev).seq_pure hbr)).mono (by norm_cast; omega)
    refine ⟨PMF.pure y₀, ⟨θ_mem, hmem_surv⟩, ?_, ?_, ?_⟩
    · simp only [hmem_surv, ↓reduceIte]; exact hdist
    · simp only [hmem_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply]
      exact congrArg PMF.pure hs4_seed
    · intro y hy
      have hy_bdd := hdist.bounded hx_bdd y hy
      rw [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨by wram_simp [y₀], ⟨hy_bdd, by wram_simp [y₀, hs4_0], hs2_hdr,
        hs4_seed ▸ hs2_hash, hs4_kv, tbl', hs4_seed ▸ hrep_app, hs2_slots⟩, hs4_mod⟩
  | none =>
    rw [hev_eq] at hs2_res
    have hnot_surv :
        θ_mem ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) := by
      rw [mem_survivingSeeds, pureReplay_append_singleton, hreplay]
      simp [hev_eq]
    simp only [hnot_surv, ↓reduceIte]
    have hs4_bdd : s4.Bounded w :=
      (prepHeaderFlag_exec hs2_0 (by decide) hfit_end).bounded (he_pref.bounded hx_bdd)
    obtain ⟨μ_reh, hE', hreh_dist, hreh_law, hreh_supp⟩ :=
      rehashLoopCode_execCodeDist hreh
        ⟨hs4_bdd, hs4_0, hs2_hdr, hs2_hash.1, hs4_kv, hs4_mod⟩
        hs2_res hfit_ev hw hfit_end hfit_q
    let μ_out := μ_reh.map (fun z => z.set 2 0)
    have hreh_tail : ExecCodeDist w (.seq (rehashLoopCode c_exp n_max) (.op (.const 2 0))) s4 μ_out
        ((rehashLoopSteps c_exp n_max U : ℝ≥0∞) + (1 : ℕ)) :=
      (hreh_dist.seq_const (fun z _ => ExecCodeDist.of_exec (Exec.const (d := 2) hfit_0))
        (fun _ _ => le_rfl)).congr_dist rfl le_rfl
    have hbr := branchHeaderPosCode_execCodeDist_pos (zeroCode := .op (.const 2 0))
      hs2_0 (by decide) (by omega) hfit_end hreh_tail
    have ht_ev_max := ht_ev.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _
      (evictRounds_le (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl
        ⟨u, ks.length⟩)) 10)
    have hdist : ExecCodeDist w (insertNewKeyBranchCode c_exp n_max) x μ_out
        (maxEvictions n_max * evictIterSteps c_exp n_max U + 54 +
          rehashLoopSteps c_exp n_max U + 2 : ℕ) :=
      ((ExecCodeDist.of_exec he_setup).seq_pure
        ((ExecCodeDist.of_exec he_ev).seq_pure hbr)).mono (by norm_cast; omega)
    refine ⟨μ_out, hE', hdist, by dsimp only [μ_out]; rw [PMF.map_comp]; exact hreh_law,
      fun y hy => ?_⟩
    have hy_bdd := hdist.bounded hx_bdd y hy
    dsimp only [μ_out] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨⟨_, hz_0, hz_hdr, _, hz_kv, hz_mod⟩, hz_hash, tbl', hz_rep, hz_slots⟩ := hreh_supp z hz
    exact ⟨by wram_simp, ⟨hy_bdd, by wram_simp [hz_0], hz_hdr, hz_hash, hz_kv, tbl', hz_rep,
      hz_slots⟩, hz_mod⟩

/-- Distributional execution specification for `insertCode` maintaining `RepWithKeys` and exact
conditional-uniform surviving-seed transition. -/
theorem insertCode_execCodeDist {w base c_exp n_max U V v : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    {u : Fin U} {x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hrep : RepWithKeys w base c_exp n_max U V ks s x)
    (h3 : x.regs 3 = u.val)
    (h4 : x.regs 4 = v)
    (hpre : ((Dictionary.dom s).card < n_max ∨ (s u).isSome) ∧ v < V)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem
    ∃ (μ_ins : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
        (stepKeys ks (.insert u v))).Nonempty),
      ExecCodeDist w (insertCode c_exp n_max) x μ_ins
        (insertSeedSteps c_exp n_max U ks θ_mem s u) ∧
      μ_ins.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
            (stepKeys ks (.insert u v)) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
              (stepKeys ks (.insert u v))) hE') ∧
      ∀ y ∈ μ_ins.support,
        y.regs 2 = 0 ∧
        RepWithKeys w base c_exp n_max U V (stepKeys ks (.insert u v))
          (Function.update s u (some v)) y ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  classical
  intro θ_mem
  have hθ_surv : θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks :=
    hrep.extractSeed_mem_survivingSeeds
  obtain ⟨hx_bdd, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ :=
    unpackRepWithKeys (θ := θ_mem) hrep rfl
  have hle_sp := le_space c_exp n_max
  have hle_hp := le_hashPairSpace c_exp n_max
  have hts : tableSize n_max = 2 ^ tableBits n_max := rfl
  have hlen_le : ks.length ≤ n_max := hkv.2.1
  have e_st11 := storeHeaderCode_exec (w := w) (off := 11) (src := 3) (x := x)
    h0 (by decide) (by decide) (by fits) (by fits)
  set s1 := (((x.set 15 11).set 16 (base + 11)).write (base + 11) (x.regs 3))
  have e_st18 := storeHeaderCode_exec (w := w) (base := base) (off := 18) (src := 4) (x := s1)
    (by regs_frame) (by decide) (by decide) (by fits) (by fits)
  set s2 := (((s1.set 15 18).set 16 (base + 18)).write (base + 18) (s1.regs 4))
  have hs2_11 : s2.mem (base + 11) = u.val := by wram_simp [s2, s1, h3]
  have hs2_18 : s2.mem (base + 18) = v := by wram_simp [s2, s1, h4]
  obtain ⟨s3, ⟨t_probe, ht_probe, he_probe⟩, hs3_0, hs3_lookup, hs3_frame⟩ :=
    probeKeyCode_execWithin (x := s2) (ks := ks) (tbl := tbl) (u := u)
      (by struct_frame hhdr) (hhash.congr_of_ge_hashBase (by mem_frame))
      (by struct_frame hslots) (pureReplay_tableIdxValid hkv.1 hreplay) hlen_le
      (fun idx hlt => by have := (hkv.2.2.2.2.1 idx hlt).1; mem_frame)
      (by regs_frame) hs2_11 hw hfit_end
  have he_pref : Exec w (.seq (storeHeaderCode 11 3)
      (.seq (storeHeaderCode 18 4) (probeKeyCode c_exp n_max))) x s3 (3 + (3 + t_probe)) :=
    e_st11.seq (e_st18.seq he_probe)
  set s5 := prepHeaderFlagData base 13 s3
  have hs5_mem : s5.mem = s3.mem := rfl
  have hs5_0 : s5.regs 0 = base := by simp +decide [s5, prepHeaderFlagData, hs3_0]
  have hs5_bdd : s5.Bounded w :=
    (prepHeaderFlag_exec hs3_0 (by decide) hfit_end).bounded (he_pref.bounded hx_bdd)
  have hs3_seed_x : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) s3.mem = θ_mem :=
    extractSeed_congr_of_ge_hashBase (by mem_frame)
  have hs3_hdr : HeaderConstsRep base c_exp n_max U s3.mem := by struct_frame hhdr
  have hs3_slots :
      TableSlotsRep (t1Base base c_exp n_max) (t2Base base c_exp n_max) tbl s3.mem := by
    struct_frame hslots
  have hs3_kv : KeysValsRep base c_exp n_max U V ks s s3.mem := by struct_frame hkv
  have hs3_11 : s3.mem (base + 11) = u.val := by mem_frame
  have hs3_18 : s3.mem (base + 18) = v := by mem_frame
  have hs5_mod : Modifies (Block.mk base (space c_exp n_max)).footprint x.mem s5.mem := by
    rw [hs5_mem]; mem_frame
  have hs5_rep : RepWithKeys w base c_exp n_max U V ks s s5 :=
    ⟨hs5_bdd, hs5_0, hs3_hdr, hs3_seed_x ▸ hhash.congr_of_ge_hashBase (by mem_frame),
      hs3_kv, tbl, hs3_seed_x ▸ hreplay, hs3_slots⟩
  by_cases hu : u ∈ Dictionary.dom s
  · have hu_ks : u ∈ ks := (hkv.2.2.2.1 u).mpr hu
    obtain ⟨idx, hidx_lt, hks_idx⟩ := List.mem_iff_getElem.mp hu_ks
    have hlook := pureReplay_lookupEntry_of_mem hkv.1 hreplay hidx_lt
    rw [hks_idx] at hlook
    rw [hlook] at hs3_lookup
    obtain ⟨hs3_13, hs3_14⟩ := hs3_lookup
    dsimp only at hs3_14
    obtain ⟨y, he_ov, hy_0, hy_2, hy_val, hy_frame⟩ :=
      insertOverwriteBranchCode_exec (c_exp := c_exp) (n_max := n_max)
        hs5_0 hs3_hdr.2.2.2.2.2.2.2.2.2 hs3_14 hs3_18 (by omega) hfit_end
    have hy_seed : extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem = θ_mem :=
      (extractSeed_congr_of_footprint (by mem_frame)).trans hs3_seed_x
    have hy_mod : Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
      mem_frame
    have hstep_eq : stepKeys ks (.insert u v) = ks := by simp [stepKeys, hu_ks]
    rw [hstep_eq]
    have hbr := branchHeaderPosCode_execCodeDist_pos
      (zeroCode := insertNewKeyBranchCode c_exp n_max)
      hs3_0 (by decide) (by omega) hfit_end (ExecCodeDist.of_exec he_ov)
    have hdist : ExecCodeDist w (insertCode c_exp n_max) x (PMF.pure y)
        (insertBaseSteps c_exp n_max U : ℕ) :=
      ((ExecCodeDist.of_exec e_st11).seq_pure
        ((ExecCodeDist.of_exec e_st18).seq_pure
          ((ExecCodeDist.of_exec he_probe).seq_pure hbr))).mono
        (by dsimp only [insertBaseSteps]; norm_cast; omega)
    refine ⟨PMF.pure y, ⟨θ_mem, hθ_surv⟩, hdist.mono (by dsimp only [insertSeedSteps]; simp [hu]),
      ?_, ?_⟩
    · simp only [hθ_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply, hy_seed]
    · intro z hz
      have hy_bdd := hdist.bounded hx_bdd z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hy_2, ⟨hy_bdd, hy_0, by struct_frame hs3_hdr,
        hy_seed ▸ hhash.congr_of_footprint (by mem_frame),
        hs3_kv.insert_of_mem hpre.2 hidx_lt hks_idx (by mem_frame)
          (by mem_frame) hy_val (by mem_frame),
        tbl, hy_seed ▸ hreplay, by struct_frame hs3_slots⟩, hy_mod⟩
  · have hu_ks : u ∉ ks := fun h => hu ((hkv.2.2.2.1 u).mp h)
    have hstep_eq : stepKeys ks (.insert u v) = ks ++ [u] := by simp [stepKeys, hu_ks]
    have hnone_u : s u = none := Dictionary.notMem_dom_iff.mp hu
    have hlen_lt : ks.length < n_max := by
      rw [← hkv.card_dom_eq]
      exact hpre.1.resolve_right (by rw [hnone_u]; exact Bool.false_ne_true)
    have hlook := pureReplay_lookupEntry_of_notMem hkv.1 hreplay hu_ks
    rw [hlook] at hs3_lookup
    obtain ⟨μ_br, hE'_br, hbr_dist, hbr_law, hbr_supp⟩ :=
      insertNewKeyBranchCode_execCodeDist (x₀ := x) (x := s5) hreh hs5_rep hs3_11 hs3_18 hu_ks
        hlen_lt hpre.2 hs5_mod hfit_ev hw hfit_end hfit_q
    rw [hs5_mem, hs3_seed_x] at hbr_dist hbr_law
    rw [hstep_eq]
    have hbr := branchHeaderPosCode_execCodeDist_zero (posCode := insertOverwriteBranchCode)
      hs3_0 (by decide) hs3_lookup hfit_end hbr_dist
    have hdist : ExecCodeDist w (insertCode c_exp n_max) x μ_br
        (insertSeedSteps c_exp n_max U ks θ_mem s u) :=
      ((ExecCodeDist.of_exec e_st11).seq_pure
        ((ExecCodeDist.of_exec e_st18).seq_pure
          ((ExecCodeDist.of_exec he_probe).seq_pure hbr))).mono (by
        dsimp only [insertSeedSteps]
        simp only [hu, hθ_surv, not_true_eq_false, or_false, ↓reduceIte]
        split_ifs <;> (dsimp only [insertWorstSteps, insertBaseSteps]; norm_cast; omega))
    exact ⟨μ_br, hE'_br, hdist, hbr_law, hbr_supp⟩

end Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
