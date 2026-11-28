/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Instance
public import CslibFrontier.Computability.WordRAM.Structured
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Trie
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Sparse input-trie builder on the word RAM

Accumulates a list of sparse `(setMask S, Signed.encode v)` pairs from flat word memory into a
depth-`d` binary trie in `O((d + 1) · |es|)` instructions (`buildInputTrie`, `exec_buildInputTrie`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.buildInputTrie`: builds a depth-`d` binary trie summing
  sparse `(S, v)` entries at `Reg.entryPtr`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_buildInputTrie`: `ExecWithin` specification producing
  a `HoldsTrie` representing `Signed.encode ∘ evalEntries es`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

/-- Add `Signed.right` into key `rTrieKey` of depth-`Reg.dim` trie `rTrieRoot`. -/
private def trieAdd : Code .standard numRegs :=
  .seq trieGet
    (.seq (ram[ Signed.left ← rTrieVal ])
      (.seq (Signed.add (r := 47))
        (.seq (ram[ rTrieVal ← Signed.result ]) trieSet)))

private theorem trieAdd_preserves (i : Fin numRegs) :
    9 ≤ i.val ∧ i ≠ Reg.free ∧ (i.val < 18 ∨ 23 ≤ i.val) → trieAdd.Preserves i := by
  intro hi
  refine ⟨trieGet_preserves i hi.2.2, ?_, signedAdd_preserves i hi.1, ?_,
    trieSet_preserves i ⟨hi.2.1, ?_⟩⟩ <;> revert i hi <;> decide +kernel

private theorem exec_trieAdd {w lo d root key free B : ℕ} {delta : ℤ}
    {S : Set ℕ} {fnZ : ℕ → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hr : x.regs rTrieRoot = root) (hk : x.regs rTrieKey = key)
    (hdelta : x.regs (Signed.right (r := 47)) = Signed.encode delta)
    (hfree : x.regs Reg.free = free)
    (hlo : 1 ≤ lo) (hfree_lo : lo ≤ free) (hroot : 0 < root) (hS : S ⊆ Set.Ico lo free)
    (hrep : TrieRep x.mem d root S (fun m => Signed.encode (fnZ m)))
    (hkey_lt : key < 2 ^ d)
    (hfn_le : ∀ m, (fnZ m).natAbs ≤ B) (hdelta_le : delta.natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 * d)) (hfit_d : Fits w d) (hfit_key : Fits w key) :
    ∃ y, ExecWithin w trieAdd x y (23 * d + 31) ∧
      (∀ i : Fin numRegs, 9 ≤ i.val ∧ i ≠ Reg.free ∧ (i.val < 18 ∨ 23 ≤ i.val) →
        y.regs i = x.regs i) ∧ ∃ S' free',
      y.regs Reg.free = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * d ∧
      S' ⊆ Set.Ico lo free' ∧
      (∀ a, a < lo ∨ free' ≤ a → y.mem a = x.mem a) ∧
      TrieRep y.mem d root S'
        (fun m => Signed.encode (if m % 2 ^ d = key then fnZ key + delta else fnZ m)) := by
  have htrie_ro : HoldsTrie x.mem free d root (fun m => Signed.encode (fnZ m)) :=
    HoldsTrie.iff_exists_trieRep.mpr ⟨S, fun a ha => ⟨hlo.trans (hS ha).1, (hS ha).2⟩, hrep⟩
  refine WP.exists_execWithin_preserves trieAdd_preserves ?_
  unfold trieAdd
  wram_call (exec_trieGet x hz ho hd hr hk htrie_ro (hfit_free.of_le (by omega)) hfit_d hfit_key)
    with u₁ ⟨hu₁_val, hu₁_mem, hu₁_regs⟩
  wram_exec *
  wram_call (exec_signedAdd hfit_val (hfn_le key) hdelta_le _ (by wram_simp) (by regs_frame))
    with u₃ ⟨hu₃_res, hu₃_mem, hu₃_regs⟩
  wram_exec *
  obtain ⟨y, S', free', he₅, hyfree, hle1, hle2, hS', hyframe, hyrep, -⟩ :=
    exec_trieSet (free := free) (val := Signed.encode (fnZ key + delta))
      (u₃.set rTrieVal (Signed.encode (fnZ key + delta)))
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by wram_simp) (by regs_frame) hlo hfree_lo hroot hS
      (by simpa only [Data.set_mem, hu₃_mem, hu₁_mem] using hrep) hkey_lt hfit_free hfit_d hfit_key
  wram_call he₅
  refine ⟨by omega, fun hf => ⟨hf, S', free', hyfree, hle1, hle2, hS', fun a ha => ?_,
    by simpa only [apply_ite Signed.encode] using hyrep⟩⟩
  simp only [hyframe a ha, Data.set_mem, hu₃_mem, hu₁_mem]

private def buildInputLoadCode : Code .standard numRegs := ram[
  rGenTmp ← rCellIdx + rCellIdx;
  rGenTmp ← Reg.entryPtr + rGenTmp;
  rTrieKey ← *rGenTmp;
  rGenTmp ← rGenTmp + rOne;
  Signed.right ← *rGenTmp;
  rTrieRoot ← Reg.builtRoot ]

private def buildInputStep : Code .standard numRegs :=
  .seq buildInputLoadCode
    (.seq trieAdd
      (ram[ rCellIdx ← rCellIdx + rOne ]))

/-- Build a depth-`d` binary trie accumulating the sparse `(S, v)` pairs stored as `2 * |es|` words
`[setMask S₀, Signed.encode v₀, …]` starting at `Reg.entryPtr`, writing the allocated root to
`Reg.builtRoot` and advancing `Reg.free`. -/
def buildInputTrie : Code .standard numRegs :=
  .seq (ram[ rZero ← #0; rOne ← #1 ])
    (.seq trieInit
      (.seq (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ])
        (.loop (.lt rCellIdx Reg.entryCount) buildInputStep)))

private theorem buildInputTrie_preserves (i : Fin numRegs) :
    ((11 ≤ i.val ∧ i.val ≤ 15 ∧ i ≠ Reg.free) ∨
      (44 ≤ i.val ∧ i.val ≤ 55) ∨ i = Reg.entryPtr ∨ i = Reg.entryCount) →
      buildInputTrie.Preserves i := by
  intro hi
  refine ⟨?_, trieInit_preserves i ?_, ?_, ?_, trieAdd_preserves i ?_, ?_⟩ <;>
    revert i hi <;> decide +kernel

/-- Build a depth-`d` `HoldsTrie` from `es.length` sparse `(S, v)` pairs in memory within
`es.length * (23 * d + 40) + 11` standard-basis instructions, preserving caller registers and all
memory outside `Ico free free'`. -/
theorem exec_buildInputTrie {w d entryPtr free W : ℕ}
    (es : List (Finset (Fin d) × ℤ)) (x : Data numRegs)
    (hd : x.regs Reg.dim = d)
    (hep : x.regs Reg.entryPtr = entryPtr) (hel : x.regs Reg.entryCount = es.length)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (he_below : entryPtr + 2 * es.length ≤ free)
    (he_mem : ∀ p (hp : p < es.length),
      x.mem (entryPtr + 2 * p) = setMask es[p].1 ∧
      x.mem (entryPtr + 2 * p + 1) = Signed.encode es[p].2)
    (hes_W : entryAbsSum es ≤ W)
    (hfit_val : Fits w (valueEnvelope d W))
    (hfit_free : Fits w (free + 2 + 2 * d * es.length)) :
    ∃ y free' outFn,
      ExecWithin w buildInputTrie x y (es.length * (23 * d + 40) + 11) ∧
      y.regs Reg.builtRoot = free ∧ y.regs Reg.free = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * es.length ∧
      HoldsTrie y.mem free' d free outFn ∧
      (∀ S : Finset (Fin d), outFn (setMask S) = Signed.encode (evalEntries es S)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs,
        ((11 ≤ i.val ∧ i.val ≤ 15 ∧ i ≠ Reg.free) ∨
          (44 ≤ i.val ∧ i.val ≤ 55) ∨ i = Reg.entryPtr ∨ i = Reg.entryCount) →
          y.regs i = x.regs i := by
  let B := 8 ^ d * (W + 1) ^ 2
  have hfit_B : Fits w (8 * B + 4) := hfit_val
  have hfit_1 : Fits w 1 := hfit_B.of_le (by omega)
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  have hW_le_B : W ≤ B :=
    (show W ≤ (W + 1) ^ 2 by rw [sq]; nlinarith).trans (Nat.le_mul_of_pos_left _ (by positivity))
  let x₀ := (x.set rZero 0).set rOne 1
  have hinit_zo : ExecWithin (B := .standard) w (ram[ rZero ← #0; rOne ← #1 ]) x x₀ 2 := by
    wram_exec
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x₀ (by regs_frame) (by regs_frame) (by regs_frame) (by omega)
      (hfit_free.of_le (by omega))
  let s₁ := (s₀.set Reg.builtRoot free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w
      (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ]) s₀ s₁ 2 := by
    wram_exec [hs₀_root]
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    (s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧
      s.regs Reg.entryPtr = entryPtr ∧ s.regs Reg.entryCount = es.length ∧
      s.regs Reg.builtRoot = free) ∧
    ∃ (curFree : ℕ) (S : Set ℕ) (fnZ : ℕ → ℤ), s.regs Reg.free = curFree ∧
      free + 2 ≤ curFree ∧ curFree ≤ free + 2 + 2 * d * p ∧
      S ⊆ Set.Ico free curFree ∧
      TrieRep s.mem d free S (fun m => Signed.encode (fnZ m)) ∧
      (∀ m, (fnZ m).natAbs ≤ entryAbsSum (es.take p)) ∧
      (∀ X : Finset (Fin d), fnZ (setMask X) = evalEntries (es.take p) X) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rCellIdx) s) (hp : s.regs rCellIdx < es.length) :
      ∃ z, ExecWithin w buildInputStep s z (23 * d + 38) ∧
        P (s.regs rCellIdx + 1) z ∧ z.regs rCellIdx = s.regs rCellIdx + 1 := by
    generalize hp_eq : s.regs rCellIdx = p at hs hp ⊢
    obtain ⟨⟨hsz, hso, hsd, hsep, hsel, hssav⟩, curFree, S, fnZ, hsfr, hcf_lo, hcf_hi,
      hS_sub, hsrep, hfnZ_abs, hfnZ_eq, hsframe⟩ := hs
    obtain ⟨hmk, hv⟩ := he_mem p hp
    rw [two_mul] at hmk hv
    have hrmk := (hsframe _ (Or.inl (by omega))).trans hmk
    have hrv := (hsframe _ (Or.inl (by omega))).trans hv
    have hfit_p : Fits w (entryPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hcf_fit : Fits w (curFree + 2 * d) := hfit_free.of_le (by
      have := Nat.mul_le_mul_left (2 * d) (show p + 1 ≤ es.length from hp)
      rw [mul_add] at this; omega)
    have htake : es.take (p + 1) = es.take p ++ [es[p]] := List.take_succ_eq_append_getElem hp
    have htake_sum : entryAbsSum (es.take (p + 1)) = entryAbsSum (es.take p) + es[p].2.natAbs := by
      rw [htake]; simp only [entryAbsSum, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have htake_W : entryAbsSum (es.take (p + 1)) ≤ W :=
      (((List.take_sublist _ _).map _).sum_le_sum fun _ _ => Nat.zero_le _).trans hes_W
    wram_exec * [buildInputStep, buildInputLoadCode, hrmk, hrv]
    wram_call (exec_trieAdd (lo := free) (root := free) (key := setMask es[p].1)
      (delta := es[p].2) (free := curFree) (B := B) (fnZ := fnZ) _ (by regs_frame)
      (by regs_frame) (by regs_frame) (by wram_simp) (by wram_simp) (by wram_simp)
      (by regs_frame) hfree_pos (by omega) (by omega) hS_sub hsrep (setMask_lt _)
      (fun m => (hfnZ_abs m).trans (by omega)) (by omega) hfit_B hcf_fit hfit_d
      (hfit_mask.of_le (setMask_lt _).le))
      with u₁ ⟨hu₁_regs, S', free', hu₁_fr, hcf_le', hfree'_le, hS'_sub, hu₁_frame, hu₁_rep⟩
    wram_exec *
    refine ⟨⟨by regs_frame, free', S', _, by regs_frame, by omega, by rw [mul_add]; omega,
      hS'_sub, hu₁_rep, fun m => ?_, fun X => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · rw [htake_sum]
      split_ifs
      · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right (hfnZ_abs _) _)
      · exact (hfnZ_abs m).trans (Nat.le_add_right _ _)
    · rw [Nat.mod_eq_of_lt (setMask_lt X), htake]
      simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil,
        setMask_injective.eq_iff]
      rw [← evalEntries]
      by_cases hX : X = es[p].1
      · subst hX; simp [hfnZ_eq]
      · simp [hX, hfnZ_eq]
    · exact (hu₁_frame a ha).trans (hsframe a (by omega))
  have hs₁P : P (s₁.regs rCellIdx) s₁ :=
    ⟨by regs_frame, free + 2, _, fun _ => 0, by regs_frame, le_rfl, by simp [s₁],
      by simp [Set.insert_subset_iff], hs₀_rep, fun _ => Nat.zero_le _, by simp [s₁, evalEntries],
      fun a ha => hs₀_frame a ⟨by omega, by omega⟩⟩
  obtain ⟨y, hloop, ⟨⟨-, -, -, -, -, hysav⟩, free', S', fnZ, hyfr, hlo', hhi', hS', hyrep, -,
      hfnZ_eq, hyframe⟩, -⟩ :=
    ExecWithin.loop_count P (fun _ ⟨⟨_, _, _, _, h, _⟩, _⟩ => h) hbody (by simp [s₁]) hs₁P
  rw [List.take_length] at hfnZ_eq
  have htot : ExecWithin w buildInputTrie x y (es.length * (23 * d + 40) + 11) :=
    (hinit_zo.seq (hinit0.seq (hinit1.seq hloop))).mono (by
      simp only [s₁, Data.set_regs_self, Nat.sub_zero]; ring_nf; omega)
  refine ⟨y, free', fun m => Signed.encode (fnZ m), htot, hysav, hyfr, hlo', hhi',
    HoldsTrie.iff_exists_trieRep.mpr
      ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩,
    fun S => congrArg _ (hfnZ_eq S), hyframe,
    fun i hi => htot.regs_eq (buildInputTrie_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
