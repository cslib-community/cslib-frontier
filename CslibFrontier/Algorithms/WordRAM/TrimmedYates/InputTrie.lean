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
import CslibFrontier.Computability.WordRAM.SymbolicExec

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
  exact ⟨trieGet_preserves i hi.2.2,
    by revert i hi; decide +kernel,
    signedAdd_preserves i hi.1,
    by revert i hi; decide +kernel,
    trieSet_preserves i ⟨hi.2.1, by revert i hi; decide +kernel⟩⟩

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
    ∃ y S' free', ExecWithin w trieAdd x y (23 * d + 31) ∧
      y.regs Reg.free = free' ∧ free ≤ free' ∧ free' ≤ free + 2 * d ∧
      S' ⊆ Set.Ico lo free' ∧
      (∀ a, a < lo ∨ free' ≤ a → y.mem a = x.mem a) ∧
      TrieRep y.mem d root S'
        (fun m => Signed.encode (if m % 2 ^ d = key then fnZ key + delta else fnZ m)) ∧
      ∀ i : Fin numRegs, 9 ≤ i.val ∧ i ≠ Reg.free ∧ (i.val < 18 ∨ 23 ≤ i.val) →
        y.regs i = x.regs i := by
  have htrie_ro : HoldsTrie x.mem free d root (fun m => Signed.encode (fnZ m)) :=
    HoldsTrie.iff_exists_trieRep.mpr ⟨S, fun a ha => ⟨hlo.trans (hS ha).1, (hS ha).2⟩, hrep⟩
  obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ := exec_trieGet x hz ho hd hr hk htrie_ro
    (hfit_free.of_le (by omega)) hfit_d hfit_key
  let u₂ := u₁.set (Signed.left (r := 47)) (Signed.encode (fnZ key))
  have he₂ : ExecWithin (B := .standard) w (ram[ Signed.left ← rTrieVal ]) u₁ u₂ 1 := by
    wram_exec [hu₁_val]
  have hu₂_right : u₂.regs (Signed.right (r := 47)) = Signed.encode delta := by
    simp only [u₂, Data.set_regs_of_ne (by decide : Signed.right (r := 47) ≠ Signed.left)]
    exact (hu₁_regs _ (Or.inl (by decide))).trans hdelta
  obtain ⟨u₃, he₃, hu₃_res, hu₃_mem, hu₃_regs⟩ := exec_signedAdd hfit_val (hfn_le key) hdelta_le u₂
    (by simp [u₂]) hu₂_right
  let u₄ := u₃.set rTrieVal (Signed.encode (fnZ key + delta))
  have he₄ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₃ u₄ 1 := by
    wram_exec [hu₃_res]
  have hu₄_mem : u₄.mem = x.mem := hu₃_mem.trans hu₁_mem
  have reg_u₄ (i : Fin numRegs) (hi9 : 9 ≤ i.val) (hi18 : i.val < 18 ∨ 23 ≤ i.val) :
      u₄.regs i = x.regs i := by
    have hne_val : i ≠ rTrieVal := by intro h; subst h; simp at hi18
    have hne_left : i ≠ Signed.left (r := 47) := by intro h; subst h; simp at hi9
    simp only [u₄, Data.set_regs_of_ne hne_val]
    rw [hu₃_regs i hi9]
    simp only [u₂, Data.set_regs_of_ne hne_left]
    exact hu₁_regs i hi18
  obtain ⟨y, S', free', he₅, hyfree, hle1, hle2, hS', hyframe, hyrep, _⟩ :=
    exec_trieSet (val := Signed.encode (fnZ key + delta)) (free := free) u₄
      (reg_u₄ rZero (by decide) (Or.inl (by decide)) |>.trans hz)
      (reg_u₄ rOne (by decide) (Or.inl (by decide)) |>.trans ho)
      (reg_u₄ Reg.dim (by decide) (Or.inl (by decide)) |>.trans hd)
      (reg_u₄ rTrieRoot (by decide) (Or.inl (by decide)) |>.trans hr)
      (reg_u₄ rTrieKey (by decide) (Or.inl (by decide)) |>.trans hk)
      (by simp [u₄])
      (reg_u₄ Reg.free (by decide) (Or.inl (by decide)) |>.trans hfree)
      hlo hfree_lo hroot hS (by rwa [hu₄_mem]) hkey_lt hfit_free hfit_d hfit_key
  have htot : ExecWithin w trieAdd x y (23 * d + 31) :=
    (he₁.seq (he₂.seq (he₃.seq (he₄.seq he₅)))).mono (by omega)
  refine ⟨y, S', free', htot, hyfree, hle1, hle2, hS',
    fun a ha => (hyframe a ha).trans (congrFun hu₄_mem a), ?_,
    fun i hi => htot.regs_eq (trieAdd_preserves i hi)⟩
  convert hyrep using 1
  funext m
  split_ifs <;> rfl

private def buildInputLoadCode : Code .standard numRegs := ram[
  rGenTmp ← rCellIdx + rCellIdx;
  rGenTmp ← Reg.entryPtr + rGenTmp;
  rTrieKey ← *rGenTmp;
  rGenTmp ← rGenTmp + rOne;
  Signed.right ← *rGenTmp;
  rTrieRoot ← Reg.builtRoot ]

private theorem buildInputLoadCode_preserves (i : Fin numRegs) :
    i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot →
      buildInputLoadCode.Preserves i := by
  decide +kernel +revert

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
  exact ⟨by revert i hi; decide +kernel,
    trieInit_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel,
    buildInputLoadCode_preserves i (by revert i hi; decide +kernel),
    trieAdd_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel⟩

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
  have hW_le_B : W ≤ B := by
    dsimp only [B]
    have h1 : 1 ≤ 8 ^ d := Nat.one_le_pow _ _ (by decide)
    have hW : W ≤ (W + 1) ^ 2 := by rw [sq]; nlinarith
    exact hW.trans (Nat.le_mul_of_pos_left _ h1)
  let x₀ := (x.set rZero 0).set rOne 1
  have hinit_zo : ExecWithin (B := .standard) w (ram[ rZero ← #0; rOne ← #1 ]) x x₀ 2 := by
    wram_exec
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x₀ (by simp [x₀]) (by simp [x₀]) (by simpa [x₀] using hfree)
      (by omega) (hfit_free.of_le (by omega))
  let s₁ := (s₀.set Reg.builtRoot free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w
      (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ]) s₀ s₁ 2 := by
    wram_exec [hs₀_root]
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧
    s.regs Reg.entryPtr = entryPtr ∧ s.regs Reg.entryCount = es.length ∧
    s.regs Reg.builtRoot = free ∧
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
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsep, hsel, hssav, curFree, S, fnZ, hsfr, hcf_lo, hcf_hi,
      hS_sub, hsrep, hfnZ_abs, hfnZ_eq, hsframe⟩ := hs
    obtain ⟨hmk_p, hv_p⟩ := he_mem p hp
    have hrmk : s.mem (entryPtr + (p + p)) = setMask es[p].1 := by
      have : entryPtr + (p + p) = entryPtr + 2 * p := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hmk_p
    have hrv : s.mem (entryPtr + (p + p) + 1) = Signed.encode es[p].2 := by
      have : entryPtr + (p + p) + 1 = entryPtr + 2 * p + 1 := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hv_p
    have hf_2p : Fits w (p + p) := hfit_free.of_le (by omega)
    have hf_ep2p : Fits w (entryPtr + (p + p)) := hfit_free.of_le (by omega)
    have hf_ep2p1 : Fits w (entryPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hst : ∃ u₀, ExecWithin w buildInputLoadCode s u₀ 6 ∧
        u₀.regs rTrieKey = setMask es[p].1 ∧
        u₀.regs (Signed.right (r := 47)) = Signed.encode es[p].2 ∧
        u₀.regs rTrieRoot = free ∧ u₀.mem = s.mem := by
      unfold buildInputLoadCode
      wram_exec [hso, hsep, hp_eq, hssav, hrmk, hrv]
      wram_simp [hrmk, hrv]
    obtain ⟨u₀, he_ld, hu₀_key, hu₀_right, hu₀_root, hu₀_mem⟩ := hst
    have hu₀_regs : ∀ i,
        i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot →
          u₀.regs i = s.regs i :=
      fun i hi => he_ld.regs_eq (buildInputLoadCode_preserves i hi)
    have htake_sum : entryAbsSum (es.take p) + es[p].2.natAbs = entryAbsSum (es.take (p + 1)) := by
      rw [List.take_succ_eq_append_getElem hp]
      simp only [entryAbsSum, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    have htake1_le_W : entryAbsSum (es.take (p + 1)) ≤ W := by
      refine le_trans ?_ hes_W
      dsimp only [entryAbsSum]
      conv_rhs => rw [← List.take_append_drop (p + 1) es]
      rw [List.map_append, List.sum_append]
      exact Nat.le_add_right _ _
    have hcf_fit : Fits w (curFree + 2 * d) := by
      have : curFree + 2 * d ≤ free + 2 + 2 * d * es.length := by
        calc curFree + 2 * d ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
          _ = free + 2 + 2 * d * (p + 1) := by ring
          _ ≤ free + 2 + 2 * d * es.length :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (2 * d) (by omega)) _
      exact hfit_free.of_le this
    obtain ⟨u₁, S', free', he_add, hu₁_fr, hcf_le', hfree'_le, hS'_sub, hu₁_frame,
      hu₁_rep, hu₁_regs⟩ :=
      exec_trieAdd (root := free) (key := setMask es[p].1) (delta := es[p].2)
        (free := curFree) (B := B) (fnZ := fnZ) (lo := free) u₀
        ((hu₀_regs rZero (by decide)).trans hsz)
        ((hu₀_regs rOne (by decide)).trans hso)
        ((hu₀_regs Reg.dim (by decide)).trans hsd)
        hu₀_root hu₀_key hu₀_right
        ((hu₀_regs Reg.free (by decide)).trans hsfr)
        hfree_pos (by omega) (by omega) hS_sub (by rwa [hu₀_mem])
        (setMask_lt _)
        (fun m => (hfnZ_abs m).trans (by omega))
        (by omega)
        hfit_B hcf_fit hfit_d (hfit_mask.of_le (setMask_lt _).le)
    have hu₁_idx : u₁.regs rCellIdx = p :=
      (hu₁_regs rCellIdx ⟨by decide, by decide, Or.inr (by decide)⟩).trans
        ((hu₀_regs rCellIdx (by decide)).trans hp_eq)
    have hu₁_o : u₁.regs rOne = 1 :=
      (hu₁_regs rOne ⟨by decide, by decide, Or.inl (by decide)⟩).trans
        ((hu₀_regs rOne (by decide)).trans hso)
    have hf_p1 : Fits w (p + 1) := hfit_free.of_le (by omega)
    let z := u₁.set rCellIdx (p + 1)
    have he_inc : ExecWithin (B := .standard) w (ram[ rCellIdx ← rCellIdx + rOne ]) u₁ z 1 := by
      wram_exec [hu₁_idx, hu₁_o]
    have hstep_tot : ExecWithin w buildInputStep s z (23 * d + 38) :=
      (he_ld.seq (he_add.seq he_inc)).mono (by omega)
    have kz (i : Fin numRegs) (hi_ne : i ≠ rCellIdx)
        (ha : 9 ≤ i.val ∧ i ≠ Reg.free ∧ (i.val < 18 ∨ 23 ≤ i.val))
        (hl : i ≠ rGenTmp ∧ i ≠ rTrieKey ∧ i ≠ Signed.right (r := 47) ∧ i ≠ rTrieRoot) :
        z.regs i = s.regs i := by
      simp only [z, Data.set_regs_of_ne hi_ne]
      exact (hu₁_regs i ha).trans (hu₀_regs i hl)
    refine ⟨z, hstep_tot, ?_, by simp [z]⟩
    dsimp only [P]
    refine ⟨(kz rZero (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hsz,
      (kz rOne (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hso,
      (kz Reg.dim (by decide) ⟨by decide, by decide, Or.inl (by decide)⟩ (by decide)).trans hsd,
      (kz Reg.entryPtr (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans
        hsep,
      (kz Reg.entryCount (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans
        hsel,
      (kz Reg.builtRoot (by decide) ⟨by decide, by decide, Or.inr (by decide)⟩ (by decide)).trans
        hssav,
      free', S', fun m => if m % 2 ^ d = setMask es[p].1 then fnZ (setMask es[p].1) + es[p].2
        else fnZ m,
      by simp [z, hu₁_fr], by omega, ?_, hS'_sub, hu₁_rep, ?_, ?_, ?_⟩
    · calc free' ≤ curFree + 2 * d := hfree'_le
        _ ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
        _ = free + 2 + 2 * d * (p + 1) := by ring
    · intro m
      dsimp only
      rw [← htake_sum]
      split_ifs
      · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right (hfnZ_abs _) _)
      · exact (hfnZ_abs m).trans (Nat.le_add_right _ _)
    · intro X
      dsimp only
      rw [Nat.mod_eq_of_lt (setMask_lt X), List.take_succ_eq_append_getElem hp]
      simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil,
        setMask_injective.eq_iff]
      rw [← evalEntries]
      by_cases hX : X = es[p].1
      · subst hX; simp [hfnZ_eq]
      · simp [hX, hfnZ_eq]
    · intro a ha
      rcases ha with ha_lo | ha_hi
      · exact (hu₁_frame a (Or.inl ha_lo)).trans
          ((congrFun hu₀_mem a).trans (hsframe a (Or.inl ha_lo)))
      · exact (hu₁_frame a (Or.inr ha_hi)).trans
          ((congrFun hu₀_mem a).trans (hsframe a (Or.inr (by omega))))
  have hs₁P : P (s₁.regs rCellIdx) s₁ := by
    dsimp only [P]
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, List.take_zero]
    refine ⟨by simpa [s₁, x₀] using hs₀_regs rZero (by decide),
      by simpa [s₁, x₀] using hs₀_regs rOne (by decide),
      by simpa [s₁, x₀] using (hs₀_regs Reg.dim (by decide)).trans (by simpa [x₀] using hd),
      by simpa [s₁, x₀] using (hs₀_regs Reg.entryPtr (by decide)).trans (by simpa [x₀] using hep),
      by simpa [s₁, x₀] using (hs₀_regs Reg.entryCount (by decide)).trans (by simpa [x₀] using hel),
      by simp [s₁],
      free + 2, {free, free + 1}, fun _ => 0,
      by simp [s₁, hs₀_free], le_rfl, by omega, ?_, hs₀_rep, by simp [entryAbsSum],
      by simp [evalEntries], fun a ha => hs₀_frame a ⟨by omega, by omega⟩⟩
    intro a ha
    rcases ha with rfl | ha1
    · exact ⟨le_rfl, by omega⟩
    · have : a = free + 1 := by simpa using ha1
      subst this; exact ⟨by omega, by omega⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by simp [s₁]) hs₁P
  obtain ⟨_, _, _, _, _, hysav, free', S', fnZ, hyfr, hlo', hhi', hS', hyrep, _, hfnZ_eq,
    hyframe⟩ :=
    hyP
  rw [List.take_length] at hfnZ_eq
  have htot : ExecWithin w buildInputTrie x y (es.length * (23 * d + 40) + 11) := by
    refine (hinit_zo.seq (hinit0.seq (hinit1.seq hloop))).mono ?_
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, Nat.sub_zero]
    have h40 : 23 * d + 38 + 2 = 23 * d + 40 := by omega
    rw [h40]; omega
  refine ⟨y, free', fun m => Signed.encode (fnZ m), htot, hysav, hyfr, hlo', hhi',
    HoldsTrie.iff_exists_trieRep.mpr
      ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩,
    fun S => by dsimp only; rw [hfnZ_eq S], hyframe,
    fun i hi => htot.regs_eq (buildInputTrie_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
