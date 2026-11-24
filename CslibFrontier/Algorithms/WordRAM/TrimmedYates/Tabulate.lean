/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.TrieRep
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Trie
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Generic domain-to-trie tabulation and pointwise product on the word RAM

Allocates a fresh depth-`d` binary trie and evaluates either an arbitrary cell body (`tabulateDom`)
or pointwise signed multiplication (`tabulateMul`) over an interleaved `(mask, size)` domain array.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.IsCellMod`, `IsTabMod`: modified-register footprints for
  a cell body and the enclosing tabulation loop.
* `Cslib.Algorithms.WordRAM.TrimmedYates.tabulateDom`, `tabulateMul`: generic domain-tabulation loop
  and pointwise trie product over an active domain.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.tabulateDom_preserves`, `exec_tabulateDom`,
  `tabulateMul_preserves`, `exec_tabulateMul`: register frames and `ExecWithin` specifications.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

/-- Registers potentially modified by a single cell body inside `tabulateDom`. -/
abbrev IsCellMod (i : Fin numRegs) : Prop :=
  i.val < 9 ∨ (16 ≤ i.val ∧ i.val ≤ 22) ∨ i = rGenTmp

/-- Registers potentially modified by `tabulateDom`. -/
abbrev IsTabMod (i : Fin numRegs) : Prop :=
  IsCellMod i ∨ i = Reg.free ∨ i = rCellIdx ∨ i = Reg.builtRoot ∨ i = rCellKey ∨ i = rCellCard

private def tabulateDomStep (cellBody : Code .standard numRegs) : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rCellIdx + rCellIdx;
    rGenTmp ← Reg.entryPtr + rGenTmp;
    rCellKey ← *rGenTmp;
    rGenTmp ← rGenTmp + rOne;
    rCellCard ← *rGenTmp ])
  (.seq cellBody
    (.seq (ram[ rTrieRoot ← Reg.builtRoot; rTrieKey ← rCellKey ])
      (.seq trieSet
        (ram[ rCellIdx ← rCellIdx + rOne ]))))

/-- Allocate a fresh depth-`Reg.dim` trie and populate `cellBody` at each `(mask, size)` entry in
`Reg.entryPtr[0 .. Reg.entryCount - 1]`, leaving the root in `Reg.builtRoot`. -/
def tabulateDom (cellBody : Code .standard numRegs) : Code .standard numRegs :=
  .seq trieInit
    (.seq (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ])
      (.loop (.lt rCellIdx Reg.entryCount) (tabulateDomStep cellBody)))

theorem tabulateDom_preserves {cellBody : Code .standard numRegs} (i : Fin numRegs)
    (hcell : ¬ IsCellMod i → cellBody.Preserves i) (hi : ¬ IsTabMod i) :
    (tabulateDom cellBody).Preserves i :=
  ⟨trieInit_preserves i (by clear hcell; revert i hi; decide +kernel),
    by clear hcell; revert i hi; decide +kernel,
    by clear hcell; revert i hi; decide +kernel,
    hcell fun hc => hi (Or.inl hc),
    by clear hcell; revert i hi; decide +kernel,
    trieSet_preserves i (by clear hcell; revert i hi; decide +kernel),
    by clear hcell; revert i hi; decide +kernel⟩

theorem exec_tabulateDom {w d domPtr free T_cell : ℕ}
    {cellBody : Code .standard numRegs} {dom : List (Finset (Fin d))}
    {cellFn : Finset (Fin d) → ℕ} {Inv : Data numRegs → Prop} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hdp : x.regs Reg.entryPtr = domPtr) (hdl : x.regs Reg.entryCount = dom.length)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hInv_init : Inv x)
    (hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂)
    (hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs Reg.dim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w cellBody s u T_cell ∧ u.regs rTrieVal = cellFn dom[p] ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i)
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    ∃ y free' S' outFn,
      ExecWithin w (tabulateDom cellBody) x y (dom.length * (14 * d + T_cell + 16) + 9) ∧
      y.regs Reg.builtRoot = free ∧ y.regs Reg.free = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      S' ⊆ Set.Ico free free' ∧ TrieRep y.mem d free S' outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = cellFn X) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) := by
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x hz ho hfree (by omega) (hfit_free.of_le (by omega))
  let s₁ := (s₀.set Reg.builtRoot free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ])
      s₀ s₁ 2 := by wram_exec [hs₀_root]
  have hs₁_regs_tab : ∀ i, ¬ IsTabMod i → s₁.regs i = x.regs i := by
    intro i hi
    have hne_idx : i ≠ rCellIdx := fun h => hi (Or.inr (Or.inr (Or.inl h)))
    have hne_sav : i ≠ Reg.builtRoot := fun h => hi (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have hne_root : i ≠ rTrieRoot := fun h =>
      hi (Or.inl (Or.inr (Or.inl (by subst h; decide))))
    have hne_free : i ≠ Reg.free := fun h => hi (Or.inr (Or.inl h))
    simp only [s₁, Data.set_regs_of_ne hne_idx, Data.set_regs_of_ne hne_sav]
    exact hs₀_regs i ⟨hne_root, hne_free⟩
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧
    s.regs Reg.entryPtr = domPtr ∧ s.regs Reg.entryCount = dom.length ∧
    s.regs Reg.builtRoot = free ∧ Inv s ∧
    ∃ curFree S fn, s.regs Reg.free = curFree ∧
      free + 2 ≤ curFree ∧ curFree ≤ free + 2 + 2 * d * p ∧
      S ⊆ Set.Ico free curFree ∧ TrieRep s.mem d free S fn ∧
      (∀ q (hq : q < dom.length), q < p → fn (setMask dom[q]) = cellFn dom[q]) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rCellIdx) s) (hp : s.regs rCellIdx < dom.length) :
      ∃ z, ExecWithin w (tabulateDomStep cellBody) s z (14 * d + T_cell + 14) ∧
        P (s.regs rCellIdx + 1) z ∧ z.regs rCellIdx = s.regs rCellIdx + 1 := by
    generalize hp_eq : s.regs rCellIdx = p at hs hp ⊢
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsdp, hsdl, hssav, hsInv,
      curFree, S, fn, hsfree, hcf_lo, hcf_hi, hS_sub, hsrep, hdone, hsframe⟩ := hs
    obtain ⟨hmk_p, hsz_p⟩ := hdom p hp
    have hrmk : s.mem (domPtr + (p + p)) = setMask dom[p] := by
      have : domPtr + (p + p) = domPtr + 2 * p := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hmk_p
    have hrsz : s.mem (domPtr + (p + p) + 1) = #dom[p] := by
      have : domPtr + (p + p) + 1 = domPtr + 2 * p + 1 := by omega
      rw [this, hsframe _ (Or.inl (by omega))]; exact hsz_p
    have hf_2p : Fits w (p + p) := hfit_free.of_le (by omega)
    have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_free.of_le (by omega)
    have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hload : ∃ u₀, ExecWithin (B := .standard) w (ram[
        rGenTmp ← rCellIdx + rCellIdx;
        rGenTmp ← Reg.entryPtr + rGenTmp;
        rCellKey ← *rGenTmp;
        rGenTmp ← rGenTmp + rOne;
        rCellCard ← *rGenTmp ]) s u₀ 5 ∧
        u₀.regs rCellKey = setMask dom[p] ∧ u₀.regs rCellCard = #dom[p] ∧ u₀.mem = s.mem ∧
        ∀ i : Fin numRegs, i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard → u₀.regs i = s.regs i := by
      have hc_code : ∃ u₀, ExecWithin (B := .standard) w (ram[
          rGenTmp ← rCellIdx + rCellIdx;
          rGenTmp ← Reg.entryPtr + rGenTmp;
          rCellKey ← *rGenTmp;
          rGenTmp ← rGenTmp + rOne;
          rCellCard ← *rGenTmp ]) s u₀ 5 ∧
          u₀.regs rCellKey = setMask dom[p] ∧ u₀.regs rCellCard = #dom[p] ∧ u₀.mem = s.mem := by
        wram_exec [hso, hsdp, hp_eq, hrmk, hrsz]
        wram_simp [hrmk, hrsz]
      obtain ⟨u₀, he, hck, hcc, hm⟩ := hc_code
      refine ⟨u₀, he, hck, hcc, hm, fun i hi => he.regs_eq ?_⟩
      revert i hi; decide +kernel
    obtain ⟨u₀, he_load, hu₀_ck, hu₀_cc, hu₀_mem, hu₀_regs⟩ := hload
    have not_load_mod (i : Fin numRegs) (h : ¬ IsTabMod i) :
        i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard :=
      ⟨fun h1 => h (Or.inl (Or.inr (Or.inr h1))),
       fun h1 => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))),
       fun h1 => h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))⟩
    have hu₀_Inv : Inv u₀ := hInv_congr s u₀ (fun a _ => (congrFun hu₀_mem a).symm)
      (fun i hi => (hu₀_regs i (not_load_mod i hi)).symm) hsInv
    obtain ⟨u₁, he_cell, hu₁_val, hu₁_mem, hu₁_regs⟩ := hcell u₀ p hp
      ((hu₀_regs rZero (by decide)).trans hsz)
      ((hu₀_regs rOne (by decide)).trans hso)
      ((hu₀_regs Reg.dim (by decide)).trans hsd)
      hu₀_Inv (fun a ha => (congrFun hu₀_mem a).trans (hsframe a (Or.inl ha)))
      hu₀_ck hu₀_cc
    have keep_u₁ (i : Fin numRegs) (hc : ¬ IsCellMod i)
        (hl : i ≠ rGenTmp ∧ i ≠ rCellKey ∧ i ≠ rCellCard) : u₁.regs i = s.regs i :=
      (hu₁_regs i hc).trans (hu₀_regs i hl)
    have hu₁_sav : u₁.regs Reg.builtRoot = free :=
      (keep_u₁ Reg.builtRoot (by decide) (by decide)).trans hssav
    have hu₁_ck : u₁.regs rCellKey = setMask dom[p] :=
      (hu₁_regs rCellKey (by decide)).trans hu₀_ck
    let u₂ := (u₁.set rTrieRoot free).set rTrieKey (setMask dom[p])
    have he_prep : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← Reg.builtRoot; rTrieKey ← rCellKey ]) u₁ u₂ 2 := by
      wram_exec [hu₁_sav, hu₁_ck]
    have hu₂_mem : u₂.mem = s.mem := hu₁_mem.trans hu₀_mem
    have hcf_fit : Fits w (curFree + 2 * d) := by
      have : curFree + 2 * d ≤ free + 2 + 2 * d * dom.length := by
        calc curFree + 2 * d ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
          _ = free + 2 + 2 * d * (p + 1) := by ring
          _ ≤ free + 2 + 2 * d * dom.length :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (2 * d) (by omega)) _
      exact hfit_free.of_le this
    obtain ⟨u₃, S', free', he_set, hu₃_free, hcf_le', hfree'_le, hS'_sub, hu₃_frame,
      hu₃_rep, hu₃_regs⟩ :=
      exec_trieSet (root := free) (key := setMask dom[p]) (val := cellFn dom[p])
        (free := curFree) (lo := free) u₂
        (by simpa [u₂] using (keep_u₁ rZero (by decide) (by decide)).trans hsz)
        (by simpa [u₂] using (keep_u₁ rOne (by decide) (by decide)).trans hso)
        (by simpa [u₂] using (keep_u₁ Reg.dim (by decide) (by decide)).trans hsd)
        (by simp [u₂]) (by simp [u₂])
        (by simpa [u₂] using hu₁_val)
        (by simpa [u₂] using (keep_u₁ Reg.free (by decide) (by decide)).trans hsfree)
        hfree_pos (by omega) (by omega) hS_sub (by rwa [hu₂_mem])
        (setMask_lt _) hcf_fit hfit_d (hfit_mask.of_le (setMask_lt _).le)
    have hu₃_idx : u₃.regs rCellIdx = p := by
      rw [hu₃_regs rCellIdx ⟨by decide, Or.inr (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : rCellIdx ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : rCellIdx ≠ rTrieRoot)]
      exact (keep_u₁ rCellIdx (by decide) (by decide)).trans hp_eq
    have hu₃_one : u₃.regs rOne = 1 := by
      rw [hu₃_regs rOne ⟨by decide, Or.inl (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : rOne ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : rOne ≠ rTrieRoot)]
      exact (keep_u₁ rOne (by decide) (by decide)).trans hso
    have hf_p1 : Fits w (p + 1) := hfit_free.of_le (by omega)
    let z := u₃.set rCellIdx (p + 1)
    have he_inc : ExecWithin (B := .standard) w (ram[ rCellIdx ← rCellIdx + rOne ]) u₃ z 1 := by
      wram_exec [hu₃_idx, hu₃_one]
    have hstep_tot : ExecWithin w (tabulateDomStep cellBody) s z (14 * d + T_cell + 14) :=
      (he_load.seq (he_cell.seq (he_prep.seq (he_set.seq he_inc)))).mono (by omega)
    have hz_regs_tab : ∀ i, ¬ IsTabMod i → z.regs i = s.regs i := by
      intro i hi
      have hne_idx : i ≠ rCellIdx := fun h => hi (Or.inr (Or.inr (Or.inl h)))
      have hne_free : i ≠ Reg.free := fun h => hi (Or.inr (Or.inl h))
      have hnot_cell : ¬ IsCellMod i := fun h => hi (Or.inl h)
      have hrange : i.val < 19 ∨ 23 ≤ i.val := by
        by_contra hbad
        exact hnot_cell (Or.inr (Or.inl ⟨by omega, by omega⟩))
      have hne_key : i ≠ rTrieKey := fun h =>
        hnot_cell (Or.inr (Or.inl (by subst h; decide)))
      have hne_root : i ≠ rTrieRoot := fun h =>
        hnot_cell (Or.inr (Or.inl (by subst h; decide)))
      simp only [z, Data.set_regs_of_ne hne_idx]
      rw [hu₃_regs i ⟨hne_free, hrange⟩]
      simp only [u₂, Data.set_regs_of_ne hne_key, Data.set_regs_of_ne hne_root]
      exact keep_u₁ i hnot_cell (not_load_mod i hi)
    have hz_frame_below : ∀ a < free, z.mem a = s.mem a :=
      fun a ha => (hu₃_frame a (Or.inl ha)).trans (congrFun hu₂_mem a)
    have hz_sav : z.regs Reg.builtRoot = free := by
      simp only [z, Data.set_regs_of_ne (by decide : Reg.builtRoot ≠ rCellIdx)]
      rw [hu₃_regs Reg.builtRoot ⟨by decide, Or.inr (by decide)⟩]
      simp only [u₂, Data.set_regs_of_ne (by decide : Reg.builtRoot ≠ rTrieKey),
        Data.set_regs_of_ne (by decide : Reg.builtRoot ≠ rTrieRoot)]
      exact hu₁_sav
    refine ⟨z, hstep_tot, ?_, by simp [z]⟩
    dsimp only [P]
    refine ⟨(hz_regs_tab rZero (by decide)).trans hsz,
      (hz_regs_tab rOne (by decide)).trans hso,
      (hz_regs_tab Reg.dim (by decide)).trans hsd,
      (hz_regs_tab Reg.entryPtr (by decide)).trans hsdp,
      (hz_regs_tab Reg.entryCount (by decide)).trans hsdl,
      hz_sav,
      hInv_congr s z (fun a ha => (hz_frame_below a ha).symm)
        (fun i hi => (hz_regs_tab i hi).symm) hsInv,
      free', S', _, ?_, by omega, ?_, hS'_sub, hu₃_rep, ?_, ?_⟩
    · simp only [z, Data.set_regs_of_ne (by decide : Reg.free ≠ rCellIdx)]
      exact hu₃_free
    · calc free' ≤ curFree + 2 * d := hfree'_le
        _ ≤ free + 2 + 2 * d * p + 2 * d := Nat.add_le_add_right hcf_hi _
        _ = free + 2 + 2 * d * (p + 1) := by ring
    · intro q hq hqp1
      rw [Nat.mod_eq_of_lt (setMask_lt dom[q])]
      by_cases hqp : q = p
      · subst hqp; simp
      · have hne_dom : dom[q] ≠ dom[p] := fun h => hqp ((hnd.getElem_inj_iff).mp h)
        have hne_mk : setMask dom[q] ≠ setMask dom[p] := fun h => hne_dom (setMask_injective h)
        simp only [hne_mk, ↓reduceIte]
        exact hdone q hq (by omega)
    · intro a ha
      rcases ha with ha_lo | ha_hi
      · exact (hz_frame_below a ha_lo).trans (hsframe a (Or.inl ha_lo))
      · exact (hu₃_frame a (Or.inr ha_hi)).trans
          ((congrFun hu₂_mem a).trans (hsframe a (Or.inr (by omega))))
  have hs₁P : P (s₁.regs rCellIdx) s₁ := by
    dsimp only [P]
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx]
    refine ⟨(hs₁_regs_tab rZero (by decide)).trans hz,
      (hs₁_regs_tab rOne (by decide)).trans ho,
      (hs₁_regs_tab Reg.dim (by decide)).trans hd,
      (hs₁_regs_tab Reg.entryPtr (by decide)).trans hdp,
      (hs₁_regs_tab Reg.entryCount (by decide)).trans hdl,
      by simp [s₁],
      hInv_congr x s₁ (fun a ha => (hs₀_frame a ⟨by omega, by omega⟩).symm)
        (fun i hi => (hs₁_regs_tab i hi).symm) hInv_init,
      free + 2, {free, free + 1}, fun _ => 0, ?_, le_rfl, by omega, ?_, hs₀_rep,
      by simp, ?_⟩
    · simp only [s₁, Data.set_regs_of_ne (by decide : Reg.free ≠ rCellIdx),
        Data.set_regs_of_ne (by decide : Reg.free ≠ Reg.builtRoot)]
      exact hs₀_free
    · intro a ha
      rcases ha with rfl | ha1
      · exact ⟨le_rfl, by omega⟩
      · have : a = free + 1 := by simpa using ha1
        subst this; exact ⟨by omega, by omega⟩
    · intro a ha
      exact hs₀_frame a ⟨by omega, by omega⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by simp [s₁]) hs₁P
  obtain ⟨_, _, _, _, _, hysav, _, free', S', outFn, hyfree, hlo', hhi', hS', hyrep,
    hydone, hyframe⟩ := hyP
  have htot : ExecWithin w (tabulateDom cellBody) x y
      (dom.length * (14 * d + T_cell + 16) + 9) := by
    refine (hinit0.seq (hinit1.seq hloop)).mono ?_
    have hs₁_idx : s₁.regs rCellIdx = 0 := by simp [s₁]
    rw [hs₁_idx, Nat.sub_zero]
    have h16 : 14 * d + T_cell + 14 + 2 = 14 * d + T_cell + 16 := by omega
    change 5 + (2 + (dom.length * (14 * d + T_cell + 14 + 2) + 2)) ≤
      dom.length * (14 * d + T_cell + 16) + 9
    rw [h16]; omega
  refine ⟨y, free', S', outFn, htot, hysav, hyfree, hlo', hhi', hS', hyrep, ?_, hyframe⟩
  intro X hX
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hX
  exact hydone q hq hq

/-- Cell body for pointwise multiplication of `rStageCurRoot` and `rStageFbRoot` at `rCellKey`. -/
private def mulCellBody : Code .standard numRegs :=
  .seq (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ])
    (.seq trieGet
      (.seq (ram[ Signed.left ← rTrieVal; rTrieRoot ← rStageFbRoot; rTrieKey ← rCellKey ])
        (.seq trieGet
          (.seq (ram[ Signed.right ← rTrieVal ])
            (.seq (Signed.multiply (r := 47))
              (ram[ rTrieVal ← Signed.result ]))))))

/-- Tabulate the pointwise signed product of tries `rStageCurRoot` and `rStageFbRoot` across
`Reg.entryPtr[0 .. Reg.entryCount - 1]`, leaving the product trie root in `Reg.builtRoot`. -/
def tabulateMul : Code .standard numRegs := tabulateDom mulCellBody

private theorem mulCellBody_preserves (i : Fin numRegs) :
    ¬ IsCellMod i → mulCellBody.Preserves i := by
  intro hi
  exact ⟨by revert i hi; decide +kernel,
    trieGet_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel,
    trieGet_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel,
    signedMul_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel⟩

theorem tabulateMul_preserves (i : Fin numRegs) :
    ¬ IsTabMod i → tabulateMul.Preserves i :=
  tabulateDom_preserves i (mulCellBody_preserves i)

theorem exec_tabulateMul {w d domPtr free rootF rootG B : ℕ}
    {dom : List (Finset (Fin d))} {fnF fnG : ℕ → ℕ} {valF valG : Finset (Fin d) → ℤ}
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hdp : x.regs Reg.entryPtr = domPtr) (hdl : x.regs Reg.entryCount = dom.length)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (hrF : x.regs rStageCurRoot = rootF) (hrG : x.regs rStageFbRoot = rootG)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (htrieF : HoldsTrie x.mem free d rootF fnF)
    (htrieG : HoldsTrie x.mem free d rootG fnG)
    (hvalF : ∀ X ∈ dom, fnF (setMask X) = Signed.encode (valF X) ∧ (valF X).natAbs ≤ B)
    (hvalG : ∀ X ∈ dom, fnG (setMask X) = Signed.encode (valG X) ∧ (valG X).natAbs ≤ B)
    (hvalFG : ∀ X ∈ dom, (valF X * valG X).natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    ∃ y free' outFn,
      ExecWithin w tabulateMul x y (dom.length * (32 * d + 53) + 9) ∧
      y.regs Reg.builtRoot = free ∧ y.regs Reg.free = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      HoldsTrie y.mem free' d free outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = Signed.encode (valF X * valG X)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTabMod i → y.regs i = x.regs i := by
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let Inv (s : Data numRegs) : Prop :=
    s.regs rStageCurRoot = rootF ∧ s.regs rStageFbRoot = rootG
  have hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂ := by
    intro s₁ s₂ _ hregs ⟨h1, h2⟩
    exact ⟨(hregs rStageCurRoot (by decide)).symm.trans h1,
      (hregs rStageFbRoot (by decide)).symm.trans h2⟩
  have hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs Reg.dim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w mulCellBody s u (18 * d + 37) ∧
        u.regs rTrieVal = Signed.encode (valF dom[p] * valG dom[p]) ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i := by
    intro s p hp hsz hso hsd ⟨hsrF, hsrG⟩ hsmem hsck _
    have hXp : dom[p] ∈ dom := List.getElem_mem hp
    obtain ⟨hf_enc, hf_le⟩ := hvalF dom[p] hXp
    obtain ⟨hg_enc, hg_le⟩ := hvalG dom[p] hXp
    have hfg_le := hvalFG dom[p] hXp
    have htF_s : HoldsTrie s.mem free d rootF fnF := htrieF.congr_below hsmem
    have htG_s : HoldsTrie s.mem free d rootG fnG := htrieG.congr_below hsmem
    let u₀ := (s.set rTrieRoot rootF).set rTrieKey (setMask dom[p])
    have he₀ : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ]) s u₀ 2 := by
      wram_exec [hsrF, hsck]
    obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ := exec_trieGet u₀
      (by simp [u₀, hsz]) (by simp [u₀, hso]) (by simp [u₀, hsd])
      (by simp [u₀]) (by simp [u₀]) htF_s
      (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt dom[p]).le)
    rw [hf_enc] at hu₁_val
    have hu₁_srG : u₁.regs rStageFbRoot = rootG := by
      rw [hu₁_regs rStageFbRoot (Or.inr (by decide))]; simp [u₀, hsrG]
    have hu₁_ck : u₁.regs rCellKey = setMask dom[p] := by
      rw [hu₁_regs rCellKey (Or.inr (by decide))]; simp [u₀, hsck]
    let u₂ := ((u₁.set (Signed.left (r := 47)) (Signed.encode (valF dom[p]))).set
      rTrieRoot rootG).set rTrieKey (setMask dom[p])
    have he₂ : ExecWithin (B := .standard) w
        (ram[ Signed.left ← rTrieVal; rTrieRoot ← rStageFbRoot; rTrieKey ← rCellKey ])
        u₁ u₂ 3 := by
      wram_exec [hu₁_val, hu₁_srG, hu₁_ck]
    have htG_u₂ : HoldsTrie u₂.mem free d rootG fnG := by
      change HoldsTrie u₁.mem free d rootG fnG; rwa [hu₁_mem]
    obtain ⟨u₃, he₃, hu₃_val, hu₃_mem, hu₃_regs⟩ := exec_trieGet u₂
      (by simpa [u₂, u₀, hsz] using hu₁_regs rZero (Or.inl (by decide)))
      (by simpa [u₂, u₀, hso] using hu₁_regs rOne (Or.inl (by decide)))
      (by simpa [u₂, u₀, hsd] using hu₁_regs Reg.dim (Or.inl (by decide)))
      (by simp [u₂]) (by simp [u₂]) htG_u₂
      (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt dom[p]).le)
    rw [hg_enc] at hu₃_val
    have hu₃_left : u₃.regs (Signed.left (r := 47)) = Signed.encode (valF dom[p]) := by
      rw [hu₃_regs _ (Or.inl (by decide))]; simp [u₂]
    let u₄ := u₃.set (Signed.right (r := 47)) (Signed.encode (valG dom[p]))
    have he₄ : ExecWithin (B := .standard) w (ram[ Signed.right ← rTrieVal ]) u₃ u₄ 1 := by
      wram_exec [hu₃_val]
    obtain ⟨u₅, he₅, hu₅_res, hu₅_mem, _⟩ := exec_signedMul hfit_val hf_le hg_le hfg_le u₄
      (by simp only [u₄, Data.set_regs_of_ne (by decide :
            Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₃_left)
      (by simp [u₄])
    let u := u₅.set rTrieVal (Signed.encode (valF dom[p] * valG dom[p]))
    have he₆ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₅ u 1 := by
      wram_exec [hu₅_res]
    have htot : ExecWithin w mulCellBody s u (18 * d + 37) :=
      (he₀.seq (he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq he₆)))))).mono (by omega)
    refine ⟨u, htot, by simp [u], hu₅_mem.trans (hu₃_mem.trans hu₁_mem),
      fun i hi => htot.regs_eq (mulCellBody_preserves i hi)⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := mulCellBody)
      (cellFn := fun X => Signed.encode (valF X * valG X))
      (T_cell := 18 * d + 37) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hrF, hrG⟩ hInv_congr hcell hfit_free hfit_mask
  have he' : ExecWithin w tabulateMul x y (dom.length * (32 * d + 53) + 9) :=
    he.mono (by
      have : 14 * d + (18 * d + 37) + 16 = 32 * d + 53 := by omega
      rw [this])
  exact ⟨y, free', outFn, he', hysav, hyfree, hlo', hhi',
    HoldsTrie.iff_exists_trieRep.mpr
      ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩,
    hydom, hyframe, fun i hi => he'.regs_eq (tabulateMul_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
