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
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

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
    (tabulateDom cellBody).Preserves i := by
  refine ⟨trieInit_preserves i ?_, ?_, ?_, hcell fun hc => hi (Or.inl hc), ?_,
    trieSet_preserves i ?_, ?_⟩ <;> clear hcell <;> revert i hi <;> decide +kernel

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
  -- What `¬ IsTabMod i` gives, in the shapes of the frames below.
  have hnt (i : Fin numRegs) (hi : ¬ IsTabMod i) : ¬ IsCellMod i ∧ i ≠ rCellIdx ∧
      i ≠ Reg.builtRoot ∧ i ≠ rCellKey ∧ i ≠ rCellCard ∧ i ≠ rGenTmp ∧ i ≠ rTrieRoot ∧
      i ≠ rTrieKey ∧ (i ≠ rTrieRoot ∧ i ≠ Reg.free) ∧
      (i ≠ Reg.free ∧ (i.val < 19 ∨ 23 ≤ i.val)) := by
    revert i; decide +kernel
  obtain ⟨s₀, hinit0, hs₀_root, hs₀_free, hs₀_rep, hs₀_frame, hs₀_regs⟩ :=
    exec_trieInit (d := d) x hz ho hfree (by omega) (hfit_free.of_le (by omega))
  let s₁ := (s₀.set Reg.builtRoot free).set rCellIdx 0
  have hinit1 : ExecWithin (B := .standard) w (ram[ Reg.builtRoot ← rTrieRoot; rCellIdx ← #0 ])
      s₀ s₁ 2 := by wram_exec [hs₀_root]
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    (∀ i, ¬ IsTabMod i → s.regs i = x.regs i) ∧ s.regs Reg.builtRoot = free ∧
    ∃ curFree S fn, s.regs Reg.free = curFree ∧
      free + 2 ≤ curFree ∧ curFree ≤ free + 2 + 2 * d * p ∧
      S ⊆ Set.Ico free curFree ∧ TrieRep s.mem d free S fn ∧
      (∀ q (hq : q < dom.length), q < p → fn (setMask dom[q]) = cellFn dom[q]) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rCellIdx) s) (hp : s.regs rCellIdx < dom.length) :
      ∃ z, ExecWithin w (tabulateDomStep cellBody) s z (14 * d + T_cell + 14) ∧
        P (s.regs rCellIdx + 1) z ∧ z.regs rCellIdx = s.regs rCellIdx + 1 := by
    generalize hp_eq : s.regs rCellIdx = p at hs hp ⊢
    obtain ⟨hsx, hssav, curFree, S, fn, hsfree, hcf_lo, hcf_hi, hS_sub, hsrep, hdone, hsframe⟩ := hs
    have hsmem (a : ℕ) (ha : a < free) : s.mem a = x.mem a := hsframe a (Or.inl ha)
    obtain ⟨hmk, hsz⟩ := hdom p hp
    rw [two_mul] at hmk hsz
    have hrmk := (hsmem _ (by omega)).trans hmk
    have hrsz := (hsmem _ (by omega)).trans hsz
    have hfit_p : Fits w (domPtr + (p + p) + 1) := hfit_free.of_le (by omega)
    have hcf_fit : Fits w (curFree + 2 * d) := hfit_free.of_le (by
      have := Nat.mul_add (2 * d) p 1 ▸ Nat.mul_le_mul_left (2 * d) (Nat.succ_le_of_lt hp)
      omega)
    unfold tabulateDomStep
    wram_exec * [hrmk, hrsz]
    wram_call (hcell _ p hp (by regs_frame) (by regs_frame) (by regs_frame)
      (hInv_congr x _ (fun a ha => (hsmem a ha).symm) (fun i hi => by
        obtain ⟨_, _, _, _, _, _, _⟩ := hnt i hi; regs_frame) hInv_init)
      hsmem (by wram_simp) (by wram_simp)) with u₁ ⟨hu₁_val, hu₁_mem, hu₁_regs⟩
    wram_exec *
    obtain ⟨u₃, S', free', he_set, hu₃_free, hcf_le', hfree'_le, hS'_sub, hu₃_frame, hu₃_rep,
        hu₃_regs⟩ :=
      exec_trieSet (lo := free) (free := curFree) ((u₁.set rTrieRoot free).set rTrieKey
        (setMask dom[p])) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
        (by regs_frame) (by regs_frame) (by regs_frame) hfree_pos (by omega) (by omega) hS_sub
        (by simpa only [Data.set_mem, hu₁_mem] using hsrep) (setMask_lt _) hcf_fit hfit_d
        (hfit_mask.of_le (setMask_lt _).le)
    wram_call he_set
    wram_exec *
    refine ⟨⟨fun i hi => ?_, by regs_frame, free', S', _, by regs_frame, by omega,
      by rw [mul_add]; omega, hS'_sub, hu₃_rep, fun q hq hqp => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := hnt i hi
      regs_frame
    · simp only [Nat.mod_eq_of_lt (setMask_lt _), setMask_injective.eq_iff, hnd.getElem_inj_iff]
      split_ifs with hqp'
      · subst hqp'; rfl
      · exact hdone q hq (by omega)
    · refine (hu₃_frame a ha).trans ?_
      simpa only [Data.set_mem, hu₁_mem] using hsframe a (by omega)
  have hs₁P : P (s₁.regs rCellIdx) s₁ := by
    refine ⟨fun i hi => ?_, by simp [s₁], free + 2, _, _, by regs_frame, le_rfl, by simp [s₁],
      by simp [Set.insert_subset_iff], hs₀_rep, by simp [s₁],
      fun a ha => hs₀_frame a ⟨by omega, by omega⟩⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := hnt i hi
    regs_frame
  obtain ⟨y, hloop, ⟨-, hysav, free', S', outFn, hyfree, hlo', hhi', hS', hyrep, hydone, hyframe⟩,
      -⟩ := ExecWithin.loop_count P (fun s hs => (hs.1 _ (by decide)).trans hdl) hbody
    (by simp [s₁]) hs₁P
  refine ⟨y, free', S', outFn, (hinit0.seq (hinit1.seq hloop)).mono
      (le_of_eq (by simp only [s₁, Data.set_regs_self, Nat.sub_zero]; ring)),
    hysav, hyfree, hlo', hhi', hS', hyrep, fun X hX => ?_, hyframe⟩
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
  refine ⟨?_, trieGet_preserves i ?_, ?_, trieGet_preserves i ?_, ?_, signedMul_preserves i ?_,
    ?_⟩ <;> revert i hi <;> decide +kernel

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
    exact ⟨(hregs _ (by decide)).symm.trans h1, (hregs _ (by decide)).symm.trans h2⟩
  have hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs Reg.dim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w mulCellBody s u (18 * d + 37) ∧
        u.regs rTrieVal = Signed.encode (valF dom[p] * valG dom[p]) ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i := by
    intro s p hp hsz hso hsd ⟨hsrF, hsrG⟩ hsmem hsck _
    suffices h : ∃ u, ExecWithin w mulCellBody s u (18 * d + 37) ∧
        u.regs rTrieVal = Signed.encode (valF dom[p] * valG dom[p]) ∧ u.mem = s.mem from
      h.imp fun u ⟨hu, hval, hmem⟩ =>
        ⟨hu, hval, hmem, fun i hi => hu.regs_eq (mulCellBody_preserves i hi)⟩
    have hXp : dom[p] ∈ dom := List.getElem_mem hp
    have hfit_bound : Fits w free := hfit_free.of_le (by omega)
    have hfit_key : Fits w (setMask dom[p]) := hfit_mask.of_le (setMask_lt _).le
    unfold mulCellBody
    wram_exec [hsrF, hsck]
    wram_call (exec_trieGet (bound := free) (fn := fnF) _ (by wram_simp [hsz]) (by wram_simp [hso])
      (by wram_simp [hsd]) (by wram_simp) (by wram_simp) (htrieF.congr_below hsmem) hfit_bound
      hfit_d hfit_key) with u₁ ⟨hu₁_val, hu₁_mem, hu₁_regs⟩
    rw [(hvalF _ hXp).1] at hu₁_val
    wram_exec *
    wram_call (exec_trieGet (bound := free) (root := rootG) (fn := fnG) _ (by regs_frame)
      (by regs_frame) (by regs_frame) (by wram_simp) (by wram_simp)
      (by simpa only [Data.set_mem, hu₁_mem] using htrieG.congr_below hsmem) hfit_bound hfit_d
      hfit_key) with u₃ ⟨hu₃_val, hu₃_mem, hu₃_regs⟩
    rw [(hvalG _ hXp).1] at hu₃_val
    wram_exec *
    wram_call (exec_signedMul hfit_val (hvalF _ hXp).2 (hvalG _ hXp).2 (hvalFG _ hXp) _
      (by regs_frame) (by wram_simp)) with u₅ ⟨hres, hm₅, -⟩
    wram_exec * [hres]
    exact ⟨by wram_simp, by simp only [Data.set_mem, hm₅, hu₃_mem, hu₁_mem]⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := mulCellBody)
      (cellFn := fun X => Signed.encode (valF X * valG X))
      (T_cell := 18 * d + 37) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hrF, hrG⟩ hInv_congr hcell hfit_free hfit_mask
  have he' := he.mono (T₂ := dom.length * (32 * d + 53) + 9) (le_of_eq (by ring))
  exact ⟨y, free', outFn, he', hysav, hyfree, hlo', hhi', HoldsTrie.iff_exists_trieRep.mpr
    ⟨S', fun a ha => ⟨hfree_pos.trans (hS' ha).1, (hS' ha).2⟩, hyrep⟩, hydom, hyframe,
    fun i hi => he'.regs_eq (tabulateMul_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
