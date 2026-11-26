/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TrimmedYates
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Tabulate
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Trie
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.Nat.Bitwise

/-!
# Multi-stage trimmed Yates transform on the word RAM

Executes `d` coordinate passes of `yatesTransform` (`+1` for zeta, `-1` for Möbius) over an active
subset domain, falling back to precomputed stage tables below the cardinality cutoff (`stagesCode`,
`exec_stagesCode`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.IsStageMod`: modified-register footprint of `stagesCode`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.stagesCode`: `d`-stage trimmed Yates loop storing stage
  trie roots at `rRootsOut[0 .. d]`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.natAbs_yatesTransform_le`,
  `yatesTransform_natOne_eq_intOne`: magnitude bound and scalar-cast bridge for `yatesTransform`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.stagesCode_preserves`, `exec_stagesCode`: register frame
  and `ExecWithin` specification for `stagesCode`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

theorem natAbs_yatesTransform_le {d : ℕ} {c : ℤ} (hc : c.natAbs ≤ 1)
    {l : List (Fin d)} (hl : l.Nodup) {G : Finset (Fin d) → ℤ} {B₀ : ℕ}
    (hG : ∀ T, (G T).natAbs ≤ B₀) (S : Finset (Fin d)) :
    (yatesTransform c l G S).natAbs ≤ 2 ^ d * B₀ := by
  rw [yatesTransform_apply c hl G S]
  calc (∑ U ∈ (S ∩ l.toFinset).powerset, c ^ #U • G (S \ U)).natAbs
      ≤ ∑ U ∈ (S ∩ l.toFinset).powerset, (c ^ #U * G (S \ U)).natAbs := by
        simpa only [smul_eq_mul] using Int.natAbs_sum_le _ _
    _ ≤ ∑ _U ∈ (S ∩ l.toFinset).powerset, B₀ := by
        refine Finset.sum_le_sum fun U _ => ?_
        rw [Int.natAbs_mul, Int.natAbs_pow]
        calc c.natAbs ^ #U * (G (S \ U)).natAbs
            ≤ 1 ^ #U * B₀ := Nat.mul_le_mul (Nat.pow_le_pow_left hc _) (hG _)
          _ = B₀ := by simp
    _ = 2 ^ #(S ∩ l.toFinset) * B₀ := by simp
    _ ≤ 2 ^ d * B₀ := by
        refine Nat.mul_le_mul_right B₀ (Nat.pow_le_pow_right Nat.two_pos ?_)
        simpa using Finset.card_le_univ (S ∩ l.toFinset)

theorem yatesTransform_natOne_eq_intOne {d : ℕ} (l : List (Fin d))
    (G : Finset (Fin d) → ℤ) :
    yatesTransform (1 : ℕ) l G = yatesTransform (1 : ℤ) l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    have hpass : yatesPass (1 : ℕ) i G = yatesPass (1 : ℤ) i G := by
      funext S; simp [yatesPass]
    rw [yatesTransform_cons, yatesTransform_cons, hpass, ih]

/-- Cell body for one trimmed Yates pass in coordinate `rGenBitMask = 1 <<< k`, with cutoff
`rStageCutoff`, current stage `rStageCurRoot`, fallback stage `rStageFbRoot`, and sign mode
`rSignMode` (`0` for `+1`, `1` for `-1`). -/
private def passCellBody : Code .standard numRegs :=
  .seq (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ])
    (.seq trieGet
      (.seq (ram[ rGenTmp ← rCellKey &&& rGenBitMask ])
        (.branch (.eq rGenTmp rZero)
          (ram[ rTrieVal ← rTrieVal ])
          (.seq (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ])
            (.seq trieGet
              (.seq (ram[ Signed.right ← rTrieVal ])
                (.seq (.branch (.eq rSignMode rZero)
                    (Signed.add (r := 47))
                    (Signed.subtract (r := 47)))
                  (ram[ rTrieVal ← Signed.result ]))))))))

private def passCode : Code .standard numRegs := tabulateDom passCellBody

private theorem passCellBody_preserves (i : Fin numRegs) :
    ¬ IsCellMod i → passCellBody.Preserves i := by
  intro hi
  refine ⟨?_, trieGet_preserves i ?_, ?_, ?_, ?_, trieGet_preserves i ?_, ?_,
    ⟨signedAdd_preserves i ?_, signedSub_preserves i ?_⟩, ?_⟩ <;>
    revert i hi <;> decide +kernel

private theorem passCode_preserves (i : Fin numRegs) :
    ¬ IsTabMod i → passCode.Preserves i :=
  tabulateDom_preserves i (passCellBody_preserves i)

private theorem exec_passCode {w d domPtr free curRoot fbRoot cutoff signMode B : ℕ}
    {coord : Fin d} {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {curFn fbFn : ℕ → ℕ} {G_k : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hdp : x.regs Reg.entryPtr = domPtr) (hdl : x.regs Reg.entryCount = dom.length)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (hbm : x.regs rGenBitMask = (1 <<< coord.val))
    (hcut : x.regs rStageCutoff = cutoff) (hsm : x.regs rSignMode = signMode)
    (hcr : x.regs rStageCurRoot = curRoot) (hfbr : x.regs rStageFbRoot = fbRoot)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrie_cur : HoldsTrie x.mem free d curRoot curFn)
    (htrie_fb : HoldsTrie x.mem free d fbRoot fbFn)
    (hcur_eq : ∀ X ∈ dom, curFn (setMask X) = Signed.encode (G_k X))
    (hfb_eq : ∀ Y, #Y < cutoff → P_low Y → fbFn (setMask Y) = Signed.encode (G_k Y))
    (hG_le : ∀ Y, (G_k Y).natAbs ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + 2 + 2 * d * dom.length))
    (hfit_mask : Fits w (2 ^ d)) :
    let c : ℤ := if signMode = 0 then 1 else -1
    ∃ y free' S' outFn,
      ExecWithin w passCode x y (dom.length * (32 * d + 63) + 9) ∧
      y.regs Reg.builtRoot = free ∧ y.regs Reg.free = free' ∧
      free + 2 ≤ free' ∧ free' ≤ free + 2 + 2 * d * dom.length ∧
      S' ⊆ Set.Ico free free' ∧ TrieRep y.mem d free S' outFn ∧
      (∀ X ∈ dom, outFn (setMask X) = Signed.encode (yatesPass c coord G_k X)) ∧
      (∀ a, a < free ∨ free' ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTabMod i → y.regs i = x.regs i := by
  intro c
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let Inv (s : Data numRegs) : Prop :=
    s.regs rGenBitMask = (1 <<< coord.val) ∧ s.regs rStageCutoff = cutoff ∧
    s.regs rSignMode = signMode ∧ s.regs rStageCurRoot = curRoot ∧
    s.regs rStageFbRoot = fbRoot
  have hInv_congr : ∀ s₁ s₂, (∀ a < free, s₁.mem a = s₂.mem a) →
      (∀ i, ¬ IsTabMod i → s₁.regs i = s₂.regs i) → Inv s₁ → Inv s₂ := by
    intro s₁ s₂ _ hregs ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(hregs rGenBitMask (by decide)).symm.trans h1,
      (hregs rStageCutoff (by decide)).symm.trans h2,
      (hregs rSignMode (by decide)).symm.trans h3,
      (hregs rStageCurRoot (by decide)).symm.trans h4,
      (hregs rStageFbRoot (by decide)).symm.trans h5⟩
  have hcell : ∀ s (p : ℕ) (hp : p < dom.length),
      s.regs rZero = 0 → s.regs rOne = 1 → s.regs Reg.dim = d → Inv s →
      (∀ a < free, s.mem a = x.mem a) →
      s.regs rCellKey = setMask dom[p] → s.regs rCellCard = #dom[p] →
      ∃ u, ExecWithin w passCellBody s u (18 * d + 47) ∧
        u.regs rTrieVal = Signed.encode (yatesPass c coord G_k dom[p]) ∧
        u.mem = s.mem ∧ ∀ i, ¬ IsCellMod i → u.regs i = s.regs i := by
    intro s p hp hsz hso hsd ⟨hsbm, hscut, hssm, hscr, hsfbr⟩ hsmem hsck hscc
    set X := dom[p]
    suffices h : ∃ u, ExecWithin w passCellBody s u (18 * d + 47) ∧
        u.regs rTrieVal = Signed.encode (yatesPass c coord G_k X) ∧ u.mem = s.mem by
      obtain ⟨u, hu, hval, hmem⟩ := h
      exact ⟨u, hu, hval, hmem, fun i hi => hu.regs_eq (passCellBody_preserves i hi)⟩
    have hX_mem : X ∈ dom := List.getElem_mem hp
    have ht_cur_s : HoldsTrie s.mem free d curRoot curFn := htrie_cur.congr_below hsmem
    have ht_fb_s : HoldsTrie s.mem free d fbRoot fbFn := htrie_fb.congr_below hsmem
    have hfit_bound : Fits w free := hfit_free.of_le (by omega)
    have hand_eq : setMask X &&& (1 <<< coord.val) =
        (if coord ∈ X then 2 ^ coord.val else 0) := by
      by_cases hcX : coord ∈ X <;> simp [Nat.shiftLeft_eq, Nat.and_two_pow, testBit_setMask, hcX]
    unfold passCellBody
    wram_exec [hscr, hsck]
    wram_call (exec_trieGet (bound := free) (fn := curFn) _ (by wram_simp [hsz])
      (by wram_simp [hso]) (by wram_simp [hsd]) (by wram_simp) (by wram_simp) ht_cur_s
      hfit_bound hfit_d (hfit_mask.of_le (setMask_lt X).le)) with u₁ ⟨hu₁_val, hu₁_mem, hu₁_regs⟩
    rw [hcur_eq X hX_mem] at hu₁_val
    by_cases hcX : coord ∈ X
    · have hf_pow : Fits w (2 ^ coord.val) :=
        hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos coord.isLt.le)
      have hfit_er : Fits w (setMask (X.erase coord)) := hfit_mask.of_le (setMask_lt _).le
      obtain ⟨selRoot, selFn, hsel, htsel, hval_er⟩ : ∃ selRoot selFn,
          (if cutoff < #X then curRoot else fbRoot) = selRoot ∧
          HoldsTrie s.mem free d selRoot selFn ∧
          selFn (setMask (X.erase coord)) = Signed.encode (G_k (X.erase coord)) := by
        have hcard_er : #(X.erase coord) + 1 = #X := Finset.card_erase_add_one hcX
        by_cases hlt_cut : cutoff < #X
        · exact ⟨curRoot, curFn, ite_eq_left hlt_cut, ht_cur_s,
            hcur_eq _ ((hdom_closed X hX_mem hcX).1 (by omega))⟩
        · exact ⟨fbRoot, fbFn, ite_eq_right hlt_cut, ht_fb_s,
            hfb_eq _ (by omega) ((hdom_closed X hX_mem hcX).2 (by omega))⟩
      have hsign : ∀ u : Data numRegs, u.regs rZero = 0 → u.regs rSignMode = signMode →
          u.regs (Signed.left (r := 47)) = Signed.encode (G_k X) →
          u.regs (Signed.right (r := 47)) = Signed.encode (G_k (X.erase coord)) →
          ∃ v, ExecWithin w (.branch (.eq rSignMode rZero) (Signed.add (r := 47))
              (Signed.subtract (r := 47))) u v 19 ∧
            v.regs (Signed.result (r := 47)) = Signed.encode (yatesPass c coord G_k X) ∧
            v.mem = u.mem := by
        intro u huz husm hul hur
        by_cases hsm0 : signMode = 0
        · obtain ⟨v, he, hres, hm, -⟩ :=
            exec_signedAdd hfit_val (hG_le X) (hG_le (X.erase coord)) u hul hur
          refine ⟨v, (he.branch_pos (by simp [Cond.holds_eq, huz, husm, hsm0])).mono (by omega),
            ?_, hm⟩
          simpa [yatesPass, hcX, c, hsm0] using hres
        · obtain ⟨v, he, hres, hm, -⟩ :=
            exec_signedSub hfit_val (hG_le X) (hG_le (X.erase coord)) u hul hur
          refine ⟨v, (he.branch_neg (by simp [Cond.holds_eq, huz, husm, hsm0])).mono (by omega),
            ?_, hm⟩
          simpa [yatesPass, hcX, c, hsm0, sub_eq_add_neg] using hres
      wram_exec * [hand_eq, ite_eq_left hcX, (Nat.two_pow_pos coord.val).ne', ← setMask_erase hcX]
      all_goals
        simp only [hc, ↓reduceIte] at hsel
        wram_call (exec_trieGet (bound := free) (root := selRoot) (fn := selFn) _ (by regs_frame)
          (by regs_frame) (by regs_frame) (by wram_simp [hsel]) (by wram_simp)
          (by simpa only [Data.set_mem, hu₁_mem] using htsel) hfit_bound hfit_d hfit_er)
          with u₄ ⟨hu₄_val, hu₄_mem, hu₄_regs⟩
        rw [hval_er] at hu₄_val
        wram_exec * -split [hu₄_val]
        wram_call (hsign _ (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp))
          with u₆ ⟨hres, hm₆⟩
        wram_exec * [hres]
        exact ⟨by wram_simp, by simp only [Data.set_mem, hm₆, hu₄_mem, hu₁_mem]⟩
    · wram_exec * [hand_eq, ite_eq_right hcX]
      exact ⟨by wram_simp [yatesPass, ite_eq_right hcX], by simp only [Data.set_mem, hu₁_mem]⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := passCellBody)
      (cellFn := fun X => Signed.encode (yatesPass c coord G_k X))
      (T_cell := 18 * d + 47) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hbm, hcut, hsm, hcr, hfbr⟩ hInv_congr hcell hfit_free hfit_mask
  have he' : ExecWithin w passCode x y (dom.length * (32 * d + 63) + 9) :=
    he.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 9)
  exact ⟨y, free', S', outFn, he', hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe,
    fun i hi => he'.regs_eq (passCode_preserves i hi)⟩

/-- Depth-`d` trie in `Ico 1 bound` whose footprint avoids `Ico exclLo exclHi` (used for the
`(d + 1)`-word stage-root array allocated at the start of `stagesCode`). -/
private def HoldsTrieOutside (mem : ℕ → ℕ) (exclLo exclHi bound d root : ℕ) (fn : ℕ → ℕ) : Prop :=
  ∃ S ⊆ Set.Ico 1 bound, Disjoint S (Set.Ico exclLo exclHi) ∧ TrieRep mem d root S fn

private theorem HoldsTrieOutside.toHoldsTrie {mem : ℕ → ℕ} {exclLo exclHi bound d root : ℕ}
    {fn : ℕ → ℕ} (h : HoldsTrieOutside mem exclLo exclHi bound d root fn) :
    HoldsTrie mem bound d root fn :=
  let ⟨S, hS, _, hrep⟩ := h; HoldsTrie.iff_exists_trieRep.mpr ⟨S, hS, hrep⟩

private theorem HoldsTrie.toOutside_of_le {mem : ℕ → ℕ} {b exclLo exclHi bound d root : ℕ}
    {fn : ℕ → ℕ} (h : HoldsTrie mem b d root fn) (hb_excl : b ≤ exclLo) (hb_bound : b ≤ bound) :
    HoldsTrieOutside mem exclLo exclHi bound d root fn := by
  rw [HoldsTrie.iff_exists_trieRep] at h
  obtain ⟨S, hS, hrep⟩ := h
  exact ⟨S, hS.trans (Set.Ico_subset_Ico_right hb_bound),
    Set.disjoint_left.mpr (fun _ ha he => ((hS ha).2.trans_le hb_excl).not_ge he.1), hrep⟩

/-- Registers potentially modified by `stagesCode`. -/
abbrev IsStageMod (i : Fin numRegs) : Prop :=
  IsTabMod i ∨ i = rRootsOut ∨ i = rStageIdx ∨ i = rGenBitMask ∨
    i = rStageCurRoot ∨ i = rStageFbRoot

private def stagesStep : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rRootsOut + rStageIdx;
    rStageCurRoot ← *rGenTmp;
    if rStageCutoff = rZero then [
      rStageFbRoot ← #0
    ] else [
      rGenTmp ← rFbRoots + rStageIdx;
      rStageFbRoot ← *rGenTmp
    ];
    rGenBitMask ← rOne <<< rStageIdx ])
  (.seq passCode
    (ram[
      rStageIdx ← rStageIdx + rOne;
      rGenTmp ← rRootsOut + rStageIdx;
      *rGenTmp ← Reg.builtRoot ]))

/-- Allocate `(d + 1)` stage-root slots at `Reg.free` (returned in `rRootsOut`), store
`rStageCurRoot` as stage `0`, and run `d` trimmed passes over `dom`. -/
def stagesCode : Code .standard numRegs :=
  .seq (ram[
    rRootsOut ← Reg.free;
    rGenTmp ← Reg.dim + rOne;
    Reg.free ← Reg.free + rGenTmp;
    *rRootsOut ← rStageCurRoot;
    rStageIdx ← #0 ])
  (.loop (.lt rStageIdx Reg.dim) stagesStep)

theorem stagesCode_preserves (i : Fin numRegs) :
    ¬ IsStageMod i → stagesCode.Preserves i := by
  intro hi
  refine ⟨?_, ?_, passCode_preserves i fun ht => hi (Or.inl ht), ?_⟩ <;>
    revert i hi <;> decide +kernel

theorem exec_stagesCode {w d domPtr free initRoot fbBase cutoff signMode B₀ B : ℕ}
    {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {initFn : ℕ → ℕ} {G : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hdp : x.regs Reg.entryPtr = domPtr) (hdl : x.regs Reg.entryCount = dom.length)
    (hcut : x.regs rStageCutoff = cutoff) (hsm : x.regs rSignMode = signMode)
    (hfbb : x.regs rFbRoots = fbBase)
    (hir : x.regs rStageCurRoot = initRoot) (hfree : x.regs Reg.free = free)
    (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, ∀ coord : Fin d, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrie_init : HoldsTrie x.mem free d initRoot initFn)
    (hinit_eq : ∀ X ∈ dom, initFn (setMask X) = Signed.encode (G X))
    (hfb_valid : 0 < cutoff → fbBase + d ≤ free ∧
      ∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (fbBase + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) = Signed.encode
            (yatesTransform (if signMode = 0 then (1 : ℤ) else -1)
              ((List.finRange d).take k) G Y))
    (hG_le : ∀ Y, (G Y).natAbs ≤ B₀) (hB : 2 ^ d * B₀ ≤ B)
    (hfit_val : Fits w (8 * B + 4))
    (hfit_free : Fits w (free + d + 1 + d * (2 * d * dom.length + 2)))
    (hfit_mask : Fits w (2 ^ d)) :
    let c : ℤ := if signMode = 0 then 1 else -1
    ∃ y endFree,
      ExecWithin w stagesCode x y (d * (dom.length * (32 * d + 63) + 22) + 7) ∧
      y.regs rRootsOut = free ∧ y.regs Reg.free = endFree ∧
      free + d + 1 ≤ endFree ∧ endFree ≤ free + d + 1 + d * (2 * d * dom.length + 2) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (free + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform c ((List.finRange d).take k) G X)) ∧
      (∀ a, a < free ∨ endFree ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsStageMod i → y.regs i = x.regs i := by
  intro c
  have hc_abs : c.natAbs ≤ 1 := by dsimp [c]; split_ifs <;> decide
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let exclHi := free + d + 1
  let P (k : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧
    s.regs Reg.entryPtr = domPtr ∧ s.regs Reg.entryCount = dom.length ∧
    s.regs rStageCutoff = cutoff ∧ s.regs rSignMode = signMode ∧
    s.regs rFbRoots = fbBase ∧ s.regs rRootsOut = free ∧
    ∃ curFree, s.regs Reg.free = curFree ∧
      exclHi ≤ curFree ∧ curFree ≤ exclHi + k * (2 * d * dom.length + 2) ∧
      (∀ j ≤ k, ∃ stFn, HoldsTrieOutside s.mem free exclHi curFree d (s.mem (free + j)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform c ((List.finRange d).take j) G X)) ∧
      (∀ a, a < free ∨ curFree ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rStageIdx) s) (hk : s.regs rStageIdx < d) :
      ∃ z, ExecWithin w stagesStep s z (dom.length * (32 * d + 63) + 20) ∧
        P (s.regs rStageIdx + 1) z ∧ z.regs rStageIdx = s.regs rStageIdx + 1 := by
    generalize hk_eq : s.regs rStageIdx = k at hs hk ⊢
    obtain ⟨hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro,
      curFree, hsfree, hcf_lo, hcf_hi, hstages, hsframe⟩ := hs
    let coord : Fin d := ⟨k, hk⟩
    let G_k := yatesTransform c ((List.finRange d).take k) G
    obtain ⟨curFn, hcur_out, hcur_eq⟩ := hstages k le_rfl
    have hG_k_le : ∀ Y, (G_k Y).natAbs ≤ B := fun Y =>
      (natAbs_yatesTransform_le hc_abs ((List.nodup_finRange d).sublist (List.take_sublist _ _))
        hG_le Y).trans hB
    have hf_ro_k : Fits w (free + k) := hfit_free.of_le (by omega)
    have hf_shl : Fits w (1 <<< k) :=
      Nat.one_shiftLeft k ▸ hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos hk.le)
    have hf_k1 : Fits w (k + 1) := hfit_d.of_le (by omega)
    have hf_ro_k1 : Fits w (free + (k + 1)) := hfit_free.of_le (by omega)
    have hpass_le := Nat.add_one_mul k (2 * d * dom.length + 2)
    have hpass_mul : (k + 1) * (2 * d * dom.length + 2) ≤ d * (2 * d * dom.length + 2) :=
      Nat.mul_le_mul_right _ hk
    have hpass_fit : Fits w (curFree + 2 + 2 * d * dom.length) := hfit_free.of_le (by omega)
    -- The fallback trie of stage `k`: empty when `cutoff = 0`, else stored at `fbBase + k`.
    obtain ⟨fbRoot, fbFn, hfbr, hfb_tr, hfb_eq⟩ : ∃ fbRoot fbFn,
        (if cutoff = 0 then 0 else s.mem (fbBase + k)) = fbRoot ∧
        HoldsTrie s.mem curFree d fbRoot fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y → fbFn (setMask Y) = Signed.encode (G_k Y) := by
      by_cases hcut0 : cutoff = 0
      · exact ⟨0, fun _ => 0, by simp [hcut0], HoldsTrie.zero_root _ _ _, fun _ hY _ => by omega⟩
      · obtain ⟨hfbb_le, hfb_all⟩ := hfb_valid (by omega)
        obtain ⟨fbFn, hfb_tr, hfb_eq⟩ := hfb_all k hk
        refine ⟨s.mem (fbBase + k), fbFn, by simp [hcut0], ?_, hfb_eq⟩
        rw [hsframe _ (Or.inl (by omega))]
        exact (hfb_tr.congr_below fun a ha => hsframe a (Or.inl ha)).mono_bound (by omega)
    obtain ⟨u₀, he₀, hu₀cr, hu₀fbr, hu₀bm, hu₀mem⟩ : ∃ u₀, ExecWithin (B := .standard) w (ram[
          rGenTmp ← rRootsOut + rStageIdx;
          rStageCurRoot ← *rGenTmp;
          if rStageCutoff = rZero then [
            rStageFbRoot ← #0
          ] else [
            rGenTmp ← rFbRoots + rStageIdx;
            rStageFbRoot ← *rGenTmp
          ];
          rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
        u₀.regs rStageCurRoot = s.mem (free + k) ∧ u₀.regs rStageFbRoot = fbRoot ∧
        u₀.regs rGenBitMask = (1 <<< coord.val) ∧ u₀.mem = s.mem := by
      by_cases hcut0 : cutoff = 0
      · wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0]
        wram_simp [coord, ← hfbr, hcut0]
      · have : Fits w (fbBase + k) := hfit_free.of_le (by have := (hfb_valid (by omega)).1; omega)
        wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0, hsfbb]
        wram_simp [coord, ← hfbr, hcut0]
    have hdom_s : HoldsDom s.mem domPtr dom := fun p hp => by
      rw [hsframe _ (Or.inl (by omega)), hsframe _ (Or.inl (by omega))]
      exact hdom p hp
    obtain ⟨u₁, free', S_new, outFn, he_pass, hu₁_sav, hu₁_free, hcf_le', hfree'_le,
        hS_new, hrep_new, hout_eq, hu₁_frame, hu₁_regs⟩ :=
      exec_passCode (domPtr := domPtr) (free := curFree) (cutoff := cutoff) (signMode := signMode)
        (coord := coord) (P_low := P_low) (G_k := G_k) (B := B) u₀
        (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
        (by regs_frame) (by omega) hu₀bm (by regs_frame) (by regs_frame) hu₀cr hu₀fbr hnd
        (by rwa [hu₀mem]) (by omega) (fun X hX hc => hdom_closed X hX coord hc)
        (by rw [hu₀mem]; exact hcur_out.toHoldsTrie) (by rwa [hu₀mem]) hcur_eq hfb_eq hG_k_le
        hfit_val hpass_fit hfit_mask
    obtain ⟨z, he_st, hz_k, hz_mem⟩ : ∃ z, ExecWithin (B := .standard) w (ram[
        rStageIdx ← rStageIdx + rOne;
        rGenTmp ← rRootsOut + rStageIdx;
        *rGenTmp ← Reg.builtRoot ]) u₁ z 3 ∧ z.regs rStageIdx = k + 1 ∧
        z.mem = Function.update u₁.mem (free + (k + 1)) curFree := by
      wram_exec * [hu₁_sav]
      wram_simp
    -- Cells below `curFree` other than the new stage slot keep their values from `s`.
    have hz_old (a : ℕ) (ha : a ≠ free + (k + 1)) (hlt : a < curFree) : z.mem a = s.mem a := by
      rw [hz_mem, Function.update_of_ne ha, hu₁_frame a (Or.inl hlt), hu₀mem]
    refine ⟨z, (he₀.seq (he_pass.seq he_st)).mono (by omega), ⟨by regs_frame, by regs_frame,
      by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, free', by regs_frame, by omega, by omega, fun j hj => ?_, fun a ha => ?_⟩,
      hz_k⟩
    · rcases Nat.le_succ_iff.mp hj with hj | rfl
      · obtain ⟨stFn, ⟨S_j, hSj_sub, hSj_disj, hSj_rep⟩, hst_eq⟩ := hstages j hj
        have hslot : free + (k + 1) ∈ Set.Ico free exclHi := ⟨by omega, by omega⟩
        refine ⟨stFn, ⟨S_j, fun a ha => ⟨(hSj_sub ha).1, (hSj_sub ha).2.trans_le (by omega)⟩,
          hSj_disj, ?_⟩, hst_eq⟩
        rw [hz_old _ (by omega) (by omega)]
        exact hSj_rep.congr_mem fun a ha =>
          hz_old a (fun h => Set.disjoint_left.1 hSj_disj ha (h ▸ hslot)) (hSj_sub ha).2
      · refine ⟨outFn, ⟨S_new, fun a ha => ⟨by have := (hS_new ha).1; omega, (hS_new ha).2⟩,
          Set.disjoint_left.2 fun a ha hx => by have := (hS_new ha).1; have := hx.2; omega,
          ?_⟩, fun X hX => ?_⟩
        · rw [(congrFun hz_mem _).trans (Function.update_self _ _ _)]
          exact hrep_new.congr_mem fun a ha => by
            have := (hS_new ha).1
            rw [hz_mem, Function.update_of_ne (by omega)]
        · rw [List.take_succ_eq_append_getElem (by simpa using hk), List.getElem_finRange,
            yatesTransform_append, yatesTransform_cons, yatesTransform_nil]
          exact hout_eq X hX
    · rw [hz_mem, Function.update_of_ne (by omega),
        hu₁_frame a (ha.imp (fun _ => by omega) id), hu₀mem,
        hsframe a (ha.imp id fun _ => by omega)]
  have hf_d1 : Fits w (d + 1) := hfit_free.of_le (by omega)
  have hf_excl : Fits w (free + (d + 1)) := hfit_free.of_le (by omega)
  have hf_free0 : Fits w free := hfit_free.of_le (by omega)
  obtain ⟨s₀, hinit_ex, hs₀ro, hs₀fr, hs₀k, hs₀mem⟩ : ∃ s₀, ExecWithin (B := .standard) w (ram[
      rRootsOut ← Reg.free;
      rGenTmp ← Reg.dim + rOne;
      Reg.free ← Reg.free + rGenTmp;
      *rRootsOut ← rStageCurRoot;
      rStageIdx ← #0 ]) x s₀ 5 ∧
      s₀.regs rRootsOut = free ∧ s₀.regs Reg.free = exclHi ∧ s₀.regs rStageIdx = 0 ∧
      s₀.mem = Function.update x.mem free initRoot := by
    wram_exec [ho, hd, hir, hfree]
    exact ⟨by wram_simp, by wram_simp [exclHi]; omega, by wram_simp, by wram_simp⟩
  have hs₀P : P (s₀.regs rStageIdx) s₀ := by
    rw [hs₀k]
    refine ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, by regs_frame, by regs_frame, hs₀ro, exclHi, hs₀fr, le_rfl, by omega, ?_, ?_⟩
    · intro j hj
      obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
      simp only [Nat.add_zero, List.take_zero, yatesTransform_nil]
      rw [(congrFun hs₀mem free).trans (Function.update_self _ _ _)]
      exact ⟨initFn, (htrie_init.congr_below fun a ha => by
        rw [hs₀mem, Function.update_of_ne (by omega)]).toOutside_of_le le_rfl (by omega), hinit_eq⟩
    · exact fun a _ => (congrFun hs₀mem a).trans (Function.update_of_ne (by omega) _ _)
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
    (by simp [hs₀k]) hs₀P
  obtain ⟨_, _, _, _, _, _, _, _, hyro, endFree, hyfr, hlo_ef, hhi_ef, hystages, hyframe⟩ := hyP
  have htot : ExecWithin w stagesCode x y (d * (dom.length * (32 * d + 63) + 22) + 7) :=
    (hinit_ex.seq hloop).mono (by
      rw [hs₀k, Nat.sub_zero, Nat.add_assoc _ 20 2]
      omega)
  refine ⟨y, endFree, htot, hyro, hyfr, hlo_ef, hhi_ef,
    fun k hk => let ⟨stFn, hout, heq⟩ := hystages k hk; ⟨stFn, hout.toHoldsTrie, heq⟩,
    hyframe, fun i hi => htot.regs_eq (stagesCode_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
