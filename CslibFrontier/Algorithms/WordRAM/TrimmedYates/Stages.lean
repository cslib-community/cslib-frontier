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
import CslibFrontier.Computability.WordRAM.SymbolicExec

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
  exact ⟨by revert i hi; decide +kernel,
    trieGet_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel,
    by revert i hi; decide +kernel,
    by revert i hi; decide +kernel,
    trieGet_preserves i (by revert i hi; decide +kernel),
    by revert i hi; decide +kernel,
    ⟨signedAdd_preserves i (by revert i hi; decide +kernel),
      signedSub_preserves i (by revert i hi; decide +kernel)⟩,
    by revert i hi; decide +kernel⟩

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
    let X := dom[p]
    change s.regs rCellKey = setMask X at hsck
    change s.regs rCellCard = #X at hscc
    have hX_mem : X ∈ dom := List.getElem_mem hp
    have ht_cur_s : HoldsTrie s.mem free d curRoot curFn := htrie_cur.congr_below hsmem
    have ht_fb_s : HoldsTrie s.mem free d fbRoot fbFn := htrie_fb.congr_below hsmem
    let u₀ := (s.set rTrieRoot curRoot).set rTrieKey (setMask X)
    have he₀ : ExecWithin (B := .standard) w
        (ram[ rTrieRoot ← rStageCurRoot; rTrieKey ← rCellKey ]) s u₀ 2 := by
      wram_exec [hscr, hsck]
    obtain ⟨u₁, he₁, hu₁_val, hu₁_mem, hu₁_regs⟩ :=
      exec_trieGet (root := curRoot) (key := setMask X) u₀
        (by simp [u₀, hsz]) (by simp [u₀, hso]) (by simp [u₀, hsd])
        (by simp [u₀]) (by simp [u₀]) ht_cur_s
        (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt _).le)
    rw [hcur_eq X hX_mem] at hu₁_val
    have hand_eq : setMask X &&& (1 <<< coord.val) =
        (if coord ∈ X then 2 ^ coord.val else 0) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
      by_cases hj : j = coord.val
      · subst hj
        rw [testBit_setMask]
        by_cases hcX : coord ∈ X <;> simp [hcX]
      · have hne : coord.val ≠ j := Ne.symm hj
        by_cases hcX : coord ∈ X <;> simp [hcX, hne]
    have hf_and : Fits w (setMask X &&& (1 <<< coord.val)) :=
      hfit_mask.of_le (Nat.and_le_left.trans (setMask_lt X).le)
    have hu₁_ck : u₁.regs rCellKey = setMask X := by
      rw [hu₁_regs rCellKey (Or.inr (by decide))]; simp [u₀, hsck]
    have hu₁_bm : u₁.regs rGenBitMask = (1 <<< coord.val) := by
      rw [hu₁_regs rGenBitMask (Or.inr (by decide))]; simp [u₀, hsbm]
    let u₂ := u₁.set rGenTmp (setMask X &&& (1 <<< coord.val))
    have he₂ : ExecWithin (B := .standard) w
        (ram[ rGenTmp ← rCellKey &&& rGenBitMask ]) u₁ u₂ 1 := by
      wram_exec [hu₁_ck, hu₁_bm]
    have hu₂_z : u₂.regs rZero = 0 := by
      simp only [u₂, Data.set_regs_of_ne (by decide : rZero ≠ rGenTmp)]
      rw [hu₁_regs rZero (Or.inl (by decide))]; simp [u₀, hsz]
    by_cases hcX : coord ∈ X
    · have hgt_ne : u₂.regs rGenTmp ≠ u₂.regs rZero := by
        rw [hu₂_z]; simp only [u₂, Data.set_regs_self, hand_eq, hcX, ↓reduceIte]
        exact (Nat.two_pow_pos coord.val).ne'
      have hcard_er : #(X.erase coord) + 1 = #X := Finset.card_erase_add_one hcX
      have hf_xor : Fits w (setMask X ^^^ (1 <<< coord.val)) := by
        rw [← setMask_erase hcX]; exact hfit_mask.of_le (setMask_lt _).le
      have hu₂_val : u₂.regs rTrieVal = Signed.encode (G_k X) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rTrieVal ≠ rGenTmp)]; exact hu₁_val
      have hu₂_ck : u₂.regs rCellKey = setMask X := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rCellKey ≠ rGenTmp)]; exact hu₁_ck
      have hu₂_bm : u₂.regs rGenBitMask = (1 <<< coord.val) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rGenBitMask ≠ rGenTmp)]; exact hu₁_bm
      have hu₂_cut : u₂.regs rStageCutoff = cutoff := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageCutoff ≠ rGenTmp)]
        rw [hu₁_regs rStageCutoff (Or.inr (by decide))]; simp [u₀, hscut]
      have hu₂_cc : u₂.regs rCellCard = #X := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rCellCard ≠ rGenTmp)]
        rw [hu₁_regs rCellCard (Or.inr (by decide))]; simp [u₀, hscc]
      have hu₂_cr : u₂.regs rStageCurRoot = curRoot := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageCurRoot ≠ rGenTmp)]
        rw [hu₁_regs rStageCurRoot (Or.inr (by decide))]; simp [u₀, hscr]
      have hu₂_fbr : u₂.regs rStageFbRoot = fbRoot := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rStageFbRoot ≠ rGenTmp)]
        rw [hu₁_regs rStageFbRoot (Or.inr (by decide))]; simp [u₀, hsfbr]
      have hsel : ∃ u₃ selRoot selFn,
          ExecWithin (B := .standard) w (ram[
            Signed.left ← rTrieVal;
            rTrieKey ← rCellKey ^^^ rGenBitMask;
            if rStageCutoff < rCellCard then [
              rTrieRoot ← rStageCurRoot
            ] else [
              rTrieRoot ← rStageFbRoot
            ] ]) u₂ u₃ 5 ∧
          u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
          u₃.regs rTrieKey = setMask (X.erase coord) ∧
          u₃.regs rTrieRoot = selRoot ∧
          u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs Reg.dim = d ∧
          u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem ∧
          HoldsTrie u₃.mem free d selRoot selFn ∧
          selFn (setMask (X.erase coord)) = Signed.encode (G_k (X.erase coord)) := by
        have hu₂_o : u₂.regs rOne = 1 := by
          simp only [u₂, Data.set_regs_of_ne (by decide : rOne ≠ rGenTmp)]
          rw [hu₁_regs rOne (Or.inl (by decide))]; simp [u₀, hso]
        have hu₂_d : u₂.regs Reg.dim = d := by
          simp only [u₂, Data.set_regs_of_ne (by decide : Reg.dim ≠ rGenTmp)]
          rw [hu₁_regs Reg.dim (Or.inl (by decide))]; simp [u₀, hsd]
        have hu₂_sm : u₂.regs rSignMode = signMode := by
          simp only [u₂, Data.set_regs_of_ne (by decide : rSignMode ≠ rGenTmp)]
          rw [hu₁_regs rSignMode (Or.inr (by decide))]; simp [u₀, hssm]
        by_cases hlt_cut : cutoff < #X
        · have hst : ∃ u₃, ExecWithin (B := .standard) w (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ]) u₂ u₃ 5 ∧
              u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
              u₃.regs rTrieKey = setMask (X.erase coord) ∧
              u₃.regs rTrieRoot = curRoot ∧
              u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs Reg.dim = d ∧
              u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem := by
            wram_exec [hu₂_val, hu₂_ck, hu₂_bm, hu₂_cut, hu₂_cc, hu₂_cr, hlt_cut]
            wram_simp [setMask_erase hcX, hu₂_z, hu₂_o, hu₂_d, hu₂_sm]
          obtain ⟨u₃, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃⟩ := hst
          refine ⟨u₃, curRoot, curFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, ?_,
            hcur_eq _ ((hdom_closed X hX_mem hcX).1 (by omega))⟩
          rw [hm₃]; change HoldsTrie u₁.mem free d curRoot curFn; rwa [hu₁_mem]
        · have hst : ∃ u₃, ExecWithin (B := .standard) w (ram[
              Signed.left ← rTrieVal;
              rTrieKey ← rCellKey ^^^ rGenBitMask;
              if rStageCutoff < rCellCard then [
                rTrieRoot ← rStageCurRoot
              ] else [
                rTrieRoot ← rStageFbRoot
              ] ]) u₂ u₃ 5 ∧
              u₃.regs (Signed.left (r := 47)) = Signed.encode (G_k X) ∧
              u₃.regs rTrieKey = setMask (X.erase coord) ∧
              u₃.regs rTrieRoot = fbRoot ∧
              u₃.regs rZero = 0 ∧ u₃.regs rOne = 1 ∧ u₃.regs Reg.dim = d ∧
              u₃.regs rSignMode = signMode ∧ u₃.mem = u₂.mem := by
            wram_exec [hu₂_val, hu₂_ck, hu₂_bm, hu₂_cut, hu₂_cc, hu₂_fbr, hlt_cut]
            wram_simp [setMask_erase hcX, hu₂_z, hu₂_o, hu₂_d, hu₂_sm]
          obtain ⟨u₃, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃⟩ := hst
          refine ⟨u₃, fbRoot, fbFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, ?_,
            hfb_eq _ (by omega) ((hdom_closed X hX_mem hcX).2 (by omega))⟩
          rw [hm₃]; change HoldsTrie u₁.mem free d fbRoot fbFn; rwa [hu₁_mem]
      obtain ⟨u₃, selRoot, selFn, he₃, hl₃, hk₃, hr₃, hz₃, ho₃, hd₃, hsm₃, hm₃, htsel, hval_er⟩ :=
        hsel
      obtain ⟨u₄, he₄, hu₄_val, hu₄_mem, hu₄_regs⟩ := exec_trieGet u₃ hz₃ ho₃ hd₃ hr₃ hk₃ htsel
        (hfit_free.of_le (by omega)) hfit_d (hfit_mask.of_le (setMask_lt _).le)
      rw [hval_er] at hu₄_val
      have hu₄_left : u₄.regs (Signed.left (r := 47)) = Signed.encode (G_k X) :=
        (hu₄_regs _ (Or.inl (by decide))).trans hl₃
      have hu₄_sm : u₄.regs rSignMode = signMode :=
        (hu₄_regs _ (Or.inr (by decide))).trans hsm₃
      have hu₄_z : u₄.regs rZero = 0 :=
        (hu₄_regs _ (Or.inl (by decide))).trans hz₃
      let u₅ := u₄.set (Signed.right (r := 47)) (Signed.encode (G_k (X.erase coord)))
      have he₅ : ExecWithin (B := .standard) w (ram[ Signed.right ← rTrieVal ]) u₄ u₅ 1 := by
        wram_exec [hu₄_val]
      have harith : ∃ u₆, ExecWithin w
          (.branch (.eq rSignMode rZero) (Signed.add (r := 47)) (Signed.subtract (r := 47)))
          u₅ u₆ 19 ∧
          u₆.regs (Signed.result (r := 47)) = Signed.encode (yatesPass c coord G_k X) ∧
          u₆.mem = u₅.mem := by
        by_cases hsm0 : signMode = 0
        · have hcond : (Cond.eq rSignMode rZero).Holds u₅ := by
            simp [Cond.holds_eq, u₅, hu₄_sm, hu₄_z, hsm0]
          obtain ⟨u₆, he₆, hres₆, hmem₆, _⟩ :=
            exec_signedAdd hfit_val (hG_le X) (hG_le (X.erase coord)) u₅
              (by simp only [u₅, Data.set_regs_of_ne (by decide :
                    Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₄_left)
              (by simp [u₅])
          refine ⟨u₆, (he₆.branch_pos hcond).mono (by omega), ?_, hmem₆⟩
          simpa [yatesPass, hcX, c, hsm0] using hres₆
        · have hcond : ¬ (Cond.eq rSignMode rZero).Holds u₅ := by
            simp [Cond.holds_eq, u₅, hu₄_sm, hu₄_z, hsm0]
          obtain ⟨u₆, he₆, hres₆, hmem₆, _⟩ :=
            exec_signedSub hfit_val (hG_le X) (hG_le (X.erase coord)) u₅
              (by simp only [u₅, Data.set_regs_of_ne (by decide :
                    Signed.left (r := 47) ≠ Signed.right (r := 47))]; exact hu₄_left)
              (by simp [u₅])
          refine ⟨u₆, (he₆.branch_neg hcond).mono (by omega), ?_, hmem₆⟩
          simpa [yatesPass, hcX, c, hsm0, sub_eq_add_neg] using hres₆
      obtain ⟨u₆, he₆, hres₆, hm₆⟩ := harith
      let u := u₆.set rTrieVal (Signed.encode (yatesPass c coord G_k X))
      have he₇ : ExecWithin (B := .standard) w (ram[ rTrieVal ← Signed.result ]) u₆ u 1 := by
        wram_exec [hres₆]
      have helse : ExecWithin w
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
                  (ram[ rTrieVal ← Signed.result ])))))
          u₂ u (9 * d + 34) :=
        (he₃.seq (he₄.seq (he₅.seq (he₆.seq he₇)))).mono (by omega)
      have hbr : ExecWithin w
          (.branch (.eq rGenTmp rZero) (ram[ rTrieVal ← rTrieVal ]) _) u₂ u (9 * d + 36) :=
        (helse.branch_neg (by simpa [Cond.holds_eq] using hgt_ne)).mono (by omega)
      have htot : ExecWithin w passCellBody s u (18 * d + 47) :=
        (he₀.seq (he₁.seq (he₂.seq hbr))).mono (by omega)
      refine ⟨u, htot, by simp [u, X], hm₆.trans (hu₄_mem.trans (hm₃.trans hu₁_mem)),
        fun i hi => htot.regs_eq (passCellBody_preserves i hi)⟩
    · have hgt_eq : u₂.regs rGenTmp = u₂.regs rZero := by
        rw [hu₂_z]; simp [u₂, hand_eq, hcX]
      have hu₂_val : u₂.regs rTrieVal = Signed.encode (G_k X) := by
        simp only [u₂, Data.set_regs_of_ne (by decide : rTrieVal ≠ rGenTmp)]; exact hu₁_val
      let u := u₂.set rTrieVal (Signed.encode (G_k X))
      have hnop : ExecWithin (B := .standard) w (ram[ rTrieVal ← rTrieVal ]) u₂ u 1 := by
        wram_exec [hu₂_val]
      have htot : ExecWithin w passCellBody s u (18 * d + 47) :=
        (he₀.seq (he₁.seq (he₂.seq
          (hnop.branch_pos (by simpa [Cond.holds_eq] using hgt_eq))))).mono (by omega)
      refine ⟨u, htot, by simp [u, X, yatesPass, hcX], hu₁_mem,
        fun i hi => htot.regs_eq (passCellBody_preserves i hi)⟩
  obtain ⟨y, free', S', outFn, he, hysav, hyfree, hlo', hhi', hS', hyrep, hydom, hyframe⟩ :=
    exec_tabulateDom (cellBody := passCellBody)
      (cellFn := fun X => Signed.encode (yatesPass c coord G_k X))
      (T_cell := 18 * d + 47) x hz ho hd hdp hdl hfree hfree_pos
      hnd hdom hdom_below ⟨hbm, hcut, hsm, hcr, hfbr⟩ hInv_congr hcell hfit_free hfit_mask
  have he' : ExecWithin w passCode x y (dom.length * (32 * d + 63) + 9) :=
    he.mono (by
      have : 14 * d + (18 * d + 47) + 16 = 32 * d + 63 := by omega
      rw [this])
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
  refine ⟨S, fun a ha => ⟨(hS ha).1, (hS ha).2.trans_le hb_bound⟩, Set.disjoint_left.mpr ?_, hrep⟩
  intro a ha hexcl
  have := (hS ha).2; have := hexcl.1; omega

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
  exact ⟨by revert i hi; decide +kernel,
    by revert i hi; decide +kernel,
    passCode_preserves i (fun ht => hi (Or.inl ht)),
    by revert i hi; decide +kernel⟩

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
    dsimp only [P] at hs
    obtain ⟨hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro,
      curFree, hsfree, hcf_lo, hcf_hi, hstages, hsframe⟩ := hs
    let coord : Fin d := ⟨k, hk⟩
    let G_k := yatesTransform c ((List.finRange d).take k) G
    obtain ⟨curFn, hcur_out, hcur_eq⟩ := hstages k le_rfl
    have hcur_trie : HoldsTrie s.mem curFree d (s.mem (free + k)) curFn := hcur_out.toHoldsTrie
    have hG_k_le : ∀ Y, (G_k Y).natAbs ≤ B := fun Y =>
      (natAbs_yatesTransform_le hc_abs ((List.nodup_finRange d).sublist (List.take_sublist _ _))
        hG_le Y).trans hB
    have hf_ro_k : Fits w (free + k) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
    have hf_shl : Fits w (1 <<< k) := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos hk.le)
    have hsetup : ∃ u₀ fbRoot fbFn,
        ExecWithin (B := .standard) w (ram[
          rGenTmp ← rRootsOut + rStageIdx;
          rStageCurRoot ← *rGenTmp;
          if rStageCutoff = rZero then [
            rStageFbRoot ← #0
          ] else [
            rGenTmp ← rFbRoots + rStageIdx;
            rStageFbRoot ← *rGenTmp
          ];
          rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
        u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs Reg.dim = d ∧
        u₀.regs Reg.entryPtr = domPtr ∧ u₀.regs Reg.entryCount = dom.length ∧
        u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
        u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
        u₀.regs rStageIdx = k ∧ u₀.regs Reg.free = curFree ∧
        u₀.regs rStageCurRoot = s.mem (free + k) ∧
        u₀.regs rStageFbRoot = fbRoot ∧ u₀.regs rGenBitMask = (1 <<< coord.val) ∧
        u₀.mem = s.mem ∧ HoldsTrie s.mem curFree d fbRoot fbFn ∧
        (∀ Y, #Y < cutoff → P_low Y → fbFn (setMask Y) = Signed.encode (G_k Y)) := by
      by_cases hcut0 : cutoff = 0
      · have hst : ∃ u₀, ExecWithin (B := .standard) w (ram[
            rGenTmp ← rRootsOut + rStageIdx;
            rStageCurRoot ← *rGenTmp;
            if rStageCutoff = rZero then [
              rStageFbRoot ← #0
            ] else [
              rGenTmp ← rFbRoots + rStageIdx;
              rStageFbRoot ← *rGenTmp
            ];
            rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
            u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs Reg.dim = d ∧
            u₀.regs Reg.entryPtr = domPtr ∧ u₀.regs Reg.entryCount = dom.length ∧
            u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
            u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
            u₀.regs rStageIdx = k ∧ u₀.regs Reg.free = curFree ∧
            u₀.regs rStageCurRoot = s.mem (free + k) ∧
            u₀.regs rStageFbRoot = 0 ∧ u₀.regs rGenBitMask = (1 <<< coord.val) ∧
            u₀.mem = s.mem := by
          wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0]
          wram_simp [hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro, hk_eq, hsfree, coord]
        obtain ⟨u₀, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro, hzk, hzfr,
          hzcr, hzfbr, hzbm, hzm⟩ := hst
        refine ⟨u₀, 0, fun _ => 0, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro,
          hzk, hzfr, hzcr, hzfbr, hzbm, hzm, HoldsTrie.zero_root _ _ _, fun _ hY _ => by omega⟩
      · obtain ⟨hfbb_le, hfb_all⟩ := hfb_valid (by omega)
        obtain ⟨fbFn, hfb_tr, hfb_eq⟩ := hfb_all k hk
        have hf_fbb_k : Fits w (fbBase + k) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
        have hs_fbb_read : s.mem (fbBase + k) = x.mem (fbBase + k) :=
          hsframe _ (Or.inl (by omega))
        have hfb_tr_s : HoldsTrie s.mem curFree d (s.mem (fbBase + k)) fbFn := by
          rw [hs_fbb_read]
          exact (hfb_tr.congr_below fun a ha => hsframe a (Or.inl ha)).mono_bound
            (by dsimp [exclHi] at hcf_lo; omega)
        have hst : ∃ u₀, ExecWithin (B := .standard) w (ram[
            rGenTmp ← rRootsOut + rStageIdx;
            rStageCurRoot ← *rGenTmp;
            if rStageCutoff = rZero then [
              rStageFbRoot ← #0
            ] else [
              rGenTmp ← rFbRoots + rStageIdx;
              rStageFbRoot ← *rGenTmp
            ];
            rGenBitMask ← rOne <<< rStageIdx ]) s u₀ 8 ∧
            u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs Reg.dim = d ∧
            u₀.regs Reg.entryPtr = domPtr ∧ u₀.regs Reg.entryCount = dom.length ∧
            u₀.regs rStageCutoff = cutoff ∧ u₀.regs rSignMode = signMode ∧
            u₀.regs rFbRoots = fbBase ∧ u₀.regs rRootsOut = free ∧
            u₀.regs rStageIdx = k ∧ u₀.regs Reg.free = curFree ∧
            u₀.regs rStageCurRoot = s.mem (free + k) ∧
            u₀.regs rStageFbRoot = s.mem (fbBase + k) ∧
            u₀.regs rGenBitMask = (1 <<< coord.val) ∧ u₀.mem = s.mem := by
          wram_exec [hsz, hso, hsro, hk_eq, hscut, hcut0, hsfbb]
          wram_simp [hsz, hso, hsd, hsdp, hsdl, hscut, hssm, hsfbb, hsro, hk_eq, hsfree, coord]
        obtain ⟨u₀, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm, hzfbb, hzro, hzk, hzfr,
          hzcr, hzfbr, hzbm, hzm⟩ := hst
        exact ⟨u₀, s.mem (fbBase + k), fbFn, he₀, hzz, hzo, hzd, hzdp, hzdl, hzcut, hzsm,
          hzfbb, hzro, hzk, hzfr, hzcr, hzfbr, hzbm, hzm, hfb_tr_s, hfb_eq⟩
    obtain ⟨u₀, fbRoot, fbFn, he₀, hu₀z, hu₀o, hu₀d, hu₀dp, hu₀dl, hu₀cut, hu₀sm, hu₀fbb,
      hu₀ro, hu₀k, hu₀fr, hu₀cr, hu₀fbr, hu₀bm, hu₀mem, hfb_tr, hfb_eq⟩ := hsetup
    have hpass_fit : Fits w (curFree + 2 + 2 * d * dom.length) := by
      have : curFree + 2 + 2 * d * dom.length ≤
          free + d + 1 + d * (2 * d * dom.length + 2) := by
        calc curFree + 2 + 2 * d * dom.length
            ≤ exclHi + k * (2 * d * dom.length + 2) + (2 * d * dom.length + 2) := by omega
          _ = exclHi + (k + 1) * (2 * d * dom.length + 2) := by ring
          _ ≤ exclHi + d * (2 * d * dom.length + 2) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      exact hfit_free.of_le this
    have hdom_u₀ : HoldsDom u₀.mem domPtr dom := by
      rw [hu₀mem]
      intro p hp
      rw [hsframe _ (Or.inl (by omega)), hsframe _ (Or.inl (by omega))]
      exact hdom p hp
    obtain ⟨u₁, free', S_new, outFn, he_pass, hu₁_sav, hu₁_free, hcf_le', hfree'_le,
      hS_new, hrep_new, hout_eq, hu₁_frame, hu₁_regs⟩ :=
      exec_passCode (coord := coord) (P_low := P_low) (G_k := G_k) (B := B) u₀
        hu₀z hu₀o hu₀d hu₀dp hu₀dl hu₀fr (by dsimp [exclHi] at hcf_lo; omega)
        hu₀bm hu₀cut hu₀sm hu₀cr hu₀fbr hnd hdom_u₀ (by dsimp [exclHi] at hcf_lo; omega)
        (fun X hX hc => hdom_closed X hX coord hc)
        (by rwa [hu₀mem]) (by rwa [hu₀mem]) hcur_eq hfb_eq hG_k_le
        hfit_val hpass_fit hfit_mask
    have hu₁_k : u₁.regs rStageIdx = k :=
      (hu₁_regs rStageIdx (by decide)).trans hu₀k
    have hu₁_o : u₁.regs rOne = 1 :=
      (hu₁_regs rOne (by decide)).trans hu₀o
    have hu₁_ro : u₁.regs rRootsOut = free :=
      (hu₁_regs rRootsOut (by decide)).trans hu₀ro
    have hf_k1 : Fits w (k + 1) := hfit_d.of_le (by omega)
    have hf_ro_k1 : Fits w (free + (k + 1)) := hfit_free.of_le (by dsimp [exclHi] at *; omega)
    have hstore : ∃ z, ExecWithin (B := .standard) w (ram[
        rStageIdx ← rStageIdx + rOne;
        rGenTmp ← rRootsOut + rStageIdx;
        *rGenTmp ← Reg.builtRoot ]) u₁ z 3 ∧
        z.regs rStageIdx = k + 1 ∧
        z.mem = Function.update u₁.mem (free + (k + 1)) curFree ∧
        ∀ i : Fin numRegs, i ≠ rStageIdx ∧ i ≠ rGenTmp → z.regs i = u₁.regs i := by
      have hst : ∃ z, ExecWithin (B := .standard) w (ram[
          rStageIdx ← rStageIdx + rOne;
          rGenTmp ← rRootsOut + rStageIdx;
          *rGenTmp ← Reg.builtRoot ]) u₁ z 3 ∧
          z.regs rStageIdx = k + 1 ∧
          z.mem = Function.update u₁.mem (free + (k + 1)) curFree := by
        wram_exec [hu₁_k, hu₁_o, hu₁_ro, hu₁_sav]
        wram_simp
      obtain ⟨z, hez, hzk, hzm⟩ := hst
      refine ⟨z, hez, hzk, hzm, fun i hi => hez.regs_eq ?_⟩
      revert i hi; decide +kernel
    obtain ⟨z, he_st, hz_k, hz_mem, hz_regs⟩ := hstore
    have hstep_tot : ExecWithin w stagesStep s z (dom.length * (32 * d + 63) + 20) :=
      (he₀.seq (he_pass.seq he_st)).mono (by omega)
    have reg_z (i : Fin numRegs) (ht : ¬ IsTabMod i) (hs : i ≠ rStageIdx ∧ i ≠ rGenTmp) :
        z.regs i = u₀.regs i := (hz_regs i hs).trans (hu₁_regs i ht)
    refine ⟨z, hstep_tot, ?_, hz_k⟩
    dsimp only [P]
    refine ⟨(reg_z rZero (by decide) (by decide)).trans hu₀z,
      (reg_z rOne (by decide) (by decide)).trans hu₀o,
      (reg_z Reg.dim (by decide) (by decide)).trans hu₀d,
      (reg_z Reg.entryPtr (by decide) (by decide)).trans hu₀dp,
      (reg_z Reg.entryCount (by decide) (by decide)).trans hu₀dl,
      (reg_z rStageCutoff (by decide) (by decide)).trans hu₀cut,
      (reg_z rSignMode (by decide) (by decide)).trans hu₀sm,
      (reg_z rFbRoots (by decide) (by decide)).trans hu₀fbb,
      (reg_z rRootsOut (by decide) (by decide)).trans hu₀ro,
      free', (hz_regs Reg.free (by decide)).trans hu₁_free, by omega, ?_, ?_, ?_⟩
    · calc free' ≤ curFree + (2 * d * dom.length + 2) := by omega
        _ ≤ exclHi + k * (2 * d * dom.length + 2) + (2 * d * dom.length + 2) :=
            Nat.add_le_add_right hcf_hi _
        _ = exclHi + (k + 1) * (2 * d * dom.length + 2) := by ring
    · intro j hj
      by_cases hjk : j = k + 1
      · subst hjk
        have hroot_at : z.mem (free + (k + 1)) = curFree := by simp [hz_mem]
        rw [hroot_at]
        have hdisj_excl : Disjoint S_new (Set.Ico free exclHi) := by
          rw [Set.disjoint_left]
          intro a ha hexcl
          have := (hS_new ha).1; have := hexcl.2; omega
        have hrep_z : TrieRep z.mem d curFree S_new outFn :=
          hrep_new.congr_mem fun a ha => by
            have := (hS_new ha).1
            rw [hz_mem, Function.update_of_ne (by dsimp [exclHi] at hcf_lo; omega)]
        refine ⟨outFn, ⟨S_new, fun a ha => ⟨by
          dsimp [exclHi] at hcf_lo; have := (hS_new ha).1; omega,
          (hS_new ha).2⟩, hdisj_excl, hrep_z⟩, fun X hX => ?_⟩
        have htake1 : (List.finRange d).take (k + 1) = (List.finRange d).take k ++ [coord] := by
          rw [List.take_succ_eq_append_getElem (by simp [hk])]
          simp [coord]
        rw [htake1, yatesTransform_append, yatesTransform_cons, yatesTransform_nil]
        exact hout_eq X hX
      · obtain ⟨stFn, ⟨S_j, hSj_sub, hSj_disj, hSj_rep⟩, hst_eq⟩ := hstages j (by omega)
        have hslot_eq : z.mem (free + j) = s.mem (free + j) := by
          rw [hz_mem, Function.update_of_ne (by omega),
            hu₁_frame _ (Or.inl (by dsimp [exclHi] at hcf_lo; omega)), hu₀mem]
        rw [hslot_eq]
        have hrep_z : TrieRep z.mem d (s.mem (free + j)) S_j stFn :=
          hSj_rep.congr_mem fun a ha => by
            have ha_not_slot : a ≠ free + (k + 1) := fun h =>
              Set.disjoint_left.mp hSj_disj ha
                (by subst h; exact ⟨by omega, by dsimp [exclHi]; omega⟩)
            have ha_lt_cf : a < curFree := (hSj_sub ha).2
            rw [hz_mem, Function.update_of_ne ha_not_slot, hu₁_frame a (Or.inl ha_lt_cf), hu₀mem]
        exact ⟨stFn, ⟨S_j, fun a ha => ⟨(hSj_sub ha).1, (hSj_sub ha).2.trans_le (by omega)⟩,
          hSj_disj, hrep_z⟩, hst_eq⟩
    · intro a ha
      have ha_ne : a ≠ free + (k + 1) := by
        rcases ha with h1 | h2 <;> { dsimp [exclHi] at *; omega }
      rw [hz_mem, Function.update_of_ne ha_ne]
      rcases ha with ha_lo | ha_hi
      · rw [hu₁_frame a (Or.inl (by dsimp [exclHi] at hcf_lo; omega)), hu₀mem]
        exact hsframe a (Or.inl ha_lo)
      · rw [hu₁_frame a (Or.inr ha_hi), hu₀mem]
        exact hsframe a (Or.inr (by omega))
  have hf_d1 : Fits w (d + 1) := hfit_free.of_le (by omega)
  have hf_excl : Fits w (free + (d + 1)) := hfit_free.of_le (by omega)
  have hf_free0 : Fits w free := hfit_free.of_le (by omega)
  have hinit : ∃ s₀, ExecWithin (B := .standard) w (ram[
      rRootsOut ← Reg.free;
      rGenTmp ← Reg.dim + rOne;
      Reg.free ← Reg.free + rGenTmp;
      *rRootsOut ← rStageCurRoot;
      rStageIdx ← #0 ]) x s₀ 5 ∧
      s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧ s₀.regs Reg.dim = d ∧
      s₀.regs Reg.entryPtr = domPtr ∧ s₀.regs Reg.entryCount = dom.length ∧
      s₀.regs rStageCutoff = cutoff ∧ s₀.regs rSignMode = signMode ∧
      s₀.regs rFbRoots = fbBase ∧ s₀.regs rRootsOut = free ∧
      s₀.regs Reg.free = exclHi ∧ s₀.regs rStageIdx = 0 ∧
      s₀.mem = Function.update x.mem free initRoot := by
    wram_exec [ho, hd, hir, hfree]
    refine ⟨hz, ho, hd, hdp, hdl, hcut, hsm, hfbb, ?_, ?_, ?_, ?_⟩
    · wram_simp
    · wram_simp [exclHi]; omega
    · wram_simp
    · wram_simp
  obtain ⟨s₀, hinit_ex, hs₀z, hs₀o, hs₀d, hs₀dp, hs₀dl, hs₀cut, hs₀sm, hs₀fbb,
    hs₀ro, hs₀fr, hs₀k, hs₀mem⟩ := hinit
  have hs₀P : P (s₀.regs rStageIdx) s₀ := by
    dsimp only [P]
    rw [hs₀k]
    refine ⟨hs₀z, hs₀o, hs₀d, hs₀dp, hs₀dl, hs₀cut, hs₀sm, hs₀fbb, hs₀ro,
      exclHi, hs₀fr, le_rfl, by omega, ?_, ?_⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      simp only [Nat.add_zero, List.take_zero, yatesTransform_nil]
      have hroot0 : s₀.mem free = initRoot := by simp [hs₀mem]
      rw [hroot0]
      have ht_s₀ : HoldsTrie s₀.mem free d initRoot initFn :=
        htrie_init.congr_below fun a ha => by rw [hs₀mem, Function.update_of_ne (by omega)]
      exact ⟨initFn, ht_s₀.toOutside_of_le le_rfl (by dsimp [exclHi]; omega), hinit_eq⟩
    · intro a ha
      rw [hs₀mem, Function.update_of_ne
        (by rcases ha with h1 | h2 <;> { dsimp [exclHi] at *; omega })]
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
    (by simp [hs₀k]) hs₀P
  obtain ⟨_, _, _, _, _, _, _, _, hyro, endFree, hyfr, hlo_ef, hhi_ef, hystages, hyframe⟩ := hyP
  have htot : ExecWithin w stagesCode x y (d * (dom.length * (32 * d + 63) + 22) + 7) := by
    refine (hinit_ex.seq hloop).mono ?_
    rw [hs₀k, Nat.sub_zero]
    have h22 : dom.length * (32 * d + 63) + 20 + 2 = dom.length * (32 * d + 63) + 22 := by omega
    rw [h22]; omega
  refine ⟨y, endFree, htot, hyro, hyfr, hlo_ef, hhi_ef,
    fun k hk => let ⟨stFn, hout, heq⟩ := hystages k hk; ⟨stFn, hout.toHoldsTrie, heq⟩,
    hyframe, fun i hi => htot.regs_eq (stagesCode_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
