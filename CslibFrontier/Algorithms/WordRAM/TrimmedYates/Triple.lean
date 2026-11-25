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
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Stages
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Three-transform zeta/pointwise-product/Möbius kernel on the word RAM

Combines two trimmed zeta transforms (`f` and `g`), pointwise domain multiplication (`tabulateMul`),
and one trimmed Möbius transform into `runTransformTriple`, together with the query-loop state
invariant `QueryInv`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.tripleSpace`, `tripleTime`: workspace and instruction
  budgets for `runTransformTriple`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.IsTripleMod`: modified-register footprint of
  `runTransformTriple`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.runTransformTriple`: 3-transform convolution kernel.
* `Cslib.Algorithms.WordRAM.TrimmedYates.QueryInv`: loop invariant across queries `0 .. Cs.length`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.tripleSpace_le`, `phaseTime_le`: quadratic-in-`(d + 1)`
  space and instruction upper bounds.
* `Cslib.Algorithms.WordRAM.TrimmedYates.runTransformTriple_preserves`,
  `exec_runTransformTriple`: register frame and `ExecWithin` specification producing stage tables
  and `coveringProduct` values on the active domain.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

/-- Scratch words allocated by `runTransformTriple` on dimension `d` and domain length `L`. -/
@[expose] def tripleSpace (d L : ℕ) : ℕ :=
  3 * (d + 1 + d * (2 * d * L + 2)) + (2 + 2 * d * L)

/-- Instruction budget for `runTransformTriple` on dimension `d` and domain length `L`. -/
@[expose] def tripleTime (d L : ℕ) : ℕ :=
  3 * (d * (L * (32 * d + 63) + 22) + 7) + (L * (32 * d + 53) + 9) + 15

theorem tripleSpace_le (d L : ℕ) :
    d + 2 * L + tripleSpace d L ≤ 6 * (d + 1) ^ 2 * (L + 1) + 4 * (d + 1) ^ 2 := by
  dsimp only [tripleSpace]
  rw [sq]
  nlinarith

theorem phaseTime_le {d L : ℕ} (hL : 1 ≤ L) :
    d * (20 * L + 12) + 8 + (12 * L + 3) + (11 * d + 5) + (9 * d + 8) + tripleTime d L + 35 ≤
      180 * (d + 1) ^ 2 * L := by
  obtain ⟨Lp, rfl⟩ : ∃ Lp, L = Lp + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  dsimp only [tripleTime]
  have hid :
      (d * (20 * (Lp + 1) + 12) + 8 + (12 * (Lp + 1) + 3) + (11 * d + 5) + (9 * d + 8) +
        (3 * (d * ((Lp + 1) * (32 * d + 63) + 22) + 7) +
          ((Lp + 1) * (32 * d + 53) + 9) + 15) + 35) +
      (84 * d ^ 2 + 21 * d + 11 + Lp * (84 * d ^ 2 + 119 * d + 115)) =
      180 * (d + 1) ^ 2 * (Lp + 1) := by ring
  omega

/-- Registers potentially modified by `runTransformTriple`. -/
abbrev IsTripleMod (i : Fin numRegs) : Prop :=
  IsStageMod i ∨ i = rSignMode ∨ i = rFbRoots ∨ i = rQFsBase ∨ i = rQGsBase

/-- Run the 3 trimmed transforms (`f` with `+1`, `g` with `+1`, pointwise product `h₀ = f_d * g_d`,
and `h` with `-1`) on `dom` at `Reg.entryPtr[0 .. Reg.entryCount - 1]`. Leaves the three stage-root
base addresses in `rQFsBase`, `rQGsBase`, and `rRootsOut`. -/
def runTransformTriple : Code .standard numRegs :=
  .seq (ram[
    rStageCurRoot ← Reg.trieF;
    rFbRoots ← rPreFsBase;
    rSignMode ← #0 ])
  (.seq stagesCode
    (.seq (ram[
      rQFsBase ← rRootsOut;
      rStageCurRoot ← Reg.trieG;
      rFbRoots ← rPreGsBase;
      rSignMode ← #0 ])
    (.seq stagesCode
      (.seq (ram[
        rQGsBase ← rRootsOut;
        rGenTmp ← rQFsBase + Reg.dim;
        rStageCurRoot ← *rGenTmp;
        rGenTmp ← rQGsBase + Reg.dim;
        rStageFbRoot ← *rGenTmp ])
      (.seq tabulateMul
        (.seq (ram[
          rStageCurRoot ← Reg.builtRoot;
          rFbRoots ← rPreHsBase;
          rSignMode ← #1 ])
        stagesCode))))))

theorem runTransformTriple_preserves (i : Fin numRegs) :
    ¬ IsTripleMod i → runTransformTriple.Preserves i := by
  intro hi
  have hst : ¬ IsStageMod i := fun hs => hi (Or.inl hs)
  exact ⟨by clear hst; revert i hi; decide +kernel,
    stagesCode_preserves i hst,
    by clear hst; revert i hi; decide +kernel,
    stagesCode_preserves i hst,
    by clear hst; revert i hi; decide +kernel,
    tabulateMul_preserves i (fun ht => hst (Or.inl ht)),
    by clear hst; revert i hi; decide +kernel,
    stagesCode_preserves i hst⟩

theorem exec_runTransformTriple {w d domPtr free rootF rootG preFs preGs preHs cutoff W : ℕ}
    {dom : List (Finset (Fin d))} {P_low : Finset (Fin d) → Prop}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hdp : x.regs Reg.entryPtr = domPtr) (hdl : x.regs Reg.entryCount = dom.length)
    (hcut : x.regs rStageCutoff = cutoff)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hpFs : x.regs rPreFsBase = preFs) (hpGs : x.regs rPreGsBase = preGs)
    (hpHs : x.regs rPreHsBase = preHs)
    (hfree : x.regs Reg.free = free) (hfree_pos : 1 ≤ free)
    (hnd : dom.Nodup) (hdom : HoldsDom x.mem domPtr dom)
    (hdom_below : domPtr + 2 * dom.length ≤ free)
    (hdom_closed : ∀ X ∈ dom, ∀ coord : Fin d, coord ∈ X →
      (cutoff ≤ #(X.erase coord) → X.erase coord ∈ dom) ∧
      (#(X.erase coord) < cutoff → P_low (X.erase coord)))
    (htrieF : HoldsTrie x.mem free d rootF fnF)
    (htrieG : HoldsTrie x.mem free d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hfb_valid : 0 < cutoff →
      preFs + d ≤ free ∧ preGs + d ≤ free ∧ preHs + d ≤ free ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preFs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y)) ∧
      (∀ k < d, ∃ fbFn, HoldsTrie x.mem free d (x.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) = Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k)
            (fun S => subsetZeta f S * subsetZeta g S) Y)))
    (hfit_val : Fits w (valueEnvelope d W))
    (hfit_free : Fits w (free + tripleSpace d dom.length)) :
    let H : Finset (Fin d) → ℤ := fun S => subsetZeta f S * subsetZeta g S
    ∃ y fsBase gsBase hsBase endFree,
      ExecWithin w runTransformTriple x y (tripleTime d dom.length) ∧
      y.regs rQFsBase = fsBase ∧ y.regs rQGsBase = gsBase ∧
      y.regs rRootsOut = hsBase ∧ y.regs Reg.free = endFree ∧
      free ≤ endFree ∧ endFree ≤ free + tripleSpace d dom.length ∧
      fsBase + d < endFree ∧ gsBase + d < endFree ∧ hsBase + d < endFree ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (fsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) f X)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (gsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g X)) ∧
      (∀ k ≤ d, ∃ stFn, HoldsTrie y.mem endFree d (y.mem (hsBase + k)) stFn ∧
        ∀ X ∈ dom, stFn (setMask X) =
          Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k) H X)) ∧
      (∃ outFn, HoldsTrie y.mem endFree d (y.mem (hsBase + d)) outFn ∧
        ∀ X ∈ dom, outFn (setMask X) = Signed.encode (coveringProduct f g X)) ∧
      (∀ a, a < free ∨ endFree ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, ¬ IsTripleMod i → y.regs i = x.regs i := by
  intro H
  let B := 8 ^ d * (W + 1) ^ 2
  have hfit_B : Fits w (8 * B + 4) := hfit_val
  have hfit_mask : Fits w (2 ^ d) := mask_fits_of_valueEnvelope hfit_val
  have hB_fg : 2 ^ d * W ≤ B := by
    dsimp only [B]
    have h28 : 2 ^ d ≤ 8 ^ d := Nat.pow_le_pow_left (by decide) d
    have hW : W ≤ (W + 1) ^ 2 := by rw [sq]; nlinarith
    exact Nat.mul_le_mul h28 hW
  have hH_le : ∀ S, (H S).natAbs ≤ 4 ^ d * W ^ 2 := by
    intro S
    dsimp only [H]
    have hzf : subsetZeta f S = yatesTransform (1 : ℤ) (List.finRange d) f S := by
      rw [← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) f (by intro i _; simp)]
    have hzg : subsetZeta g S = yatesTransform (1 : ℤ) (List.finRange d) g S := by
      rw [← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) g (by intro i _; simp)]
    have h1 : (subsetZeta f S).natAbs ≤ 2 ^ d * W := by
      rw [hzf]; exact natAbs_yatesTransform_le (by decide) (List.nodup_finRange d) hf_le S
    have h2 : (subsetZeta g S).natAbs ≤ 2 ^ d * W := by
      rw [hzg]; exact natAbs_yatesTransform_le (by decide) (List.nodup_finRange d) hg_le S
    rw [Int.natAbs_mul]
    calc (subsetZeta f S).natAbs * (subsetZeta g S).natAbs
        ≤ (2 ^ d * W) * (2 ^ d * W) := Nat.mul_le_mul h1 h2
      _ = (2 * 2) ^ d * W ^ 2 := by rw [Nat.mul_pow]; ring
      _ = 4 ^ d * W ^ 2 := rfl
  have hB_H : 2 ^ d * (4 ^ d * W ^ 2) ≤ B := by
    dsimp only [B]
    have h248 : 2 ^ d * 4 ^ d = 8 ^ d := by rw [← Nat.mul_pow]
    calc 2 ^ d * (4 ^ d * W ^ 2) = (2 ^ d * 4 ^ d) * W ^ 2 := by ring
      _ = 8 ^ d * W ^ 2 := by rw [h248]
      _ ≤ 8 ^ d * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  -- Phase 1: f stages
  let u₀ := ((x.set rStageCurRoot rootF).set rFbRoots preFs).set rSignMode 0
  have he₀ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← Reg.trieF; rFbRoots ← rPreFsBase; rSignMode ← #0 ]) x u₀ 3 := by
    wram_exec [htF_reg, hpFs]
  obtain ⟨u₁, free₁, he_stF, hu₁_ro, hu₁_free, hlo₁, hhi₁, hstF, hfr₁, hreg₁⟩ :=
    exec_stagesCode (initRoot := rootF) (fbBase := preFs) (signMode := 0)
      (P_low := P_low) (G := f) (B₀ := W) (B := B) u₀
      (by simp [u₀, hz]) (by simp [u₀, ho]) (by simp [u₀, hd])
      (by simp [u₀, hdp]) (by simp [u₀, hdl])
      (by simp [u₀, hcut]) (by simp [u₀]) (by simp [u₀])
      (by simp [u₀]) (by simp [u₀, hfree]) hfree_pos
      hnd hdom hdom_below hdom_closed htrieF (fun X _ => hf_eq X)
      (fun hpos => ⟨(hfb_valid hpos).1, (hfb_valid hpos).2.2.2.1⟩)
      hf_le hB_fg hfit_B (hfit_free.of_le (by dsimp [tripleSpace]; omega)) hfit_mask
  -- Phase 2: g stages
  have hu₁_tG : u₁.regs Reg.trieG = rootG := by
    rw [hreg₁ Reg.trieG (by decide)]; simp [u₀, htG_reg]
  have hu₁_pGs : u₁.regs rPreGsBase = preGs := by
    rw [hreg₁ rPreGsBase (by decide)]; simp [u₀, hpGs]
  let u₂ := (((u₁.set rQFsBase free).set rStageCurRoot rootG).set rFbRoots preGs).set rSignMode 0
  have he₂ : ExecWithin (B := .standard) w (ram[
      rQFsBase ← rRootsOut;
      rStageCurRoot ← Reg.trieG;
      rFbRoots ← rPreGsBase;
      rSignMode ← #0 ]) u₁ u₂ 4 := by
    wram_exec [hu₁_ro, hu₁_tG, hu₁_pGs]
  have hdom_u₂ : HoldsDom u₂.mem domPtr dom := by
    intro p hp
    change u₁.mem _ = _ ∧ u₁.mem _ = _
    rw [hfr₁ _ (Or.inl (by omega)), hfr₁ _ (Or.inl (by omega))]
    exact hdom p hp
  have htrieG_u₂ : HoldsTrie u₂.mem free₁ d rootG fnG :=
    (htrieG.congr_below fun a ha => hfr₁ a (Or.inl ha)).mono_bound (by omega)
  have hfbG_u₂ : 0 < cutoff → preGs + d ≤ free₁ ∧
      ∀ k < d, ∃ fbFn, HoldsTrie u₂.mem free₁ d (u₂.mem (preGs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (1 : ℤ) ((List.finRange d).take k) g Y) := by
    intro hpos
    obtain ⟨_, hpg_le, _, _, hfbG, _⟩ := hfb_valid hpos
    refine ⟨by omega, fun k hk => ?_⟩
    obtain ⟨fbFn, htr, heq⟩ := hfbG k hk
    have hm_eq : u₂.mem (preGs + k) = x.mem (preGs + k) := hfr₁ _ (Or.inl (by omega))
    rw [hm_eq]
    exact ⟨fbFn, (htr.congr_below fun a ha => hfr₁ a (Or.inl ha)).mono_bound (by omega), heq⟩
  have keep_u₀_u₁ (i : Fin numRegs) (h1 : ¬ IsStageMod i)
      (h0 : i ≠ rStageCurRoot ∧ i ≠ rFbRoots ∧ i ≠ rSignMode) : u₁.regs i = x.regs i := by
    rw [hreg₁ i h1]
    simp [u₀, Data.set_regs_of_ne h0.1, Data.set_regs_of_ne h0.2.1, Data.set_regs_of_ne h0.2.2]
  obtain ⟨u₃, free₂, he_stG, hu₃_ro, hu₃_free, hlo₂, hhi₂, hstG, hfr₂, hreg₃⟩ :=
    exec_stagesCode (initRoot := rootG) (fbBase := preGs) (signMode := 0)
      (P_low := P_low) (G := g) (B₀ := W) (B := B) u₂
      (by simpa [u₂] using (keep_u₀_u₁ rZero (by decide) (by decide)).trans hz)
      (by simpa [u₂] using (keep_u₀_u₁ rOne (by decide) (by decide)).trans ho)
      (by simpa [u₂] using (keep_u₀_u₁ Reg.dim (by decide) (by decide)).trans hd)
      (by simpa [u₂] using (keep_u₀_u₁ Reg.entryPtr (by decide) (by decide)).trans hdp)
      (by simpa [u₂] using (keep_u₀_u₁ Reg.entryCount (by decide) (by decide)).trans hdl)
      (by simpa [u₂] using (keep_u₀_u₁ rStageCutoff (by decide) (by decide)).trans hcut)
      (by simp [u₂]) (by simp [u₂]) (by simp [u₂])
      (by simp [u₂, hu₁_free]) (by omega)
      hnd hdom_u₂ (by omega) hdom_closed htrieG_u₂ (fun X _ => hg_eq X)
      hfbG_u₂ hg_le hB_fg hfit_B (hfit_free.of_le (by dsimp [tripleSpace]; omega)) hfit_mask
  -- Phase 3: tabulateMul on stage d of f and g
  have hu₃_qFs : u₃.regs rQFsBase = free := by
    rw [hreg₃ rQFsBase (by decide)]; simp [u₂]
  have hu₃_d : u₃.regs Reg.dim = d := by
    rw [hreg₃ Reg.dim (by decide)]
    simpa [u₂] using (keep_u₀_u₁ Reg.dim (by decide) (by decide)).trans hd
  have hf_f0_d : Fits w (free + d) := hfit_free.of_le (by dsimp [tripleSpace]; omega)
  have hf_f1_d : Fits w (free₁ + d) := hfit_free.of_le (by dsimp [tripleSpace] at *; omega)
  have hprep_mul : ∃ u₄, ExecWithin (B := .standard) w (ram[
      rQGsBase ← rRootsOut;
      rGenTmp ← rQFsBase + Reg.dim;
      rStageCurRoot ← *rGenTmp;
      rGenTmp ← rQGsBase + Reg.dim;
      rStageFbRoot ← *rGenTmp ]) u₃ u₄ 5 ∧
      u₄.regs rQGsBase = free₁ ∧
      u₄.regs rStageCurRoot = u₃.mem (free + d) ∧
      u₄.regs rStageFbRoot = u₃.mem (free₁ + d) ∧
      u₄.mem = u₃.mem ∧
      ∀ i : Fin numRegs, i ≠ rQGsBase ∧ i ≠ rGenTmp ∧ i ≠ rStageCurRoot ∧ i ≠ rStageFbRoot →
        u₄.regs i = u₃.regs i := by
    have hst : ∃ u₄, ExecWithin (B := .standard) w (ram[
        rQGsBase ← rRootsOut;
        rGenTmp ← rQFsBase + Reg.dim;
        rStageCurRoot ← *rGenTmp;
        rGenTmp ← rQGsBase + Reg.dim;
        rStageFbRoot ← *rGenTmp ]) u₃ u₄ 5 ∧
        u₄.regs rQGsBase = free₁ ∧
        u₄.regs rStageCurRoot = u₃.mem (free + d) ∧
        u₄.regs rStageFbRoot = u₃.mem (free₁ + d) ∧ u₄.mem = u₃.mem := by
      wram_exec [hu₃_ro, hu₃_qFs, hu₃_d]
      wram_simp
    obtain ⟨u₄, he₄, hqg, hcr, hfbr, hm⟩ := hst
    refine ⟨u₄, he₄, hqg, hcr, hfbr, hm, fun i hi => he₄.regs_eq ?_⟩
    revert i hi; decide +kernel
  obtain ⟨u₄, he₄, hu₄_qGs, hu₄_cr, hu₄_fbr, hu₄_mem, hreg₄⟩ := hprep_mul
  obtain ⟨stFnF_d, htrF_d, heqF_d⟩ := hstF d le_rfl
  obtain ⟨stFnG_d, htrG_d, heqG_d⟩ := hstG d le_rfl
  have hm_f_d : u₃.mem (free + d) = u₁.mem (free + d) := hfr₂ _ (Or.inl (by omega))
  have htrF_d_u₄ : HoldsTrie u₄.mem free₂ d (u₃.mem (free + d)) stFnF_d := by
    rw [hu₄_mem, hm_f_d]
    exact (htrF_d.congr_below fun a ha => hfr₂ a (Or.inl ha)).mono_bound (by omega)
  have htrG_d_u₄ : HoldsTrie u₄.mem free₂ d (u₃.mem (free₁ + d)) stFnG_d := by
    rwa [hu₄_mem]
  have hzetaF_eq : ∀ X ∈ dom, stFnF_d (setMask X) = Signed.encode (subsetZeta f X) ∧
      (subsetZeta f X).natAbs ≤ B := by
    intro X hX
    have htake : (List.finRange d).take d = List.finRange d := by simp
    have hzf : yatesTransform (1 : ℤ) ((List.finRange d).take d) f X = subsetZeta f X := by
      rw [htake, ← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) f (by intro i _; simp)]
    refine ⟨by rw [heqF_d X hX]; simp only [↓reduceIte, hzf], ?_⟩
    rw [← hzf]
    exact (natAbs_yatesTransform_le (by decide)
      ((List.nodup_finRange d).sublist (List.take_sublist _ _)) hf_le X).trans hB_fg
  have hzetaG_eq : ∀ X ∈ dom, stFnG_d (setMask X) = Signed.encode (subsetZeta g X) ∧
      (subsetZeta g X).natAbs ≤ B := by
    intro X hX
    have htake : (List.finRange d).take d = List.finRange d := by simp
    have hzg : yatesTransform (1 : ℤ) ((List.finRange d).take d) g X = subsetZeta g X := by
      rw [htake, ← yatesTransform_natOne_eq_intOne,
        yatesTransform_one_apply (List.nodup_finRange d) g (by intro i _; simp)]
    refine ⟨by rw [heqG_d X hX]; simp only [↓reduceIte, hzg], ?_⟩
    rw [← hzg]
    exact (natAbs_yatesTransform_le (by decide)
      ((List.nodup_finRange d).sublist (List.take_sublist _ _)) hg_le X).trans hB_fg
  have hdom_u₄ : HoldsDom u₄.mem domPtr dom := by
    rw [hu₄_mem]
    intro p hp
    rw [hfr₂ _ (Or.inl (by omega)), hfr₂ _ (Or.inl (by omega))]
    exact hdom_u₂ p hp
  have keep_u₃_x (i : Fin numRegs) (h1 : ¬ IsStageMod i)
      (h0 : i ≠ rStageCurRoot ∧ i ≠ rFbRoots ∧ i ≠ rSignMode ∧ i ≠ rQFsBase) :
      u₃.regs i = x.regs i := by
    rw [hreg₃ i h1]
    simp only [u₂, Data.set_regs_of_ne h0.2.2.1, Data.set_regs_of_ne h0.2.1,
      Data.set_regs_of_ne h0.1, Data.set_regs_of_ne h0.2.2.2]
    exact keep_u₀_u₁ i h1 ⟨h0.1, h0.2.1, h0.2.2.1⟩
  obtain ⟨u₅, free₃, h0Fn, he_mul, hu₅_sav, hu₅_free, hlo₃, hhi₃, htr_h0, heq_h0,
    hfr₃, hreg₅⟩ :=
    exec_tabulateMul (valF := subsetZeta f) (valG := subsetZeta g) (B := B) u₄
      ((hreg₄ rZero (by decide)).trans ((keep_u₃_x rZero (by decide) (by decide)).trans hz))
      ((hreg₄ rOne (by decide)).trans ((keep_u₃_x rOne (by decide) (by decide)).trans ho))
      ((hreg₄ Reg.dim (by decide)).trans hu₃_d)
      ((hreg₄ Reg.entryPtr (by decide)).trans
        ((keep_u₃_x Reg.entryPtr (by decide) (by decide)).trans hdp))
      ((hreg₄ Reg.entryCount (by decide)).trans
        ((keep_u₃_x Reg.entryCount (by decide) (by decide)).trans hdl))
      ((hreg₄ Reg.free (by decide)).trans hu₃_free) (by omega)
      hu₄_cr hu₄_fbr hnd hdom_u₄ (by omega) htrF_d_u₄ htrG_d_u₄
      hzetaF_eq hzetaG_eq
      (fun X _ => (hH_le X).trans (le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)) hB_H))
      hfit_B (hfit_free.of_le (by dsimp [tripleSpace] at *; omega)) hfit_mask
  -- Phase 4: H stages with signMode = 1 (-1)
  have hu₅_pHs : u₅.regs rPreHsBase = preHs := by
    rw [hreg₅ rPreHsBase (by decide), hreg₄ rPreHsBase (by decide)]
    exact (keep_u₃_x rPreHsBase (by decide) (by decide)).trans hpHs
  let u₆ := ((u₅.set rStageCurRoot free₂).set rFbRoots preHs).set rSignMode 1
  have he₆ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← Reg.builtRoot; rFbRoots ← rPreHsBase; rSignMode ← #1 ]) u₅ u₆ 3 := by
    wram_exec [hu₅_sav, hu₅_pHs]
  have below_u₅_x : ∀ a < free, u₅.mem a = x.mem a := fun a ha => by
    rw [hfr₃ a (Or.inl (by omega)), hu₄_mem, hfr₂ a (Or.inl (by omega))]
    change u₁.mem a = x.mem a
    rw [hfr₁ a (Or.inl ha)]
    rfl
  have hdom_u₆ : HoldsDom u₆.mem domPtr dom := by
    intro p hp
    change u₅.mem _ = _ ∧ u₅.mem _ = _
    rw [below_u₅_x _ (by omega), below_u₅_x _ (by omega)]
    exact hdom p hp
  have hfbH_u₆ : 0 < cutoff → preHs + d ≤ free₃ ∧
      ∀ k < d, ∃ fbFn, HoldsTrie u₆.mem free₃ d (u₆.mem (preHs + k)) fbFn ∧
        ∀ Y, #Y < cutoff → P_low Y →
          fbFn (setMask Y) =
            Signed.encode (yatesTransform (-1 : ℤ) ((List.finRange d).take k) H Y) := by
    intro hpos
    obtain ⟨_, _, hph_le, _, _, hfbH⟩ := hfb_valid hpos
    refine ⟨by omega, fun k hk => ?_⟩
    obtain ⟨fbFn, htr, heq⟩ := hfbH k hk
    have hm_eq : u₆.mem (preHs + k) = x.mem (preHs + k) := below_u₅_x _ (by omega)
    rw [hm_eq]
    exact ⟨fbFn, (htr.congr_below below_u₅_x).mono_bound (by omega), heq⟩
  have keep_u₅ (i : Fin numRegs) (ht : ¬ IsTabMod i)
      (h4 : i ≠ rQGsBase ∧ i ≠ rGenTmp ∧ i ≠ rStageCurRoot ∧ i ≠ rStageFbRoot) :
      u₅.regs i = u₃.regs i :=
    (hreg₅ i ht).trans (hreg₄ i h4)
  have hu₆_z : u₆.regs rZero = 0 := by
    simpa [u₆] using (keep_u₅ rZero (by decide) (by decide)).trans
      ((keep_u₃_x rZero (by decide) (by decide)).trans hz)
  have hu₆_o : u₆.regs rOne = 1 := by
    simpa [u₆] using (keep_u₅ rOne (by decide) (by decide)).trans
      ((keep_u₃_x rOne (by decide) (by decide)).trans ho)
  have hu₆_d : u₆.regs Reg.dim = d := by
    simpa [u₆] using (keep_u₅ Reg.dim (by decide) (by decide)).trans hu₃_d
  have hu₆_dp : u₆.regs Reg.entryPtr = domPtr := by
    simpa [u₆] using (keep_u₅ Reg.entryPtr (by decide) (by decide)).trans
      ((keep_u₃_x Reg.entryPtr (by decide) (by decide)).trans hdp)
  have hu₆_dl : u₆.regs Reg.entryCount = dom.length := by
    simpa [u₆] using (keep_u₅ Reg.entryCount (by decide) (by decide)).trans
      ((keep_u₃_x Reg.entryCount (by decide) (by decide)).trans hdl)
  have hu₆_cut : u₆.regs rStageCutoff = cutoff := by
    simpa [u₆] using (keep_u₅ rStageCutoff (by decide) (by decide)).trans
      ((keep_u₃_x rStageCutoff (by decide) (by decide)).trans hcut)
  obtain ⟨y, endFree, he_stH, hy_ro, hy_free, hlo₄, hhi₄, hstH, hfr₄, hreg_y⟩ :=
    exec_stagesCode (initRoot := free₂) (fbBase := preHs) (signMode := 1)
      (P_low := P_low) (G := H) (B₀ := 4 ^ d * W ^ 2) (B := B) u₆
      hu₆_z hu₆_o hu₆_d hu₆_dp hu₆_dl hu₆_cut
      (by simp [u₆]) (by simp [u₆]) (by simp [u₆])
      (by simp [u₆, hu₅_free]) (by omega)
      hnd hdom_u₆ (by omega) hdom_closed htr_h0 heq_h0 hfbH_u₆
      hH_le hB_H hfit_B (hfit_free.of_le (by dsimp [tripleSpace] at *; omega)) hfit_mask
  have htot : ExecWithin w runTransformTriple x y (tripleTime d dom.length) :=
    (he₀.seq (he_stF.seq (he₂.seq (he_stG.seq (he₄.seq (he_mul.seq (he₆.seq he_stH))))))).mono
      (by dsimp [tripleTime]; omega)
  have hy_qFs : y.regs rQFsBase = free := by
    rw [hreg_y rQFsBase (by decide)]
    simpa [u₆] using (keep_u₅ rQFsBase (by decide) (by decide)).trans hu₃_qFs
  have hy_qGs : y.regs rQGsBase = free₁ := by
    rw [hreg_y rQGsBase (by decide)]
    simpa [u₆] using (hreg₅ rQGsBase (by decide)).trans hu₄_qGs
  have y_eq_u₃ : ∀ a < free₂, y.mem a = u₃.mem a := fun a ha => by
    rw [hfr₄ a (Or.inl (by omega))]
    change u₅.mem a = u₃.mem a
    rw [hfr₃ a (Or.inl ha), hu₄_mem]
  have y_eq_u₁ : ∀ a < free₁, y.mem a = u₁.mem a := fun a ha => by
    rw [y_eq_u₃ a (by omega), hfr₂ a (Or.inl ha)]
    rfl
  refine ⟨y, free, free₁, free₃, endFree, htot, hy_qFs, hy_qGs, hy_ro, hy_free,
    by omega, by dsimp [tripleSpace]; omega, by omega, by omega, by omega,
    ?_, ?_, hstH, ?_, ?_, fun i hi => htot.regs_eq (runTransformTriple_preserves i hi)⟩
  · intro k hk
    obtain ⟨stFn, htr, heq⟩ := hstF k hk
    rw [y_eq_u₁ (free + k) (by omega)]
    exact ⟨stFn, (htr.congr_below fun a ha => y_eq_u₁ a ha).mono_bound (by omega), heq⟩
  · intro k hk
    obtain ⟨stFn, htr, heq⟩ := hstG k hk
    rw [y_eq_u₃ (free₁ + k) (by omega)]
    exact ⟨stFn, (htr.congr_below fun a ha => y_eq_u₃ a ha).mono_bound (by omega), heq⟩
  · obtain ⟨outFn, htr, heq⟩ := hstH d le_rfl
    refine ⟨outFn, htr, fun X hX => ?_⟩
    rw [heq X hX]
    congr 1
    have htake : (List.finRange d).take d = List.finRange d := by simp
    simp only [one_ne_zero, ↓reduceIte]
    rw [htake, yatesTransform_neg_one_apply (List.nodup_finRange d) H (by intro i _; simp),
      coveringProduct_eq_subsetMobius]
  · intro a ha
    rcases ha with ha_lo | ha_hi
    · rw [y_eq_u₁ a (by omega), hfr₁ a (Or.inl ha_lo)]
      rfl
    · rw [hfr₄ a (Or.inr ha_hi)]
      change u₅.mem a = x.mem a
      rw [hfr₃ a (Or.inr (by omega)), hu₄_mem, hfr₂ a (Or.inr (by omega))]
      change u₁.mem a = x.mem a
      rw [hfr₁ a (Or.inr (by omega))]
      rfl

/-- Loop invariant across queries `q ∈ [0, Cs.length]` in `solveFromTries`. -/
@[expose] def QueryInv {d : ℕ} (s outBase rootF rootG qPtr preFs preGs preHs : ℕ)
    (f g : Finset (Fin d) → ℤ) (Cs : List (Finset (Fin d))) (preMem : ℕ → ℕ)
    (q : ℕ) (st : Data numRegs) : Prop :=
  st.regs rZero = 0 ∧ st.regs rOne = 1 ∧ st.regs Reg.dim = d ∧ st.regs Reg.thresh = s ∧
  st.regs Reg.outPtr = outBase ∧ st.regs rPreFree = outBase + 1 + Cs.length ∧
  st.regs Reg.trieF = rootF ∧ st.regs Reg.trieG = rootG ∧
  st.regs Reg.queryPtr = qPtr ∧ st.regs Reg.queryCount = Cs.length ∧
  st.regs rPreFsBase = preFs ∧ st.regs rPreGsBase = preGs ∧ st.regs rPreHsBase = preHs ∧
  (∀ a < outBase, st.mem a = preMem a) ∧
  st.mem outBase = Cs.length ∧
  (∀ j (hj : j < Cs.length), j < q →
    st.mem (outBase + 1 + j) = Signed.encode (coveringProduct f g Cs[j]))

end Cslib.Algorithms.WordRAM.TrimmedYates
