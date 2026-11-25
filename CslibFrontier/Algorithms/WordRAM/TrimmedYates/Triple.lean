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
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

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
  dsimp only [tripleTime]
  nlinarith [Nat.mul_le_mul_left d hL, Nat.mul_le_mul_left (d ^ 2) hL]

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
  refine ⟨?_, stagesCode_preserves i hst, ?_, stagesCode_preserves i hst, ?_,
    tabulateMul_preserves i (fun ht => hst (Or.inl ht)), ?_, stagesCode_preserves i hst⟩ <;>
    clear hst <;> revert i hi <;> decide +kernel

/-- Trie tables stored at `pre + k` below `lo` survive any change of memory at or above `lo`. -/
private theorem tables_transport {d lo hi pre : ℕ} {m m' : ℕ → ℕ} {K : ℕ → Prop}
    {Q : ℕ → (ℕ → ℕ) → Prop} (hm : ∀ a < lo, m' a = m a) (hhi : lo ≤ hi)
    (hK : ∀ k, K k → pre + k < lo)
    (h : ∀ k, K k → ∃ fn, HoldsTrie m lo d (m (pre + k)) fn ∧ Q k fn) :
    ∀ k, K k → ∃ fn, HoldsTrie m' hi d (m' (pre + k)) fn ∧ Q k fn := fun k hk => by
  obtain ⟨fn, htr, hq⟩ := h k hk
  exact ⟨fn, by rw [hm _ (hK k hk)]; exact (htr.congr_below hm).mono_bound hhi, hq⟩

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
  have hB_fg : 2 ^ d * W ≤ B := Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) d) (by nlinarith)
  have hzeta (G : Finset (Fin d) → ℤ) :
      yatesTransform (1 : ℤ) (List.finRange d) G = subsetZeta G := by
    rw [← yatesTransform_natOne_eq_intOne,
      yatesTransform_one_eq_subsetZeta (List.nodup_finRange d) List.mem_finRange]
  have hzeta_le {G : Finset (Fin d) → ℤ} (hG : ∀ S, (G S).natAbs ≤ W) (S : Finset (Fin d)) :
      (subsetZeta G S).natAbs ≤ 2 ^ d * W := by
    rw [← hzeta]; exact natAbs_yatesTransform_le (by decide) (List.nodup_finRange d) hG S
  have hH_le : ∀ S, (H S).natAbs ≤ 4 ^ d * W ^ 2 := fun S => by
    rw [Int.natAbs_mul, show 4 ^ d * W ^ 2 = 2 ^ d * W * (2 ^ d * W) by
      rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_pow]; ring]
    exact Nat.mul_le_mul (hzeta_le hf_le S) (hzeta_le hg_le S)
  have hB_H : 2 ^ d * (4 ^ d * W ^ 2) ≤ B := by
    rw [← mul_assoc, ← Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have htake : (List.finRange d).take d = List.finRange d := by simp
  have hzeta_d {G : Finset (Fin d) → ℤ} {fn : ℕ → ℕ} (hG : ∀ S, (G S).natAbs ≤ W)
      (h : ∀ X ∈ dom, fn (setMask X) = Signed.encode
        (yatesTransform (if (0 : ℕ) = 0 then (1 : ℤ) else -1) ((List.finRange d).take d) G X)) :
      ∀ X ∈ dom, fn (setMask X) = Signed.encode (subsetZeta G X) ∧ (subsetZeta G X).natAbs ≤ B :=
    fun X hX => ⟨by simp only [h X hX, ↓reduceIte, htake, hzeta], (hzeta_le hG X).trans hB_fg⟩
  have hdom_of {m : ℕ → ℕ} (hm : ∀ a < free, m a = x.mem a) : HoldsDom m domPtr dom :=
    fun p hp => by rw [hm _ (by omega), hm _ (by omega)]; exact hdom p hp
  dsimp only [tripleSpace] at hfit_free
  -- Phase 1: the stages of `f`
  let u₀ := ((x.set rStageCurRoot rootF).set rFbRoots preFs).set rSignMode 0
  have he₀ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← Reg.trieF; rFbRoots ← rPreFsBase; rSignMode ← #0 ]) x u₀ 3 := by
    wram_exec [htF_reg, hpFs]
  obtain ⟨u₁, free₁, he_stF, hu₁_ro, hu₁_free, hlo₁, hhi₁, hstF, hfr₁, hreg₁⟩ :=
    exec_stagesCode (initRoot := rootF) (fbBase := preFs) (signMode := 0)
      (P_low := P_low) (G := f) (B₀ := W) (B := B) u₀
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) hfree_pos
      hnd hdom hdom_below hdom_closed htrieF (fun X _ => hf_eq X)
      (fun hpos => ⟨(hfb_valid hpos).1, (hfb_valid hpos).2.2.2.1⟩)
      hf_le hB_fg hfit_B (hfit_free.of_le (by omega)) hfit_mask
  -- Phase 2: the stages of `g`
  let u₂ := (((u₁.set rQFsBase free).set rStageCurRoot rootG).set rFbRoots preGs).set rSignMode 0
  have he₂ : ExecWithin (B := .standard) w (ram[
      rQFsBase ← rRootsOut;
      rStageCurRoot ← Reg.trieG;
      rFbRoots ← rPreGsBase;
      rSignMode ← #0 ]) u₁ u₂ 4 := by
    wram_exec [hu₁_ro, show u₁.regs Reg.trieG = rootG by regs_frame,
      show u₁.regs rPreGsBase = preGs by regs_frame]
  have below₂ : ∀ a < free, u₂.mem a = x.mem a := fun a ha => hfr₁ a (Or.inl ha)
  obtain ⟨u₃, free₂, he_stG, hu₃_ro, hu₃_free, hlo₂, hhi₂, hstG, hfr₂, hreg₃⟩ :=
    exec_stagesCode (initRoot := rootG) (fbBase := preGs) (signMode := 0)
      (P_low := P_low) (G := g) (B₀ := W) (B := B) u₂
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by omega)
      hnd (hdom_of below₂) (by omega) hdom_closed
      ((htrieG.congr_below below₂).mono_bound (by omega)) (fun X _ => hg_eq X)
      (fun hpos => by
        obtain ⟨-, hpg, -, -, hfbG, -⟩ := hfb_valid hpos
        exact ⟨by omega, tables_transport below₂ (by omega) (fun k hk => by omega) hfbG⟩)
      hg_le hB_fg hfit_B (hfit_free.of_le (by omega)) hfit_mask
  -- Phase 3: `tabulateMul` on stage `d` of `f` and `g`
  have hf_f0_d : Fits w (free + d) := hfit_free.of_le (by omega)
  have hf_f1_d : Fits w (free₁ + d) := hfit_free.of_le (by omega)
  obtain ⟨u₄, he₄, hu₄_qGs, hu₄_cr, hu₄_fbr, hu₄_mem⟩ : ∃ u₄, ExecWithin (B := .standard) w (ram[
      rQGsBase ← rRootsOut;
      rGenTmp ← rQFsBase + Reg.dim;
      rStageCurRoot ← *rGenTmp;
      rGenTmp ← rQGsBase + Reg.dim;
      rStageFbRoot ← *rGenTmp ]) u₃ u₄ 5 ∧
      u₄.regs rQGsBase = free₁ ∧ u₄.regs rStageCurRoot = u₄.mem (free + d) ∧
      u₄.regs rStageFbRoot = u₄.mem (free₁ + d) ∧ u₄.mem = u₃.mem := by
    wram_exec [hu₃_ro, show u₃.regs rQFsBase = free by regs_frame,
      show u₃.regs Reg.dim = d by regs_frame]
    wram_simp
  have below₄ : ∀ a < free₁, u₄.mem a = u₁.mem a := fun a ha => by
    rw [hu₄_mem, hfr₂ a (Or.inl ha)]; rfl
  obtain ⟨stFnF_d, htrF_d, heqF_d⟩ :=
    tables_transport (hi := free₂) below₄ (by omega) (fun k hk => by omega) hstF d le_rfl
  obtain ⟨stFnG_d, htrG_d, heqG_d⟩ := hstG d le_rfl
  obtain ⟨u₅, free₃, h0Fn, he_mul, hu₅_sav, hu₅_free, hlo₃, hhi₃, htr_h0, heq_h0, hfr₃, hreg₅⟩ :=
    exec_tabulateMul (valF := subsetZeta f) (valG := subsetZeta g) (B := B) u₄
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by omega) hu₄_cr hu₄_fbr hnd
      (hdom_of fun a ha => (below₄ a (by omega)).trans (hfr₁ a (Or.inl ha))) (by omega)
      htrF_d (by rwa [hu₄_mem]) (hzeta_d hf_le heqF_d) (hzeta_d hg_le heqG_d)
      (fun X _ => (hH_le X).trans (le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)) hB_H))
      hfit_B (hfit_free.of_le (by omega)) hfit_mask
  -- Phase 4: the stages of `H` with `signMode = 1` (coefficient `-1`)
  let u₆ := ((u₅.set rStageCurRoot free₂).set rFbRoots preHs).set rSignMode 1
  have he₆ : ExecWithin (B := .standard) w
      (ram[ rStageCurRoot ← Reg.builtRoot; rFbRoots ← rPreHsBase; rSignMode ← #1 ]) u₅ u₆ 3 := by
    wram_exec [hu₅_sav, show u₅.regs rPreHsBase = preHs by regs_frame]
  have below₆ : ∀ a < free, u₆.mem a = x.mem a := fun a ha =>
    (hfr₃ a (Or.inl (by omega))).trans ((below₄ a (by omega)).trans (hfr₁ a (Or.inl ha)))
  obtain ⟨y, endFree, he_stH, hy_ro, hy_free, hlo₄, hhi₄, hstH, hfr₄, hreg_y⟩ :=
    exec_stagesCode (initRoot := free₂) (fbBase := preHs) (signMode := 1)
      (P_low := P_low) (G := H) (B₀ := 4 ^ d * W ^ 2) (B := B) u₆
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by omega)
      hnd (hdom_of below₆) (by omega) hdom_closed htr_h0 heq_h0
      (fun hpos => by
        obtain ⟨-, -, hph, -, -, hfbH⟩ := hfb_valid hpos
        exact ⟨by omega, tables_transport below₆ (by omega) (fun k hk => by omega) hfbH⟩)
      hH_le hB_H hfit_B (hfit_free.of_le (by omega)) hfit_mask
  have htot : ExecWithin w runTransformTriple x y (tripleTime d dom.length) :=
    (he₀.seq (he_stF.seq (he₂.seq (he_stG.seq (he₄.seq (he_mul.seq (he₆.seq he_stH))))))).mono
      (by dsimp [tripleTime]; omega)
  have y_eq_u₃ : ∀ a < free₂, y.mem a = u₃.mem a := fun a ha => by
    rw [hfr₄ a (Or.inl (by omega)), ← hu₄_mem]; exact hfr₃ a (Or.inl ha)
  have y_eq_u₁ : ∀ a < free₁, y.mem a = u₁.mem a := fun a ha =>
    (y_eq_u₃ a (by omega)).trans (hfr₂ a (Or.inl ha))
  refine ⟨y, free, free₁, free₃, endFree, htot, by regs_frame, by regs_frame, hy_ro, hy_free,
    by omega, by dsimp [tripleSpace]; omega, by omega, by omega, by omega,
    tables_transport y_eq_u₁ (by omega) (fun k hk => by omega) hstF,
    tables_transport y_eq_u₃ (by omega) (fun k hk => by omega) hstG, hstH, ?_, fun a ha => ?_,
    fun i hi => htot.regs_eq (runTransformTriple_preserves i hi)⟩
  · obtain ⟨outFn, htr, heq⟩ := hstH d le_rfl
    refine ⟨outFn, htr, fun X hX => ?_⟩
    rw [heq X hX, coveringProduct_eq_subsetMobius]
    simp only [one_ne_zero, ↓reduceIte, htake]
    rw [yatesTransform_neg_one_apply (List.nodup_finRange d) H (by intro i _; simp)]
  · rcases ha with ha | ha
    · exact (y_eq_u₁ a (by omega)).trans (hfr₁ a (Or.inl ha))
    · rw [hfr₄ a (Or.inr ha)]
      refine (hfr₃ a (Or.inr (by omega))).trans ?_
      rw [hu₄_mem]
      exact (hfr₂ a (Or.inr (by omega))).trans (hfr₁ a (Or.inr (by omega)))

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
