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
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.InputTrie
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Decoding `Instance.encode` and building both input tries on the word RAM

Decodes `[d, s, |leftEntries|, |rightEntries|, |queries|, ...]` from `Data.init inst.encode`,
builds the sparse depth-`d` binary tries for `leftEntries` and `rightEntries` via `buildInputTrie`,
and prepares the caller registers for `solveFromTries` (`inputSetupCode`, `exec_inputSetupCode`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.inputSetupCode`: header-decoding and dual-trie-building
  prefix of `program`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.input_total_time_le`: overall instruction budget for
  `inputSetupCode` followed by `solveFromTries`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_inputSetupCode`: `ExecWithin` specification from
  `Data.init inst.encode` producing `HoldsTrie` witnesses for `inst.leftFn` and `inst.rightFn`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

private def inputPrepRightCode : Code .standard numRegs := ram[
  Reg.trieF ← Reg.builtRoot;
  rGenTmp ← Reg.entryCount + Reg.entryCount;
  Reg.entryPtr ← Reg.entryPtr + rGenTmp;
  rGenTmp ← #4;
  Reg.entryCount ← *rGenTmp ]

private theorem inputPrepRightCode_preserves (i : Fin numRegs) :
    i ≠ Reg.trieF ∧ i ≠ rGenTmp ∧ i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount →
      inputPrepRightCode.Preserves i := by
  decide +kernel +revert

private def inputPrepSolveCode : Code .standard numRegs := ram[
  Reg.trieG ← Reg.builtRoot;
  rGenTmp ← Reg.entryCount + Reg.entryCount;
  Reg.queryPtr ← Reg.entryPtr + rGenTmp ]

private theorem inputPrepSolveCode_preserves (i : Fin numRegs) :
    i ≠ Reg.trieG ∧ i ≠ rGenTmp ∧ i ≠ Reg.queryPtr → inputPrepSolveCode.Preserves i := by
  decide +kernel +revert

/-- Decode `Instance.encode` from `Data.init` and build both sparse input tries (`leftEntries` and
`rightEntries`), setting up registers for `solveFromTries`. -/
def inputSetupCode : Code .standard numRegs :=
  .seq (ram[
    rZero ← #0;
    rOne ← #1;
    Reg.free ← *rZero;
    Reg.free ← Reg.free + rOne;
    rGenTmp ← #1;
    Reg.dim ← *rGenTmp;
    rGenTmp ← #2;
    Reg.thresh ← *rGenTmp;
    rGenTmp ← #3;
    Reg.entryCount ← *rGenTmp;
    rGenTmp ← #5;
    Reg.queryCount ← *rGenTmp;
    Reg.entryPtr ← #6 ])
  (.seq buildInputTrie
    (.seq inputPrepRightCode
      (.seq buildInputTrie inputPrepSolveCode)))

private theorem input_left_space_le (d s nL nR nQ H : ℕ) :
    (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL ≤
      solveSpace (10 + 2 * (d + 1) * (nL + nR) + nQ) d s nQ H := by
  dsimp only [solveSpace]; rw [sq]; nlinarith

private theorem input_right_space_le {d s nL nR nQ H free₁ : ℕ}
    (h1 : free₁ ≤ (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL) :
    free₁ + 2 + 2 * d * nR ≤
      solveSpace (10 + 2 * (d + 1) * (nL + nR) + nQ) d s nQ H := by
  dsimp only [solveSpace]; rw [sq]; nlinarith

private theorem input_bf_le {d nL nR nQ free₁ bf : ℕ}
    (h1 : free₁ ≤ (6 + 2 * (nL + nR) + nQ) + 2 + 2 * d * nL)
    (h2 : bf ≤ free₁ + 2 + 2 * d * nR) :
    bf ≤ 10 + 2 * (d + 1) * (nL + nR) + nQ := by
  nlinarith

theorem input_total_time_le {d nL nR nQ L H : ℕ} (hL : 1 ≤ L) :
    13 + (nL * (23 * d + 40) + 11 + (5 + (nR * (23 * d + 40) + 11 +
      (3 + 200 * (d + 1) ^ 2 * (L + nQ * H))))) ≤
      250 * (d + 1) ^ 2 * (nL + nR + L + nQ * H) - 1 := by
  obtain ⟨Lp, rfl⟩ : ∃ Lp, L = Lp + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  have hid :
      (13 + (nL * (23 * d + 40) + 11 + (5 + (nR * (23 * d + 40) + 11 +
        (3 + 200 * (d + 1) ^ 2 * ((Lp + 1) + nQ * H))))) + 1) +
      ((nL + nR) * (250 * d ^ 2 + 477 * d + 210) + (50 * d ^ 2 + 100 * d + 6) +
        Lp * (50 * (d + 1) ^ 2) + nQ * H * (50 * (d + 1) ^ 2)) =
      250 * (d + 1) ^ 2 * (nL + nR + (Lp + 1) + nQ * H) := by ring
  omega

private theorem getElem_encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (p : ℕ) (hp : p < es.length) :
    (encodeEntries es)[2 * p]'(by simp; omega) = setMask es[p].1 ∧
    (encodeEntries es)[2 * p + 1]'(by simp; omega) = Signed.encode es[p].2 := by
  induction es generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
    rcases p with _ | p
    · simp [encodeEntries]
    · have hp' : p < tl.length := by simp at hp; omega
      obtain ⟨h0, h1⟩ := ih p hp'
      have heq : encodeEntries (hd :: tl) = [setMask hd.1, Signed.encode hd.2] ++
          encodeEntries tl := rfl
      refine ⟨?_, ?_⟩
      · simp only [heq]
        rw [List.getElem_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
        simpa [Nat.mul_add] using h0
      · simp only [heq]
        rw [List.getElem_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
        simpa [Nat.mul_add] using h1

theorem exec_inputSetupCode (inst : Instance) {w : ℕ} (hw : inst.FitsWidth w) :
    ∃ u₄ baseFree rootF rootG fnF fnG,
      ExecWithin w inputSetupCode (.init inst.encode) u₄
        (13 + (inst.leftEntries.length * (23 * inst.d + 40) + 11 +
          (5 + (inst.rightEntries.length * (23 * inst.d + 40) + 11 + 3)))) ∧
      u₄.regs Reg.dim = inst.d ∧ u₄.regs Reg.thresh = inst.s ∧
      u₄.regs Reg.free = baseFree ∧ 1 ≤ baseFree ∧
      u₄.regs Reg.trieF = rootF ∧ u₄.regs Reg.trieG = rootG ∧
      u₄.regs Reg.queryPtr = 6 + 2 * inst.numEntries ∧
      u₄.regs Reg.queryCount = inst.queries.length ∧
      6 + 2 * inst.numEntries + inst.queries.length ≤ baseFree ∧
      (∀ j (hj : j < inst.queries.length),
        u₄.mem (6 + 2 * inst.numEntries + j) = setMask inst.queries[j]) ∧
      HoldsTrie u₄.mem baseFree inst.d rootF fnF ∧
      HoldsTrie u₄.mem baseFree inst.d rootG fnG ∧
      (∀ S : Finset (Fin inst.d), fnF (setMask S) = Signed.encode (inst.leftFn S)) ∧
      (∀ S : Finset (Fin inst.d), fnG (setMask S) = Signed.encode (inst.rightFn S)) ∧
      Fits w (solveSpace baseFree inst.d inst.s inst.queries.length
        (highPeak inst.s inst.queries)) := by
  obtain ⟨hsp, hval⟩ := hw
  let x : Data numRegs := .init inst.encode
  obtain ⟨nL, hnL_def⟩ : ∃ nL, inst.leftEntries.length = nL := ⟨_, rfl⟩
  obtain ⟨nR, hnR_def⟩ : ∃ nR, inst.rightEntries.length = nR := ⟨_, rfl⟩
  obtain ⟨nQ, hnQ_def⟩ : ∃ nQ, inst.queries.length = nQ := ⟨_, rfl⟩
  have hnum_eq : inst.numEntries = nL + nR := by
    rw [Instance.numEntries, hnL_def, hnR_def]
  let initFree := 6 + 2 * (nL + nR) + nQ
  have hx0 : x.mem 0 = 5 + 2 * (nL + nR) + nQ := by
    rw [Data.init_mem_zero, inst.length_encode, hnum_eq, hnQ_def]
  have hhdr : (Block.mk 1 5).Realizes x.mem
      [inst.d, inst.s, nL, nR, nQ].get := by
    rw [← hnL_def, ← hnR_def, ← hnQ_def]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs) []
        [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length]
        (encodeEntries inst.leftEntries ++ encodeEntries inst.rightEntries ++
          inst.queries.map setMask)
  have hm1 : x.mem 1 = inst.d := hhdr ⟨0, by decide⟩
  have hm2 : x.mem 2 = inst.s := hhdr ⟨1, by decide⟩
  have hm3 : x.mem 3 = nL := hhdr ⟨2, by decide⟩
  have hm4 : x.mem 4 = nR := hhdr ⟨3, by decide⟩
  have hm5 : x.mem 5 = nQ := hhdr ⟨4, by decide⟩
  have hleft_blk : (Block.mk 6 (encodeEntries inst.leftEntries).length).Realizes x.mem
      (encodeEntries inst.leftEntries).get := by
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length]
        (encodeEntries inst.leftEntries)
        (encodeEntries inst.rightEntries ++ inst.queries.map setMask)
  have hright_blk : (Block.mk (6 + 2 * nL) (encodeEntries inst.rightEntries).length).Realizes x.mem
      (encodeEntries inst.rightEntries).get := by
    have hpre_len : ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
        inst.queries.length] ++ encodeEntries inst.leftEntries).length + 1 =
        6 + 2 * nL := by simp [hnL_def]; omega
    rw [← hpre_len]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
          inst.queries.length] ++ encodeEntries inst.leftEntries)
        (encodeEntries inst.rightEntries)
        (inst.queries.map setMask)
  have hquery_blk :
      (Block.mk (6 + 2 * (nL + nR)) (inst.queries.map setMask).length).Realizes
        x.mem (inst.queries.map setMask).get := by
    have hpre_len : ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
        inst.queries.length] ++ encodeEntries inst.leftEntries ++
        encodeEntries inst.rightEntries).length + 1 = 6 + 2 * (nL + nR) := by
      simp [hnL_def, hnR_def]; omega
    rw [← hpre_len]
    simpa [x, Instance.encode, List.append_assoc] using
      Data.init_realizes_append (r := numRegs)
        ([inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length,
          inst.queries.length] ++ encodeEntries inst.leftEntries ++
          encodeEntries inst.rightEntries)
        (inst.queries.map setMask) []
  have hleft_mem : ∀ p (hp : p < inst.leftEntries.length),
      x.mem (6 + 2 * p) = setMask inst.leftEntries[p].1 ∧
      x.mem (6 + 2 * p + 1) = Signed.encode inst.leftEntries[p].2 := by
    intro p hp
    obtain ⟨h0, h1⟩ := getElem_encodeEntries inst.leftEntries p hp
    have hr0 : x.mem (6 + 2 * p) = (encodeEntries inst.leftEntries)[2 * p]'(by simp; omega) :=
      hleft_blk ⟨2 * p, by simp; omega⟩
    have hr1 : x.mem (6 + (2 * p + 1)) =
        (encodeEntries inst.leftEntries)[2 * p + 1]'(by simp; omega) :=
      hleft_blk ⟨2 * p + 1, by simp; omega⟩
    rw [← Nat.add_assoc] at hr1
    exact ⟨hr0.trans h0, hr1.trans h1⟩
  have hright_mem : ∀ p (hp : p < inst.rightEntries.length),
      x.mem (6 + 2 * nL + 2 * p) = setMask inst.rightEntries[p].1 ∧
      x.mem (6 + 2 * nL + 2 * p + 1) = Signed.encode inst.rightEntries[p].2 := by
    intro p hp
    obtain ⟨h0, h1⟩ := getElem_encodeEntries inst.rightEntries p hp
    have hr0 : x.mem (6 + 2 * nL + 2 * p) =
        (encodeEntries inst.rightEntries)[2 * p]'(by simp; omega) :=
      hright_blk ⟨2 * p, by simp; omega⟩
    have hr1 : x.mem (6 + 2 * nL + (2 * p + 1)) =
        (encodeEntries inst.rightEntries)[2 * p + 1]'(by simp; omega) :=
      hright_blk ⟨2 * p + 1, by simp; omega⟩
    rw [← Nat.add_assoc] at hr1
    exact ⟨hr0.trans h0, hr1.trans h1⟩
  have hquery_mem : ∀ j (hj : j < inst.queries.length),
      x.mem (6 + 2 * (nL + nR) + j) = setMask inst.queries[j] := by
    intro j hj
    have hr : x.mem (6 + 2 * (nL + nR) + j) =
        (inst.queries.map setMask)[j]'(by simp; omega) :=
      hquery_blk ⟨j, by simp; omega⟩
    simpa using hr
  -- Header decode
  have hsp_eq : inst.spaceBound = solveSpace (10 + 2 * (inst.d + 1) * (nL + nR) + nQ)
      inst.d inst.s nQ (highPeak inst.s inst.queries) := by
    rw [Instance.spaceBound, hnum_eq, hnQ_def]
  have hsp' : Fits w (solveSpace (10 + 2 * (inst.d + 1) * (nL + nR) + nQ)
      inst.d inst.s nQ (highPeak inst.s inst.queries)) := hsp_eq ▸ hsp
  have hleft_sp := input_left_space_le inst.d inst.s nL nR nQ (highPeak inst.s inst.queries)
  have hf_if : Fits w initFree := hsp'.of_le (by dsimp [initFree]; omega)
  have hf_6 : Fits w 6 := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_5 : Fits w 5 := hf_6.of_le (by omega)
  have hf_4 : Fits w 4 := hf_6.of_le (by omega)
  have hf_3 : Fits w 3 := hf_6.of_le (by omega)
  have hf_2 : Fits w 2 := hf_6.of_le (by omega)
  have hf_1 : Fits w 1 := hf_6.of_le (by omega)
  have hdec : ∃ u₀, ExecWithin (B := .standard) w (ram[
      rZero ← #0;
      rOne ← #1;
      Reg.free ← *rZero;
      Reg.free ← Reg.free + rOne;
      rGenTmp ← #1;
      Reg.dim ← *rGenTmp;
      rGenTmp ← #2;
      Reg.thresh ← *rGenTmp;
      rGenTmp ← #3;
      Reg.entryCount ← *rGenTmp;
      rGenTmp ← #5;
      Reg.queryCount ← *rGenTmp;
      Reg.entryPtr ← #6 ]) x u₀ 13 ∧
      u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧ u₀.regs Reg.dim = inst.d ∧
      u₀.regs Reg.thresh = inst.s ∧ u₀.regs Reg.free = initFree ∧
      u₀.regs Reg.entryPtr = 6 ∧ u₀.regs Reg.entryCount = inst.leftEntries.length ∧
      u₀.regs Reg.queryCount = inst.queries.length ∧ u₀.mem = x.mem := by
    wram_exec [hx0, hm1, hm2, hm3, hm5]
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, hnL_def.symm, hnQ_def.symm, rfl⟩
    wram_simp [hx0, initFree]; omega
  obtain ⟨u₀, he_dec, hu₀z, hu₀o, hu₀d, hu₀s, hu₀fr, hu₀cdp, hu₀cdl, hu₀qc, hu₀mem⟩ := hdec
  -- Build left input trie
  have hf_left : Fits w (initFree + 2 + 2 * inst.d * inst.leftEntries.length) := by
    rw [hnL_def]; exact hsp'.of_le hleft_sp
  obtain ⟨u₁, free₁, fnF, he_bL, hu₁_sav, hu₁_fr, hlo_L, hhi_L, htrF, hf_eq, hfr_L, hreg_L⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.leftEntries u₀
      hu₀d hu₀cdp hu₀cdl hu₀fr (by dsimp [initFree]; omega)
      (by rw [hnL_def]; dsimp [initFree]; omega)
      (by rwa [hu₀mem]) (Nat.le_add_right _ _) hval hf_left
  -- Prepare right input trie
  have hu₁_cdl : u₁.regs Reg.entryCount = nL :=
    (hreg_L Reg.entryCount (by decide)).trans (hu₀cdl.trans hnL_def)
  have hu₁_cdp : u₁.regs Reg.entryPtr = 6 := (hreg_L Reg.entryPtr (by decide)).trans hu₀cdp
  have hu₁_m4 : u₁.mem 4 = nR := by rw [hfr_L 4 (Or.inl (by dsimp [initFree]; omega)), hu₀mem, hm4]
  have hf_2nL : Fits w (nL + nL) := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_6_2nL : Fits w (6 + (nL + nL)) := hf_if.of_le (by dsimp [initFree]; omega)
  have hp_R_st : ∃ u₂, ExecWithin w inputPrepRightCode u₁ u₂ 5 ∧
      u₂.regs Reg.trieF = initFree ∧ u₂.regs Reg.entryPtr = 6 + 2 * nL ∧
      u₂.regs Reg.entryCount = inst.rightEntries.length ∧ u₂.mem = u₁.mem := by
    unfold inputPrepRightCode
    wram_exec [hu₁_sav, hu₁_cdl, hu₁_cdp, hu₁_m4]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · wram_simp; omega
    · wram_simp [hu₁_m4]; exact hnR_def.symm
  obtain ⟨u₂, he_pR, hu₂_tF, hu₂_cdp, hu₂_cdl, hu₂_mem⟩ := hp_R_st
  have hreg_pR : ∀ i, i ≠ Reg.trieF ∧ i ≠ rGenTmp ∧ i ≠ Reg.entryPtr ∧ i ≠ Reg.entryCount →
      u₂.regs i = u₁.regs i :=
    fun i hi => he_pR.regs_eq (inputPrepRightCode_preserves i hi)
  -- Build right input trie
  rw [hnL_def] at hhi_L
  have hright_sp := input_right_space_le (s := inst.s) (H := highPeak inst.s inst.queries) hhi_L
  have hf_right : Fits w (free₁ + 2 + 2 * inst.d * inst.rightEntries.length) := by
    rw [hnR_def]; exact hsp'.of_le hright_sp
  have hright_mem_u₂ : ∀ p (hp : p < inst.rightEntries.length),
      u₂.mem (6 + 2 * nL + 2 * p) = setMask inst.rightEntries[p].1 ∧
      u₂.mem (6 + 2 * nL + 2 * p + 1) = Signed.encode inst.rightEntries[p].2 := by
    intro p hp
    have hpR : p < nR := hnR_def ▸ hp
    rw [hu₂_mem, hfr_L _ (Or.inl (by dsimp [initFree]; omega)),
      hfr_L _ (Or.inl (by dsimp [initFree]; omega)), hu₀mem]
    exact hright_mem p hp
  obtain ⟨u₃, baseFree, fnG, he_bR, hu₃_sav, hu₃_fr, hlo_R, hhi_R, htrG, hg_eq, hfr_R, hreg_R⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.rightEntries u₂
      ((hreg_pR Reg.dim (by decide)).trans ((hreg_L Reg.dim (by decide)).trans hu₀d))
      hu₂_cdp hu₂_cdl
      ((hreg_pR Reg.free (by decide)).trans hu₁_fr) (by dsimp [initFree] at hlo_L; omega)
      (by rw [hnR_def]; dsimp [initFree] at hlo_L; omega)
      hright_mem_u₂ (Nat.le_add_left _ _) hval hf_right
  -- Prepare solveFromTries
  have hu₃_cdl : u₃.regs Reg.entryCount = nR :=
    (hreg_R Reg.entryCount (by decide)).trans (hu₂_cdl.trans hnR_def)
  have hu₃_cdp : u₃.regs Reg.entryPtr = 6 + 2 * nL :=
    (hreg_R Reg.entryPtr (by decide)).trans hu₂_cdp
  have hf_2nR : Fits w (nR + nR) := hf_if.of_le (by dsimp [initFree]; omega)
  have hf_qptr : Fits w (6 + 2 * nL + (nR + nR)) := hf_if.of_le (by dsimp [initFree]; omega)
  have hp_S_st : ∃ u₄, ExecWithin w inputPrepSolveCode u₃ u₄ 3 ∧
      u₄.regs Reg.trieG = free₁ ∧ u₄.regs Reg.queryPtr = 6 + 2 * (nL + nR) ∧
      u₄.mem = u₃.mem := by
    unfold inputPrepSolveCode
    wram_exec [hu₃_sav, hu₃_cdl, hu₃_cdp]
    refine ⟨rfl, ?_, rfl⟩
    wram_simp; omega
  obtain ⟨u₄, he_pS, hu₄_tG, hu₄_qp, hu₄_mem⟩ := hp_S_st
  have hreg_pS : ∀ i, i ≠ Reg.trieG ∧ i ≠ rGenTmp ∧ i ≠ Reg.queryPtr → u₄.regs i = u₃.regs i :=
    fun i hi => he_pS.regs_eq (inputPrepSolveCode_preserves i hi)
  rw [hnR_def] at hhi_R
  have hbf_le := input_bf_le hhi_L hhi_R
  have hf_solve_sp : Fits w (solveSpace baseFree inst.d inst.s inst.queries.length
      (highPeak inst.s inst.queries)) := by
    rw [hnQ_def]
    exact hsp'.of_le (by dsimp [solveSpace]; omega)
  have htrF_u₄ : HoldsTrie u₄.mem baseFree inst.d initFree fnF := by
    rw [hu₄_mem]
    refine (htrF.congr_below fun a ha => ?_).mono_bound (by omega)
    rw [hfr_R a (Or.inl ha), hu₂_mem]
  have hq_mem_u₄ : ∀ j (hj : j < inst.queries.length),
      u₄.mem (6 + 2 * (nL + nR) + j) = setMask inst.queries[j] := by
    intro j hj
    have hjQ : j < nQ := hnQ_def ▸ hj
    rw [hu₄_mem, hfr_R _ (Or.inl (by dsimp [initFree] at hlo_L hlo_R; omega)),
      hu₂_mem, hfr_L _ (Or.inl (by dsimp [initFree]; omega)), hu₀mem]
    exact hquery_mem j hj
  refine ⟨u₄, baseFree, initFree, free₁, fnF, fnG,
    he_dec.seq (he_bL.seq (he_pR.seq (he_bR.seq he_pS))),
    ((hreg_pS Reg.dim (by decide)).trans ((hreg_R Reg.dim (by decide)).trans
      ((hreg_pR Reg.dim (by decide)).trans ((hreg_L Reg.dim (by decide)).trans hu₀d)))),
    ((hreg_pS Reg.thresh (by decide)).trans ((hreg_R Reg.thresh (by decide)).trans
      ((hreg_pR Reg.thresh (by decide)).trans ((hreg_L Reg.thresh (by decide)).trans hu₀s)))),
    ((hreg_pS Reg.free (by decide)).trans hu₃_fr),
    by dsimp [initFree] at hlo_L hlo_R; omega,
    ((hreg_pS Reg.trieF (by decide)).trans ((hreg_R Reg.trieF (by decide)).trans hu₂_tF)),
    hu₄_tG,
    by rw [hnum_eq]; exact hu₄_qp,
    ((hreg_pS Reg.queryCount (by decide)).trans ((hreg_R Reg.queryCount (by decide)).trans
      ((hreg_pR Reg.queryCount (by decide)).trans
        ((hreg_L Reg.queryCount (by decide)).trans hu₀qc)))),
    by rw [hnum_eq, hnQ_def]; dsimp [initFree] at hlo_L hlo_R; omega,
    fun j hj => by rw [hnum_eq]; exact hq_mem_u₄ j hj,
    htrF_u₄,
    by rwa [hu₄_mem],
    hf_eq, hg_eq, hf_solve_sp⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
