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
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

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

private def inputPrepSolveCode : Code .standard numRegs := ram[
  Reg.trieG ← Reg.builtRoot;
  rGenTmp ← Reg.entryCount + Reg.entryCount;
  Reg.queryPtr ← Reg.entryPtr + rGenTmp ]

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
  obtain ⟨Lp, rfl⟩ := Nat.exists_eq_add_of_le' hL
  refine (Nat.le_sub_iff_add_le (Nat.succ_le_of_lt (by positivity))).2 ?_
  zify
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- Reads the `p`-th `(mask, weight)` pair from `encodeEntries es ++ post`. -/
private theorem getD_encodeEntries_append {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (post : List ℕ) {p : ℕ} (hp : p < es.length) :
    (encodeEntries es ++ post).getD (2 * p) 0 = setMask es[p].1 ∧
    (encodeEntries es ++ post).getD (2 * p + 1) 0 = Signed.encode es[p].2 := by
  induction es generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
    rcases p with _ | p
    · simp [encodeEntries]
    · simpa [encodeEntries, Nat.mul_add] using ih (p := p) (by simpa using hp)

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
  obtain ⟨initFree, hif⟩ : ∃ n, n = 6 + 2 * (nL + nR) + nQ := ⟨_, rfl⟩
  have hnum_eq : inst.numEntries = nL + nR := by rw [Instance.numEntries, hnL_def, hnR_def]
  have hx0 : x.mem 0 = 5 + 2 * (nL + nR) + nQ := by
    rw [Data.init_mem_zero, inst.length_encode, hnum_eq, hnQ_def]
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ : x.mem 1 = inst.d ∧ x.mem 2 = inst.s ∧
      x.mem 3 = inst.leftEntries.length ∧ x.mem 4 = inst.rightEntries.length ∧
      x.mem 5 = inst.queries.length := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsp' : Fits w (solveSpace (10 + 2 * (inst.d + 1) * (nL + nR) + nQ)
      inst.d inst.s nQ (highPeak inst.s inst.queries)) := by
    rwa [Instance.spaceBound, hnum_eq, hnQ_def] at hsp
  have hleft_sp := input_left_space_le inst.d inst.s nL nR nQ (highPeak inst.s inst.queries)
  have hf_if : Fits w (6 + 2 * (nL + nR) + nQ) := hsp'.of_le (by omega)
  -- Exact word-size facts for the pointer arithmetic, so `wram_exec` finds them by assumption.
  obtain ⟨hf_2nL, hf_L, hf_2nR, hf_R⟩ : Fits w (nL + nL) ∧ Fits w (6 + (nL + nL)) ∧
      Fits w (nR + nR) ∧ Fits w (6 + 2 * nL + (nR + nR)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact hf_if.of_le (by omega)
  -- Header decode
  dsimp only [x] at hx0 hm1 hm2 hm3 hm4 hm5
  simp only [exists_and_left]
  wram_exec [inputSetupCode, hx0, hm1, hm2, hm3, hm5]
  refine WP.name fun u₀ hu₀ => ?_
  obtain ⟨hu₀d, hu₀s, hu₀fr, hu₀cdp, hu₀cdl, hu₀qc, hu₀mem⟩ :
      u₀.regs Reg.dim = inst.d ∧ u₀.regs Reg.thresh = inst.s ∧ u₀.regs Reg.free = initFree ∧
      u₀.regs Reg.entryPtr = 6 ∧ u₀.regs Reg.entryCount = inst.leftEntries.length ∧
      u₀.regs Reg.queryCount = inst.queries.length ∧ u₀.mem = x.mem := by
    rw [hu₀]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals wram_simp
    omega
  -- Build left input trie
  obtain ⟨u₁, free₁, fnF, he_bL, hu₁_sav, hu₁_fr, hlo_L, hhi_L, htrF, hf_eq, hfr_L, hreg_L⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.leftEntries u₀ hu₀d hu₀cdp hu₀cdl hu₀fr
      (by omega) (by omega)
      (fun p hp => by
        rw [hu₀mem, show 6 + 2 * p = 2 * p + 5 + 1 by omega]
        simpa only [x, Instance.encode, List.cons_append, List.nil_append, List.append_assoc,
          Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_cons_succ] using
          getD_encodeEntries_append inst.leftEntries _ hp)
      (Nat.le_add_right _ _) hval (by rw [hnL_def, hif]; exact hsp'.of_le hleft_sp)
  rw [hnL_def, hif] at hhi_L
  -- Prepare right input trie
  obtain ⟨u₂, he_pR, hu₂_tF, hu₂_cdp, hu₂_cdl, hu₂_mem⟩ : ∃ u₂,
      ExecWithin w inputPrepRightCode u₁ u₂ 5 ∧ u₂.regs Reg.trieF = initFree ∧
      u₂.regs Reg.entryPtr = 6 + 2 * nL ∧ u₂.regs Reg.entryCount = inst.rightEntries.length ∧
      u₂.mem = u₁.mem := by
    have hu₁_m4 : u₁.mem 4 = inst.rightEntries.length := by
      rw [hfr_L 4 (Or.inl (by omega)), hu₀mem, hm4]
    have hu₁_cdl : u₁.regs Reg.entryCount = nL := by rw [← hnL_def]; regs_frame
    have hu₁_cdp : u₁.regs Reg.entryPtr = 6 := by regs_frame
    wram_exec [inputPrepRightCode, hu₁_sav, hu₁_cdl, hu₁_cdp, hu₁_m4]
    refine ⟨rfl, ?_, rfl, rfl⟩
    wram_simp; omega
  -- Build right input trie
  obtain ⟨u₃, baseFree, fnG, he_bR, hu₃_sav, hu₃_fr, hlo_R, hhi_R, htrG, hg_eq, hfr_R, hreg_R⟩ :=
    exec_buildInputTrie (W := inst.weightSum) inst.rightEntries u₂ (by regs_frame) hu₂_cdp
      hu₂_cdl (by regs_frame) (by omega) (by omega)
      (fun p hp => by
        rw [hu₂_mem, hfr_L _ (Or.inl (by omega)), hfr_L _ (Or.inl (by omega)), hu₀mem,
          show 6 + 2 * nL + 2 * p + 1 = 2 * p + 1 + 2 * nL + 5 + 1 by omega,
          show 6 + 2 * nL + 2 * p = 2 * p + 2 * nL + 5 + 1 by omega]
        simpa only [x, Instance.encode, List.cons_append, List.nil_append, List.append_assoc,
          Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, hnL_def,
          length_encodeEntries, le_add_iff_nonneg_left, zero_le, List.getElem?_append_right,
          add_tsub_cancel_right] using
          getD_encodeEntries_append inst.rightEntries (inst.queries.map setMask) hp)
      (Nat.le_add_left _ _) hval
      (by rw [hnR_def]; exact hsp'.of_le (input_right_space_le (by omega)))
  rw [hnR_def] at hhi_R
  -- Prepare solveFromTries
  obtain ⟨u₄, he_pS, hu₄_tG, hu₄_qp, hu₄_mem⟩ : ∃ u₄, ExecWithin w inputPrepSolveCode u₃ u₄ 3 ∧
      u₄.regs Reg.trieG = free₁ ∧ u₄.regs Reg.queryPtr = 6 + 2 * inst.numEntries ∧
      u₄.mem = u₃.mem := by
    have hu₃_cdl : u₃.regs Reg.entryCount = nR := by rw [← hnR_def]; regs_frame
    have hu₃_cdp : u₃.regs Reg.entryPtr = 6 + 2 * nL := by regs_frame
    wram_exec [inputPrepSolveCode, hu₃_sav, hu₃_cdl, hu₃_cdp]
    refine ⟨rfl, ?_, rfl⟩
    wram_simp [hnum_eq]; omega
  have hbf_le := input_bf_le hhi_L hhi_R
  refine WP.of_execWithin he_bL <| WP.of_execWithin (he_pR.seq (he_bR.seq he_pS))
    ⟨by omega, ?_, ?_, baseFree,
    by regs_frame, (Nat.zero_lt_succ _).trans_le hlo_R, initFree,
    by regs_frame, free₁, hu₄_tG, hu₄_qp,
    by regs_frame,
    by omega, fun j hj => ?_, fnF, ?_, fnG,
    by rwa [hu₄_mem], hf_eq, hg_eq,
    hnQ_def ▸ hsp'.of_le (by dsimp only [solveSpace]; omega)⟩
  · regs_frame
  · regs_frame
  · rw [hu₄_mem, hfr_R _ (Or.inl (by omega)), hu₂_mem, hfr_L _ (Or.inl (by omega)), hu₀mem,
      hnum_eq, show 6 + 2 * (nL + nR) + j = j + 2 * nR + 2 * nL + 5 + 1 by omega]
    simp only [x, Instance.encode, List.cons_append, List.nil_append, List.append_assoc,
      Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, hnL_def, hnR_def,
      length_encodeEntries, le_add_iff_nonneg_left, zero_le, List.getElem?_append_right,
      add_tsub_cancel_right, List.length_map, hj, getElem?_pos, List.getElem_map, Option.getD_some]
  · rw [hu₄_mem]
    refine (htrF.congr_below fun a ha => ?_).mono_bound (by omega)
    rw [hfr_R a (Or.inl ha), hu₂_mem]

end Cslib.Algorithms.WordRAM.TrimmedYates
