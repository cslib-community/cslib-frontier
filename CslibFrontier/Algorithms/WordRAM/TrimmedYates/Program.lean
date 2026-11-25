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
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Instance
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.InputSetup
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Preprocess
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Query
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Complete Word-RAM solver and initialized program for [ChanItakuraMaYu2026], Theorem 2.2

Assembles `preprocessCode` and `queryStep` into `solveFromTries`, and joins `inputSetupCode` with
`solveFromTries` into the complete initialized `Program .standard 56` (`program`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.solveFromTries`: evaluates selected entries of
  `coveringProduct` / ranked `subsetConvolution` from pre-built depth-`d` tries for `f` and `g`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.program`: complete flat `Program .standard 56` evaluating
  selected entries of `coveringProduct` / ranked `subsetConvolution` from `State.init inst.encode`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_solveFromTries`,
  `exec_solveFromTries_subsetConvolution`: `ExecWithin` bounds for general `coveringProduct`
  (`highPeak` bound) and ranked `subsetConvolution` ([ChanItakuraMaYu2026], Theorem 2.2 core).
* `Cslib.Algorithms.WordRAM.TrimmedYates.computesListInTime_program`: `ComputesListInTime` bound
  `Instance.timeBound` for `coveringProduct` on all widths satisfying `Instance.FitsWidth`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.executesList_program`: complete initialized Word-RAM bound
  for [ChanItakuraMaYu2026], Theorem 2.2 / Problem 2.1 (`ExecutesList` in
  `O((d + 1)² · (n + ∑_{j ≤ s} C(d, j) + |Cs| · ∑_{s ≤ j ≤ t₁ + t₂} C(t₁ + t₂, j)))` instructions).

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Trimmed Moebius inversion and graphs of
  bounded degree*][BjorklundHusfeldtKaskiKoivisto2010]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.BitString Cslib.WordRAM Cslib.Algorithms.Lean.TrimmedYates

/-- Answer all queries in `Reg.queryPtr[0 .. Reg.queryCount - 1]` from pre-built depth-`Reg.dim`
tries `Reg.trieF` and `Reg.trieG`, allocating preprocessing tables and the length-prefixed answer
array above `Reg.free` (returning the answer array header address in `Reg.outPtr`). -/
def solveFromTries : Code .standard numRegs :=
  .seq preprocessCode (.loop (.lt rQueryIdx Reg.queryCount) queryStep)

/-- **Pre-built input tries bound.** From depth-`d` tries representing `f` and `g` below `baseFree`
and query masks `Cs` at `qPtr`, `solveFromTries` writes the encoded covering-product answers as a
length-prefixed array at `Reg.outPtr` within
`200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * max 1 (highPeak s Cs))` instructions. -/
theorem exec_solveFromTries {w d s baseFree rootF rootG qPtr W : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    (x : Data numRegs)
    (hd : x.regs Reg.dim = d) (hs : x.regs Reg.thresh = s)
    (hfree : x.regs Reg.free = baseFree) (_hbf_pos : 1 ≤ baseFree)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hqptr : x.regs Reg.queryPtr = qPtr) (hqcnt : x.regs Reg.queryCount = Cs.length)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), x.mem (qPtr + j) = setMask Cs[j])
    (htrieF : HoldsTrie x.mem baseFree d rootF fnF)
    (htrieG : HoldsTrie x.mem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hfit_space : Fits w (solveSpace baseFree d s Cs.length (highPeak s Cs)))
    (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ y, ExecWithin w solveFromTries x y
        (200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * max 1 (highPeak s Cs))) ∧
      outputList y.mem (y.regs Reg.outPtr) = (Cs.map (coveringProduct f g)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + Cs.length) ∧
      (∀ a < baseFree, y.mem a = x.mem a) := by
  obtain ⟨s₆, preMem, outBase, preFs, preGs, preHs, preOutFn,
    he_pre, hob_gt_bf, hqw_bound, hf_qw, hpre_below_bf, ⟨hpFs_lt, hpGs_lt, hpHs_lt⟩,
    hpreF_st, hpreG_st, hpreH_st, hpreOut_tr, hpreOut_eq, hs₆_qi, hs₆P⟩ :=
    exec_preprocessCode x hd hs hfree htF_reg htG_reg hqptr hqcnt
      htrieF htrieG hf_eq hg_eq hf_le hg_le hfit_space hfit_val
  let H_pos := max 1 (highPeak s Cs)
  have hH_pos1 : 1 ≤ H_pos := le_max_left 1 _
  have hCs_H : ∀ C ∈ Cs, highCount #C s ≤ H_pos :=
    fun C hC => (le_highPeak_of_mem s hC).trans (le_max_right 1 _)
  let P_q := QueryInv s outBase rootF rootG qPtr preFs preGs preHs f g Cs preMem
  have hqbody (st : Data numRegs) (hst : P_q (st.regs rQueryIdx) st)
      (hq : st.regs rQueryIdx < Cs.length) :
      ∃ z, ExecWithin w queryStep st z (180 * (d + 1) ^ 2 * H_pos) ∧
        P_q (st.regs rQueryIdx + 1) z ∧ z.regs rQueryIdx = st.regs rQueryIdx + 1 :=
    exec_queryStep hob_gt_bf hq_below hq_mem hpre_below_bf htrieF htrieG
      hf_eq hg_eq hf_le hg_le hpFs_lt hpGs_lt hpHs_lt
      hpreF_st hpreG_st hpreH_st hpreOut_tr hpreOut_eq
      hH_pos1 hCs_H hqw_bound hfit_space hfit_val st hst hq
  obtain ⟨y, hloop_q, hyP, _⟩ := ExecWithin.loop_count P_q
    (fun st hst => hst.2.2.2.2.2.2.2.2.2.1) hqbody (by simp [hs₆_qi]) hs₆P
  obtain ⟨_, _, _, _, hy_out, _, _, _, _, _, _, _, _, hy_pre, hy_ob, hy_ans⟩ := hyP
  have htot : ExecWithin w solveFromTries x y
      (200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * H_pos)) := by
    refine (he_pre.seq hloop_q).mono ?_
    rw [hs₆_qi, Nat.sub_zero]
    exact Eq.trans_le (by omega) (solve_total_time_le (lowCount_pos d s) hH_pos1)
  refine ⟨y, htot, ?_, ?_, ?_⟩
  · rw [hy_out]
    refine List.ext_getElem (by simp [hy_ob]) fun j hj1 _ => ?_
    rw [getElem_outputList]
    have hj_cs : j < Cs.length := by simpa [hy_ob] using hj1
    simpa using hy_ans j hj_cs hj_cs
  · rw [hy_out]
    exact hf_qw.of_le (by omega)
  · intro a ha
    exact (hy_pre a (by omega)).trans (hpre_below_bf a ha)

/-- **Ranked subset-convolution bound from pre-built input tries** ([ChanItakuraMaYu2026],
Theorem 2.2 core): when `f` is supported on sets of size `t₁`, `g` on sets of size `t₂`, and every
query `C ∈ Cs` has size `t₁ + t₂` with `s ≤ t₁ + t₂` (`t₁ = t₂ = t` in Theorem 2.2),
`solveFromTries` returns `(Cs.map (subsetConvolution f g)).map Signed.encode` within
`200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * highCount (t₁ + t₂) s)` instructions. -/
theorem exec_solveFromTries_subsetConvolution {w d s t₁ t₂ baseFree rootF rootG qPtr W : ℕ}
    {fnF fnG : ℕ → ℕ} {f g : Finset (Fin d) → ℤ} {Cs : List (Finset (Fin d))}
    (x : Data numRegs)
    (hd : x.regs Reg.dim = d) (hs_reg : x.regs Reg.thresh = s)
    (hfree : x.regs Reg.free = baseFree) (hbf_pos : 1 ≤ baseFree)
    (htF_reg : x.regs Reg.trieF = rootF) (htG_reg : x.regs Reg.trieG = rootG)
    (hqptr : x.regs Reg.queryPtr = qPtr) (hqcnt : x.regs Reg.queryCount = Cs.length)
    (hq_below : qPtr + Cs.length ≤ baseFree)
    (hq_mem : ∀ j (hj : j < Cs.length), x.mem (qPtr + j) = setMask Cs[j])
    (htrieF : HoldsTrie x.mem baseFree d rootF fnF)
    (htrieG : HoldsTrie x.mem baseFree d rootG fnG)
    (hf_eq : ∀ S : Finset (Fin d), fnF (setMask S) = Signed.encode (f S))
    (hg_eq : ∀ S : Finset (Fin d), fnG (setMask S) = Signed.encode (g S))
    (hf_le : ∀ S, (f S).natAbs ≤ W) (hg_le : ∀ S, (g S).natAbs ≤ W)
    (hf_rank : ∀ A, f A ≠ 0 → #A = t₁) (hg_rank : ∀ B, g B ≠ 0 → #B = t₂)
    (hCs_card : ∀ C ∈ Cs, #C = t₁ + t₂) (hs_le : s ≤ t₁ + t₂)
    (hfit_space : Fits w (solveSpace baseFree d s Cs.length (highCount (t₁ + t₂) s)))
    (hfit_val : Fits w (valueEnvelope d W)) :
    ∃ y, ExecWithin w solveFromTries x y
        (200 * (d + 1) ^ 2 * (lowCount d s + Cs.length * highCount (t₁ + t₂) s)) ∧
      outputList y.mem (y.regs Reg.outPtr) = (Cs.map (subsetConvolution f g)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + Cs.length) ∧
      (∀ a < baseFree, y.mem a = x.mem a) := by
  have hpk_le : highPeak s Cs ≤ highCount (t₁ + t₂) s :=
    highPeak_le_of_forall_card_eq s (t₁ + t₂) hCs_card
  have hhc_pos : 1 ≤ highCount (t₁ + t₂) s := highCount_pos hs_le
  have hmax_le : max 1 (highPeak s Cs) ≤ highCount (t₁ + t₂) s := max_le hhc_pos hpk_le
  have hsp' : Fits w (solveSpace baseFree d s Cs.length (highPeak s Cs)) :=
    hfit_space.of_le (by
      dsimp only [solveSpace]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
  obtain ⟨y, he, hlist, hfit_out, hframe⟩ :=
    exec_solveFromTries x hd hs_reg hfree hbf_pos htF_reg htG_reg hqptr hqcnt
      hq_below hq_mem htrieF htrieG hf_eq hg_eq hf_le hg_le hsp' hfit_val
  refine ⟨y, he.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ hmax_le) _)), ?_, hfit_out, hframe⟩
  rw [hlist]
  congr 1
  exact List.map_congr_left fun C hC =>
    coveringProduct_eq_subsetConvolution hf_rank hg_rank (hCs_card C hC)

/-- Decode `Instance.encode` from `Data.init`, build the sparse input tries for `leftEntries` and
`rightEntries`, and invoke `solveFromTries`. -/
private def inputCode : Code .standard numRegs :=
  .seq inputSetupCode solveFromTries

/-- Complete flat `Program .standard 56` evaluating selected entries of covering product / ranked
subset convolution from `State.init inst.encode`. -/
def program : Program .standard numRegs :=
  inputCode.program Reg.outPtr

private theorem exec_inputCode (inst : Instance) {w : ℕ} (hw : inst.FitsWidth w) :
    ∃ y, ExecWithin w inputCode (.init inst.encode) y (inst.timeBound - 1) ∧
      outputList y.mem (y.regs Reg.outPtr) =
        (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map Signed.encode ∧
      Fits w (y.regs Reg.outPtr + inst.queries.length) := by
  obtain ⟨u₄, baseFree, rootF, rootG, fnF, fnG, he_setup,
    hd, hs, hfree, hbf_pos, htF, htG, hqptr, hqcnt, hq_below, hq_mem,
    htrF, htrG, hf_eq, hg_eq, hf_solve_sp⟩ := exec_inputSetupCode inst hw
  obtain ⟨y, he_solve, hy_list, hy_fit, _⟩ :=
    exec_solveFromTries (W := inst.weightSum) (f := inst.leftFn) (g := inst.rightFn) u₄
      hd hs hfree hbf_pos htF htG hqptr hqcnt hq_below hq_mem
      htrF htrG hf_eq hg_eq
      (fun S => (natAbs_evalEntries_le _ S).trans (Nat.le_add_right _ _))
      (fun S => (natAbs_evalEntries_le _ S).trans (Nat.le_add_left _ _))
      hf_solve_sp hw.2
  refine ⟨y, (he_setup.seq he_solve).mono ?_, hy_list, hy_fit⟩
  rw [Instance.timeBound, Instance.numEntries]
  exact Eq.trans_le (by omega) (input_total_time_le (lowCount_pos inst.d inst.s))

/-- `program` computes the encoded covering-product query answers within `Instance.timeBound`
instructions on every width satisfying `Instance.FitsWidth`. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ => Instance.encode) (fun inst _ => inst.timeBound)
      Instance.FitsWidth
      (fun inst => (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map
        Signed.encode) := by
  have hraw := Code.computesListInTime_program inputCode Reg.outPtr
    (encode := fun _ => Instance.encode) (time := fun inst _ => inst.timeBound - 1)
    (allowed := Instance.FitsWidth)
    (f := fun inst =>
      (inst.queries.map (coveringProduct inst.leftFn inst.rightFn)).map Signed.encode)
    fun inst w hw _ => by simpa using exec_inputCode inst hw
  refine hraw.mono (fun inst _ => ?_) (fun _ _ h => h)
  have hpos : 0 < inst.timeBound :=
    Nat.mul_pos (by positivity) (by have := lowCount_pos inst.d inst.s; omega)
  omega

/-- **Complete initialized Word-RAM bound for [ChanItakuraMaYu2026], Theorem 2.2 / Problem 2.1.**
Given a sparse weighted set-function instance `inst` over `Fin inst.d` where `leftEntries` have
size `t₁`, `rightEntries` have size `t₂`, and `queries` have size `t₁ + t₂` with
`inst.s ≤ t₁ + t₂` (set `t₁ = t₂ = t` for Theorem 2.2), running `program` from
`State.init inst.encode` halts via `ExecutesList` with the encoded subset-convolution answers in at
most `250 * (inst.d + 1) ^ 2 * (inst.numEntries + lowCount inst.d inst.s +
inst.queries.length * highCount (t₁ + t₂) inst.s)` instructions. -/
theorem executesList_program (inst : Instance) {t₁ t₂ w : ℕ}
    (hleft : ∀ p ∈ inst.leftEntries, p.2 ≠ 0 → #p.1 = t₁)
    (hright : ∀ p ∈ inst.rightEntries, p.2 ≠ 0 → #p.1 = t₂)
    (hqueries : ∀ C ∈ inst.queries, #C = t₁ + t₂)
    (hs : inst.s ≤ t₁ + t₂)
    (hfit_space : Fits w (solveSpace
      (10 + 2 * (inst.d + 1) * inst.numEntries + inst.queries.length)
      inst.d inst.s inst.queries.length (highCount (t₁ + t₂) inst.s)))
    (hfit_val : Fits w (valueEnvelope inst.d inst.weightSum)) :
    ∃ n, ExecutesList w program (.init inst.encode)
        ((inst.queries.map (subsetConvolution inst.leftFn inst.rightFn)).map Signed.encode) n ∧
      n ≤ 250 * (inst.d + 1) ^ 2 *
        (inst.numEntries + lowCount inst.d inst.s +
          inst.queries.length * highCount (t₁ + t₂) inst.s) := by
  have hpk_le : highPeak inst.s inst.queries ≤ highCount (t₁ + t₂) inst.s :=
    highPeak_le_of_forall_card_eq inst.s (t₁ + t₂) hqueries
  have hhc_pos : 1 ≤ highCount (t₁ + t₂) inst.s := highCount_pos hs
  have hmax_le : max 1 (highPeak inst.s inst.queries) ≤ highCount (t₁ + t₂) inst.s :=
    max_le hhc_pos hpk_le
  have hw : inst.FitsWidth w :=
    ⟨hfit_space.of_le (by
      dsimp only [Instance.spaceBound, solveSpace]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _), hfit_val⟩
  obtain ⟨n, hex, hn⟩ := computesListInTime_program inst w hw hw.inputFits
  dsimp only at hex hn
  have heq_conv : inst.queries.map (coveringProduct inst.leftFn inst.rightFn) =
      inst.queries.map (subsetConvolution inst.leftFn inst.rightFn) :=
    List.map_congr_left fun C hC =>
      coveringProduct_eq_subsetConvolution (evalEntries_ranked hleft) (evalEntries_ranked hright)
        (hqueries C hC)
  rw [heq_conv] at hex
  refine ⟨n, hex, hn.trans ?_⟩
  dsimp only [Instance.timeBound]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmax_le) _)

end Cslib.Algorithms.WordRAM.TrimmedYates
