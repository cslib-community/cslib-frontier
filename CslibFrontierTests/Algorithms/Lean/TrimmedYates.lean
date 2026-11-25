/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.Lean.TrimmedYates
import CslibFrontier.Algorithms.WordRAM.TrimmedYates

/-!
# Tests for the trimmed Yates passes (pure and Word-RAM)

Concrete checks on both `CslibFrontier.Algorithms.Lean.TrimmedYates` and
`CslibFrontier.Algorithms.WordRAM.TrimmedYates` as an encapsulated downstream `module` client:

* pure `solve` on `Fin 4` with ranked inputs (`t = 1`, `s = 1`) and `solve_eq_subsetConvolution`;
* separation between `coveringProduct` and `subsetConvolution` on unranked inputs;
* concrete `ExecutesList` witnesses for `WordRAM.TrimmedYates.program` on positive-weight,
  negative/duplicate-entry, empty-universe, and short-query (`#C < s`) boundary instances.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.TrimmedYates

open Finset Cslib.BitString Cslib.Algorithms.Lean.TrimmedYates Cslib.WordRAM
open Cslib.Algorithms.WordRAM.TrimmedYates

/-- Left input: weight `2` on `{0}` and `3` on `{1}`. -/
def f : Finset (Fin 4) → ℤ := fun A => if A = {0} then 2 else if A = {1} then 3 else 0

/-- Right input: weight `5` on `{1}` and `7` on `{2}`. -/
def g : Finset (Fin 4) → ℤ := fun B => if B = {1} then 5 else if B = {2} then 7 else 0

/-- Three queries of size `2t = 2`. -/
def queries : List (Finset (Fin 4)) := [{0, 1}, {1, 2}, {0, 3}]

theorem f_ranked : ∀ A, f A ≠ 0 → #A = 1 := by
  intro A h
  unfold f at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem g_ranked : ∀ B, g B ≠ 0 → #B = 1 := by
  intro B h
  unfold g at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem queries_ok : ∀ C ∈ queries, C ⊆ (List.finRange 4).toFinset ∧ #C = 1 + 1 := by
  decide

/-- Pure evaluation: `f{0} g{1} + f{1} g{0} = 10`, `f{1} g{2} = 21`, and `0` at `{0, 3}`. -/
example : solve (List.finRange 4) 1 f g queries = [10, 21, 0] := by decide +kernel

/-- The same answers equal the subset convolutions by `solve_eq_subsetConvolution`. -/
example : queries.map (subsetConvolution f g) = [10, 21, 0] := by
  rw [← solve_eq_subsetConvolution (List.nodup_finRange 4) f_ranked g_ranked queries_ok
    (by decide : 1 ≤ 1 + 1)]
  decide +kernel

/-- Unranked inputs: with `f = g = 1` on all sets, the covering product at `{0}` counts the three
covers `(∅, {0}), ({0}, ∅), ({0}, {0})`, while the subset convolution counts the two partitions. -/
example : coveringProduct (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 3 ∧
    subsetConvolution (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 2 := by
  decide +kernel

/-- Sparse Word-RAM instance corresponding to `f`, `g`, and `queries` on `Fin 4`. -/
def inst4 : Instance where
  d := 4
  s := 1
  leftEntries := [({0}, 2), ({1}, 3)]
  rightEntries := [({1}, 5), ({2}, 7)]
  queries := [{0, 1}, {1, 2}, {0, 3}]

/-- Concrete Word-RAM `ExecutesList` witness on `inst4` at word width `64`, bounding the halting
run by `250 * 5 ^ 2 * (4 + 5 + 3 * 3) = 112500` instructions via `executesList_program`. -/
example : ∃ n, ExecutesList 64 program (.init inst4.encode)
    [Signed.encode 10, Signed.encode 21, Signed.encode 0] n ∧ n ≤ 112500 := by
  have hrun := executesList_program (t₁ := 1) (t₂ := 1) (w := 64) inst4
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hout : (inst4.queries.map (subsetConvolution inst4.leftFn inst4.rightFn)).map
      Signed.encode = [Signed.encode 10, Signed.encode 21, Signed.encode 0] := by decide +kernel
  have hbnd : 250 * (inst4.d + 1) ^ 2 *
      (inst4.numEntries + lowCount inst4.d inst4.s +
        inst4.queries.length * highCount (1 + 1) inst4.s) = 112500 := by decide +kernel
  rwa [hout, hbnd] at hrun

/-- Ranked instance with duplicate set keys (`5 + (-3) = 2` on `{0}`) and negative weights. -/
def negInst : Instance where
  d := 4
  s := 1
  leftEntries := [({0}, 5), ({0}, -3), ({1}, -4)]
  rightEntries := [({1}, 5), ({2}, -7)]
  queries := [{0, 1}, {1, 2}, {0, 2}]

/-- Word-RAM `ExecutesList` witness with negative weights and duplicate entry accumulation:
`f{0} g{1} = 10`, `f{1} g{2} = 28`, and `f{0} g{2} = -14`. -/
example : ∃ n, ExecutesList 64 program (.init negInst.encode)
    [Signed.encode 10, Signed.encode 28, Signed.encode (-14)] n ∧ n ≤ 118750 := by
  have hrun := executesList_program (t₁ := 1) (t₂ := 1) (w := 64) negInst
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hout : (negInst.queries.map (subsetConvolution negInst.leftFn negInst.rightFn)).map
      Signed.encode =
      [Signed.encode 10, Signed.encode 28, Signed.encode (-14)] := by decide +kernel
  have hbnd : 250 * (negInst.d + 1) ^ 2 *
      (negInst.numEntries + lowCount negInst.d negInst.s +
        negInst.queries.length * highCount (1 + 1) negInst.s) = 118750 := by decide +kernel
  rwa [hout, hbnd] at hrun

/-- Boundary case: empty universe (`d = 0`), empty entries, and empty queries at minimal fitting
word width `w = 10`. -/
def emptyInst : Instance where
  d := 0
  s := 0
  leftEntries := []
  rightEntries := []
  queries := []

example : ∃ n, ExecutesList 6 program (.init emptyInst.encode) [] n ∧ n ≤ 250 := by
  have hw : emptyInst.FitsWidth 6 := ⟨by decide +kernel, by decide +kernel⟩
  have hrun := computesListInTime_program emptyInst 6 hw hw.inputFits
  have hout : (emptyInst.queries.map (coveringProduct emptyInst.leftFn emptyInst.rightFn)).map
      Signed.encode = [] := rfl
  have hbnd : emptyInst.timeBound = 250 := by decide +kernel
  dsimp only at hrun
  rwa [hout, hbnd] at hrun

/-- Boundary case: query with `#C < s` (`|{0}| = 1 < 2`) answered directly from preprocessing. -/
def shortQueryInst : Instance where
  d := 3
  s := 2
  leftEntries := [(∅, 3)]
  rightEntries := [({0}, 4)]
  queries := [{0}]

example : ∃ n, ExecutesList 64 program (.init shortQueryInst.encode)
    [Signed.encode 12] n ∧ n ≤ 40000 := by
  have hw : shortQueryInst.FitsWidth 64 := ⟨by decide +kernel, by decide +kernel⟩
  have hrun := computesListInTime_program shortQueryInst 64 hw hw.inputFits
  have hout : (shortQueryInst.queries.map
      (coveringProduct shortQueryInst.leftFn shortQueryInst.rightFn)).map
      Signed.encode = [Signed.encode 12] := by decide +kernel
  have hbnd : shortQueryInst.timeBound = 40000 := by decide +kernel
  dsimp only at hrun
  rwa [hout, hbnd] at hrun

/-- Nonzero downstream `module`-client composition check: build two nonzero depth-`4` tries via
`exec_buildInputTrie`, frame the first across the second via `HoldsTrie.congr_below` and
`HoldsTrie.mono_bound`, and evaluate `solveFromTries` via
`exec_solveFromTries_subsetConvolution`. -/
example :
    let esF : List (Finset (Fin 4) × ℤ) := [({0}, 2), ({1}, 3)]
    let esG : List (Finset (Fin 4) × ℤ) := [({1}, 5), ({2}, 7)]
    let qs : List (Finset (Fin 4)) := [{0, 1}, {1, 2}]
    let rawWords : List ℕ := encodeEntries esF ++ encodeEntries esG ++ qs.map setMask
    let x₀ : Data numRegs :=
      ((((((Data.init rawWords : Data numRegs).set Reg.dim 4).set Reg.thresh 1).set
        Reg.entryPtr 1).set Reg.entryCount 2).set Reg.free 12).set Reg.queryCount 2
    ∃ y, ExecWithin 64
        (.seq buildInputTrie
          (.seq (((Code.op (.copy Reg.trieF Reg.builtRoot)).seq
              (.op (.const Reg.entryPtr 5))).seq
            (.op (.const Reg.queryPtr 9)))
            (.seq buildInputTrie
              (.seq (.op (.copy Reg.trieG Reg.builtRoot)) solveFromTries))))
        x₀ y 60000 ∧
      outputList y.mem (y.regs Reg.outPtr) = [Signed.encode 10, Signed.encode 21] := by
  intro esF esG qs rawWords x₀
  have hx₀_f0 : x₀.mem 1 = setMask esF[0].1 ∧ x₀.mem 2 = Signed.encode esF[0].2 := by decide +kernel
  have hx₀_f1 : x₀.mem 3 = setMask esF[1].1 ∧ x₀.mem 4 = Signed.encode esF[1].2 := by decide +kernel
  have hmemF : ∀ p (hp : p < esF.length),
      x₀.mem (1 + 2 * p) = setMask esF[p].1 ∧
      x₀.mem (1 + 2 * p + 1) = Signed.encode esF[p].2 := by
    intro p hp
    rcases p with _ | _ | p
    · exact hx₀_f0
    · exact hx₀_f1
    · simp [esF] at hp
  have hx₀_mem5 : x₀.mem 5 = setMask esG[0].1 ∧ x₀.mem 6 = Signed.encode esG[0].2 := by
    decide +kernel
  have hx₀_mem7 : x₀.mem 7 = setMask esG[1].1 ∧ x₀.mem 8 = Signed.encode esG[1].2 := by
    decide +kernel
  have hx₀_q0 : x₀.mem 9 = setMask qs[0] := by decide +kernel
  have hx₀_q1 : x₀.mem 10 = setMask qs[1] := by decide +kernel
  have hx₀_dim : x₀.regs Reg.dim = 4 := by decide
  have hx₀_thresh : x₀.regs Reg.thresh = 1 := by decide
  have hx₀_ep : x₀.regs Reg.entryPtr = 1 := by decide
  have hx₀_ec : x₀.regs Reg.entryCount = esF.length := by decide
  have hx₀_fr : x₀.regs Reg.free = 12 := by decide
  have hx₀_qc : x₀.regs Reg.queryCount = qs.length := by decide
  obtain ⟨u₁, free₁, fnF, he₁, hsav₁, hfr₁, hlo₁, hhi₁, htrF, hf_eq, hframe₁, hreg₁⟩ :=
    exec_buildInputTrie (w := 64) (d := 4) (entryPtr := 1) (free := 12) (W := 17) esF x₀
      hx₀_dim hx₀_ep hx₀_ec hx₀_fr (by decide) (by decide) hmemF (by decide)
      (by decide +kernel) (by decide +kernel)
  let u₂ := ((u₁.set Reg.trieF (u₁.regs Reg.builtRoot)).set Reg.entryPtr 5).set Reg.queryPtr 9
  have he_prep : ExecWithin (B := .standard) 64
      (((Code.op (.copy Reg.trieF Reg.builtRoot)).seq
        (.op (.const Reg.entryPtr 5))).seq
        (.op (.const Reg.queryPtr 9))) u₁ u₂ 3 :=
    ((Exec.copy.within.seq (Exec.const (by decide)).within).seq (Exec.const (by decide)).within)
  have hmemG : ∀ p (hp : p < esG.length),
      u₂.mem (5 + 2 * p) = setMask esG[p].1 ∧
      u₂.mem (5 + 2 * p + 1) = Signed.encode esG[p].2 := by
    intro p hp
    have hlt12 : 5 + 2 * p + 1 < 12 := by simp [esG] at hp; omega
    have hm1 : u₂.mem (5 + 2 * p) = x₀.mem (5 + 2 * p) :=
      hframe₁ _ (Or.inl (by omega))
    have hm2 : u₂.mem (5 + 2 * p + 1) = x₀.mem (5 + 2 * p + 1) :=
      hframe₁ _ (Or.inl hlt12)
    rw [hm1, hm2]
    rcases p with _ | _ | p
    · exact hx₀_mem5
    · exact hx₀_mem7
    · simp [esG] at hp
  have hf_free₂ : Fits 64 (free₁ + 2 + 2 * 4 * esG.length) := by
    have : free₁ + 2 + 2 * 4 * esG.length ≤ 50 := by simp [esF, esG] at hhi₁ ⊢; omega
    exact (by decide : Fits 64 50).of_le this
  obtain ⟨u₃, free₂, fnG, he₂, hsav₂, hfr₂, hlo₂, hhi₂, htrG, hg_eq, hframe₂, hreg₂⟩ :=
    exec_buildInputTrie (w := 64) (d := 4) (entryPtr := 5) (free := free₁) (W := 17) esG u₂
      (by simpa [u₂, hx₀_dim] using hreg₁ Reg.dim (by decide))
      rfl
      (by simpa [u₂, hx₀_ec, esF, esG] using hreg₁ Reg.entryCount (by decide))
      (by simpa [u₂] using hfr₁)
      (by omega)
      (by simp [esG]; omega)
      hmemG (by decide) (by decide +kernel) hf_free₂
  let u₄ := u₃.set Reg.trieG (u₃.regs Reg.builtRoot)
  have he_cpG : ExecWithin (B := .standard) 64 (.op (.copy Reg.trieG Reg.builtRoot)) u₃ u₄ 1 :=
    Exec.copy.within
  have htrF' : HoldsTrie u₄.mem free₂ 4 12 fnF :=
    (htrF.congr_below fun a ha => hframe₂ a (Or.inl ha)).mono_bound (by omega)
  have hq_mem : ∀ j (hj : j < qs.length), u₄.mem (9 + j) = setMask qs[j] := by
    intro j hj
    have hm : u₄.mem (9 + j) = x₀.mem (9 + j) := by
      have hlt1 : 9 + j < 12 := by simp [qs] at hj; omega
      exact (hframe₂ _ (Or.inl (by omega))).trans (hframe₁ _ (Or.inl hlt1))
    rw [hm]
    rcases j with _ | _ | j
    · exact hx₀_q0
    · exact hx₀_q1
    · simp [qs] at hj
  have hf_sp : Fits 64 (solveSpace free₂ 4 1 qs.length (highCount (1 + 1) 1)) := by
    have hle : free₂ ≤ 50 := by simp [esF, esG] at hhi₁ hhi₂; omega
    exact (by decide +kernel : Fits 64 (solveSpace 50 4 1 2 (highCount 2 1))).of_le
      (by dsimp [solveSpace, qs]; omega)
  obtain ⟨y, he_solve, hy_out, -, -⟩ :=
    exec_solveFromTries_subsetConvolution (w := 64) (d := 4) (s := 1) (t₁ := 1) (t₂ := 1)
      (baseFree := free₂) (rootF := 12) (rootG := free₁) (qPtr := 9) (W := 17)
      (f := evalEntries esF) (g := evalEntries esG) (Cs := qs) u₄
      (by simpa [u₄, u₂, hx₀_dim] using
        (hreg₂ Reg.dim (by decide)).trans (hreg₁ Reg.dim (by decide)))
      (by simpa [u₄, u₂, hx₀_thresh] using
        (hreg₂ Reg.thresh (by decide)).trans (hreg₁ Reg.thresh (by decide)))
      (by simpa [u₄] using hfr₂)
      (by omega)
      (by simpa [u₄, u₂, hsav₁] using hreg₂ Reg.trieF (by decide))
      (by simp [u₄, hsav₂])
      (by simpa [u₄, u₂] using hreg₂ Reg.queryPtr (by decide))
      (by simpa [u₄, u₂, hx₀_qc] using
        (hreg₂ Reg.queryCount (by decide)).trans (hreg₁ Reg.queryCount (by decide)))
      (by simp [qs] at hlo₁ hlo₂ ⊢; omega)
      hq_mem htrF' htrG hf_eq hg_eq
      (fun S => (natAbs_evalEntries_le esF S).trans (by decide))
      (fun S => (natAbs_evalEntries_le esG S).trans (by decide))
      (evalEntries_ranked (by decide)) (evalEntries_ranked (by decide))
      (by decide) (by decide) hf_sp (by decide +kernel)
  have hconv : (qs.map (subsetConvolution (evalEntries esF) (evalEntries esG))).map
      Signed.encode = [Signed.encode 10, Signed.encode 21] := by decide +kernel
  have htime : 2 * (23 * 4 + 40) + 11 + (3 + (2 * (23 * 4 + 40) + 11 +
      (1 + 200 * (4 + 1) ^ 2 * (lowCount 4 1 + qs.length * highCount (1 + 1) 1)))) ≤ 60000 := by
    decide +kernel
  exact ⟨y, (he₁.seq (he_prep.seq (he₂.seq (he_cpG.seq he_solve)))).mono htime,
    hy_out.trans hconv⟩

end CslibFrontierTests.Algorithms.Lean.TrimmedYates
