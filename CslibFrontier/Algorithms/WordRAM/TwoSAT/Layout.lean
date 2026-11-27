/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.CSR
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Defs
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Data.List.GetD

/-!
# Scratch register layout and encoded-clause memory invariants

Internal layout definitions, register-disjointness tactic macros, and `ClauseMemAt` readback lemmas
for the Word-RAM 2-SAT solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

namespace Reg

/-- Constant `2`. -/
abbrev cTwo : Fin 28 := ⟨2, by decide⟩
/-- Variable count `G.n`. -/
abbrev nv : Fin 28 := ⟨4, by decide⟩
/-- Clause count `G.φ.length`. -/
abbrev mClauses : Fin 28 := ⟨5, by decide⟩

end Reg

/-- Discharge register inequality goals on `Fin 28`. -/
scoped macro (name := regNe) "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cTwo, cThree, nv, mClauses, nVerts, outBase, offB,
      edgeB, visB, finB, stkB, curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt,
      compIdxReg, oldFinReg, uReg, vReg, jReg, jEndReg, addr] at *
    omega))

/-- Rewrite register reads past non-overlapping register/memory updates. -/
scoped macro (name := regsLt) "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

/-- Normalize memory reads across `Data.set` and `Data.write`. -/
scoped macro (name := memUpd) "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

namespace Instance

theorem fits_of_le {G : Instance} {w x : ℕ} (hfit : Fits w G.wordBound)
    (hle : x ≤ G.wordBound) : Fits w x :=
  hfit.of_le hle

/-- Base address of the `DFS` scratch layout right after the output buffer. -/
@[expose] def workBase (G : Instance) : ℕ := G.outAddrBase + G.n + 2

end Instance

theorem length_answerWords_le (G : Instance) : (answerWords G).length ≤ G.n + 1 := by
  unfold answerWords
  cases solveFin G.n G.φ <;> simp [encodeAssignment]

/-- Contiguous clause-encoding readback invariant starting at address `p`. -/
@[expose] def ClauseMemAt {n : ℕ} (mem : ℕ → ℕ) (p : ℕ) (cs : CNF (Fin n)) : Prop :=
  let ws := cs.flatMap (encodeClauseBy Fin.val)
  ∀ k (hk : k < ws.length), mem (p + k) = ws[k]


theorem clauseMemAt_init (G : Instance) :
    ClauseMemAt (Data.init G.encode : Data 28).mem 3 G.φ := by
  intro k hk
  have h1 : 3 + k = (k + 2) + 1 := by omega
  rw [h1, Data.init_mem_succ]
  have hlen : k + 2 < G.encode.length := by
    simp only [Instance.encode, List.length_cons]; omega
  rw [List.getD_eq_getElem _ 0 hlen]
  simp [Instance.encode]

theorem clauseMemAt_cons {n : ℕ} {mem : ℕ → ℕ} {p : ℕ} {c : Clause (Fin n)}
    {cs : CNF (Fin n)} (h : ClauseMemAt mem p (c :: cs)) :
    mem p = c.length ∧
      (∀ i (hi : i < c.length), mem (p + 1 + i) = litCodeBy Fin.val c[i]) ∧
      ClauseMemAt mem (p + 1 + c.length) cs := by
  refine ⟨?_, fun i hi => ?_, fun k hk => ?_⟩
  · have h0 := h 0 (by simp [encodeClauseBy])
    simpa [encodeClauseBy] using h0
  · have hi' : i + 1 < ((c :: cs).flatMap (encodeClauseBy Fin.val)).length := by
      simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]
      omega
    have h1 := h (i + 1) hi'
    rw [show p + (i + 1) = p + 1 + i by omega] at h1
    rw [h1]
    simp only [List.flatMap_cons, encodeClauseBy, List.cons_append, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simp [hi])]
    simp
  · have hk' : c.length + 1 + k < ((c :: cs).flatMap (encodeClauseBy Fin.val)).length := by
      simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]
      omega
    have h2 := h (c.length + 1 + k) hk'
    rw [show p + (c.length + 1 + k) = p + 1 + c.length + k by omega] at h2
    rw [h2]
    simp only [List.flatMap_cons]
    rw [List.getElem_append_right (by simp [length_encodeClauseBy])]
    simp [length_encodeClauseBy]


end Cslib.Algorithms.WordRAM.TwoSAT
