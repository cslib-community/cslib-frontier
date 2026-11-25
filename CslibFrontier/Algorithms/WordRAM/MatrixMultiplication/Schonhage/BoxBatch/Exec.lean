/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Correctness and charged execution of a native sparse-query batch

The original wanted codes lie below the retained table's end, and answers lie above
the query stack. Each query preserves both the original codes and all earlier answers.
The bound sums actual sparse query allowances and charges six further instructions per
wanted code, plus two for final loop exit. Empty lists execute only that exit.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Persistent ordinary arguments of the reused tile; no execution or resource fields. -/
structure Arguments (L t AA BB D V K : ℕ) (x : Data registers) : Prop where
  /-- Original encoding depth. -/
  levels : x.regs BoxTable.Reg.levels = L
  /-- Original sparse threshold. -/
  threshold : x.regs BoxTable.Reg.threshold = t
  /-- Actual encoding-array length. -/
  span : x.regs BoxTable.Reg.span = 10 ^ L
  /-- Actual left array base. -/
  arrayA : x.regs BoxTable.Reg.arrayA = AA
  /-- Actual right array base. -/
  arrayB : x.regs BoxTable.Reg.arrayB = BB
  /-- Shared directory base. -/
  directory : x.regs BoxTable.Reg.directory = D
  /-- Retained signed value-table base. -/
  values : x.regs BoxTable.Reg.values = V
  /-- Actual compact box count. -/
  count : x.regs BoxTable.Reg.count = K

/-- The actual native batch charge, including every load, store, cursor increment and loop test. -/
@[expose] def queryTime {L : ℕ} (m t : ℕ) (qs : List (OutStr L)) : ℕ :=
  (qs.map fun η => BoxQuery.queryTime m t η + 6).sum + 2

/-- Original addresses cover the reused kernel, batch cursors and their one-past-end values. -/
@[expose] def addressBound (L t AA BB D V K Q O N : ℕ) : ℕ :=
  BoxQuery.queryAddressBound L t AA BB D V K + Q + O + 2 * N + 1

/-- Execute all wanted codes against one actual retained table. The input list may be
empty or contain duplicates. The same final memory stores every answer in order and
preserves source/table readback and all words outside the stack and output intervals. -/
theorem exec_queryProgram {w L m t AA BB D V K A B Q O : ℕ}
    (qs : List (OutStr L)) (x : Data registers) (hx : Arguments L t AA BB D V K x)
    (hnext : x.regs Reg.next = Q) (hstop : x.regs Reg.stop = Q + qs.length)
    (hout : x.regs Reg.output = O)
    (a b : Leaf L → ℤ) (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (hcodes : ∀ i : Fin qs.length, x.mem (Q + i.val) = (PrunedQuery.queryIndex (qs.get i)).val)
    (hK : K = (boxes L m t).card)
    (hAA : AA + 10 ^ L ≤ V + K) (hBB : BB + 10 ^ L ≤ V + K)
    (hDir : D + (m - t + 1) * 10 ^ L ≤ V + K)
    (hQ : Q + qs.length ≤ V + K)
    (hO : V + K + 5 * BoxQuery.stackCapacity L ≤ O)
    (hread : BoxQuery.Readback m t D V AA BB a b x.mem)
    (hfit : Fits (w + 2) (addressBound L t AA BB D V K Q O qs.length))
    (hmag : GenericRAM.Signed.Fits w (BoxQuery.magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) queryProgram x y (queryTime m t qs) ∧
      Arguments L t AA BB D V K y ∧ y.regs Reg.next = Q + qs.length ∧
      y.regs Reg.stop = Q + qs.length ∧ y.regs Reg.output = O + qs.length ∧
      (∀ i : Fin qs.length, y.mem (O + i.val) =
        Signed.encode (BoxQuery.queryValue m t (qs.get i) a b)) ∧
      BoxQuery.Readback m t D V AA BB a b y.mem ∧
      (∀ p, ¬((V + K ≤ p ∧ p < V + K + 5 * BoxQuery.stackCapacity L) ∨
        (O ≤ p ∧ p < O + qs.length)) → y.mem p = x.mem p) := by
  induction qs generalizing x Q O with
  | nil =>
    exact ⟨x, ExecWithin.loop_exit (by simp [Cond.Holds, hnext, hstop]), hx,
      by simpa using hnext, hstop, by simpa using hout, fun i => Fin.elim0 i, hread,
      fun _ _ => rfl⟩
  | cons η qs ih =>
    have hfQ : Fits (w + 2) (Q + 1) :=
      hfit.of_le (by unfold addressBound; simp only [List.length_cons]; omega)
    have hfO : Fits (w + 2) (O + 1) := hfit.of_le (by unfold addressBound; omega)
    have hload : x.mem Q = (PrunedQuery.queryIndex η).val := by simpa using hcodes ⟨0, by simp⟩
    obtain ⟨z, hbdy, zx, zn, zs, zo, zmO, zframe, zr⟩ :
        ∃ z, ExecWithin (w + 2) body x z (BoxQuery.queryTime m t η + 4) ∧
          Arguments L t AA BB D V K z ∧ z.regs Reg.next = Q + 1 ∧
          z.regs Reg.stop = (Q + 1) + qs.length ∧ z.regs Reg.output = O + 1 ∧
          z.mem O = Signed.encode (BoxQuery.queryValue m t η a b) ∧
          (∀ p, ¬((V + K ≤ p ∧ p < V + K + 5 * BoxQuery.stackCapacity L) ∨ p = O) →
            z.mem p = x.mem p) ∧
          BoxQuery.Readback m t D V AA BB a b z.mem := by
      unfold body loadQuery finishQuery
      wram_exec * [hload]
      wram_call (BoxQuery.exec_queryProgram _ η (hη η (by simp)) a b ha hb
        (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp)
        (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
        hK hAA hBB hDir (by simpa only [Data.set_mem] using hread)
        (hfit.of_le (by unfold addressBound; omega)) hmag)
        with v ⟨vp, _, va, vr, vf⟩
      have vn : v.regs Reg.next = Q :=
        (‹ExecWithin _ _ _ v _›.regs_eq query_preserves.1).trans (by regs_frame)
      have vo : v.regs Reg.output = O :=
        (‹ExecWithin _ _ _ v _›.regs_eq query_preserves.2.2).trans (by regs_frame)
      have vs : v.regs Reg.stop = Q + (η :: qs).length :=
        (‹ExecWithin _ _ _ v _›.regs_eq query_preserves.2.1).trans (by regs_frame)
      wram_exec [vn, vo, va, vp.one]
      refine ⟨by regs_frame, by wram_simp, ?_, by wram_simp, by wram_simp, ?_, ?_⟩
      · wram_simp [vs]; simp only [List.length_cons]; omega
      · exact fun p hp => by wram_simp; exact vf p (by omega)
      · exact vr.transport hAA hBB hDir (by rw [hK]) fun p hp => by wram_simp
    have zcodes (i : Fin qs.length) : z.mem (Q + 1 + i.val) =
        (PrunedQuery.queryIndex (qs.get i)).val := by
      rw [zframe _ (by have := i.isLt; simp only [List.length_cons] at hQ; omega)]
      simpa only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hcodes ⟨i.val + 1, by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using i.isLt⟩
    have zfit : Fits (w + 2) (addressBound L t AA BB D V K (Q + 1) (O + 1) qs.length) :=
      hfit.of_le (by unfold addressBound; simp only [List.length_cons]; omega)
    obtain ⟨y, hy, yx, yn, ys, yo, yanswers, yr, yf⟩ := ih z zx zn zs zo
      (fun η h => hη η (by simp [h])) zcodes (by simp only [List.length_cons] at hQ; omega)
      (by omega) zr zfit
    refine ⟨y, ?_, yx, ?_, ?_, ?_, ?_, yr, ?_⟩
    · have he := ExecWithin.loop_iter
        (show (Cond.lt Reg.next Reg.stop).Holds x from by
          simp only [Cond.Holds, hnext, hstop, List.length_cons]; omega) hbdy hy
      exact he.mono (by simp only [queryTime, List.map_cons, List.sum_cons]; omega)
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yn
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ys
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yo
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change y.mem (O + 0) = Signed.encode (BoxQuery.queryValue m t η a b)
        rw [Nat.add_zero, yf O (by omega), zmO]
      · simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yanswers j
    · intro p hp
      rw [yf p (by simp only [List.length_cons] at hp ⊢; omega),
        zframe p (by simp only [List.length_cons] at hp ⊢; omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
