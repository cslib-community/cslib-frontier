/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
public import CslibFrontier.Foundations.Data.Nat.WeightedIndex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Space for scanning a row of integer weights

A native machine selects the interval containing a binary label when the weights are available
one at a time from a column counter and the read-only input. It holds the row width, the current
column and the residual label. When the residual is smaller than the current weight, the machine
stops at that column. Exhausting all columns returns the width.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.scanWeightedRow_inSpace` proves the common space bound
  for selection from an implicitly given row.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

open Cslib Finset

/-- The row width, next column to inspect, and label remaining after the preceding columns. -/
private structure RowCursor where
  width : ℕ
  column : ℕ
  remaining : ℕ

private enc_structure encRowCursor : RowCursor logspace where
  width : encNat, column : encNat, remaining : encNat

private def consume (p : RowCursor × ℕ) : Option RowCursor :=
  if decide (p.1.remaining < p.2) then none
  else some ⟨p.1.width, p.1.column + 1, p.1.remaining - p.2⟩

private theorem consume_inSpace :
    ComputableInSpace consume (encPair encRowCursor encNat) (encOption encRowCursor)
      (fun p => (encPair encRowCursor encNat p).length) := by
  have hc := fst encRowCursor encNat
  have hw := snd encRowCursor encNat
  have hr := encRowCursor_remaining_budget hc
  exact budget_ite (budget_natLt hr hw) (budget_const none)
    (budget_optionSome (encRowCursor_mk_budget (encRowCursor_width_budget hc)
      (budget_natSucc (encRowCursor_column_budget hc)) (budget_natSub hr hw)))

/-- Selecting a column from binary weights computed on demand fits the common workspace
of the row width, the label, and the column-weight reader. The reader receives a binary column
counter and the original read-only input. The budget covers the logarithm of the input length. -/
theorem scanWeightedRow_inSpace {α : Type} {enc : α ↪ List Bool}
    {width label : α → ℕ} {weight : ℕ × α → ℕ} {S : α → ℕ}
    (hn : ComputableInSpace width enc encNat S) (hx : ComputableInSpace label enc encNat S)
    (hw : ComputableInSpace weight (encPair encNat enc) encNat
      fun p => (encNat p.1).length + S p.2)
    (hlog : ∀ a, Nat.log2 (enc a).length ≤ S a) :
    ComputableInSpace (fun a => scanWeightedRow (width a) (fun i => weight (i, a)) (label a))
      enc encNat S := by
  let T (q : RowCursor × α) := (encRowCursor q.1).length + S q.2
  let step (q : RowCursor × α) : Option RowCursor :=
    if decide (q.1.column < q.1.width) then consume (q.1, weight (q.1.column, q.2)) else none
  have hreg : ComputableInSpace (fun q : RowCursor × α => q.1) (encPair encRowCursor enc)
      encRowCursor T :=
    ((ComputableInLogSpace.fst encRowCursor enc).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)).mono_le fun q => Nat.add_le_add_left (hlog q.2) _
  have hweight : ComputableInSpace (fun q : RowCursor × α => weight (q.1.column, q.2))
      (encPair encRowCursor enc) encNat T :=
    hw.comp_logSpace_context (f := fun q : RowCursor × α => (q.1.column, q.2))
    (by fun_prop) (.of_le fun q => by
      simp only [encRowCursor_apply, encRowCursorFields, length_encPair]; omega) hlog
  have hstep : ComputableInSpace step (encPair encRowCursor enc) (encOption encRowCursor) T :=
    budget_ite (budget_natLt (encRowCursor_column_budget hreg) (encRowCursor_width_budget hreg))
      (budget_comp_linear consume_inSpace (budget_prod hreg hweight)) (budget_const none)
  let before (a : α) (j : ℕ) := ∑ i ∈ range j, weight (i, a)
  let cursor (a : α) (j : ℕ) := RowCursor.mk (width a) j (label a - before a j)
  let result (a : α) := scanWeightedRow (width a) (fun i => weight (i, a)) (label a)
  have hspec (a : α) := scanWeightedRow_spec (width a) (fun i => weight (i, a)) (label a)
  obtain ⟨cn, hcn⟩ := hn.length_le
  obtain ⟨cx, hcx⟩ := hx.length_le
  have hRun := loopWith cursor result (encRowCursor_mk_budget hn (budget_const 0) hx) hstep
    (fun a => by simp [cursor, before]) (fun a j hj => ?_) (fun a => ?_)
    (B := fun a => (4 * cn + 2 * cx + 6) * (S a + 1)) (fun a j hj => ?_)
  · refine (encRowCursor_column_budget hRun).weaken ⟨4 * cn + 2 * cx + 8, fun a => ?_⟩
    dsimp only
    nlinarith [hlog a]
  · obtain ⟨hle, hlo, _⟩ := hspec a
    change result a ≤ width a at hle
    have hsum := sum_mono_set (fun i => weight (i, a)) (range_mono hj)
    change before a (j + 1) ≤ before a (result a) at hsum
    have hp : before a (j + 1) = before a j + weight (j, a) := sum_range_succ _ _
    have hlo' : before a (result a) ≤ label a := hlo
    have hlt : j < width a := hj.trans_le hle
    have hweight : ¬ label a - before a j < weight (j, a) := by omega
    simp only [step, cursor, decide_eq_true_eq, ite_eq_left hlt, consume, ite_eq_right hweight, hp,
      Nat.sub_add_eq]
  · obtain ⟨_, hlo, hhi⟩ := hspec a
    by_cases h : result a < width a
    · have hl : before a (result a) ≤ label a := hlo
      have hu : label a < before a (result a) + weight (result a, a) := by
        simpa only [before, sum_range_succ] using hhi h
      simp [step, cursor, h, consume, show label a - before a (result a) < weight (result a, a)
        by omega]
    · simp [step, cursor, h]
  · have hj' : j ≤ width a := hj.trans (hspec a).1
    have hi := (length_encNat_mono hj').trans (hcn a)
    have hr := (length_encNat_mono (Nat.sub_le (label a) (before a j))).trans (hcx a)
    simp only [T, cursor, encRowCursor_apply, encRowCursorFields, length_encPair]
    nlinarith [hcn a]

end Turing.MultiTapeTM.ComputableInSpace
