/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceWrites

/-!
# Clean double-collect snapshot theorem (`Lemma 3.1`)

Proves `SnapshotTrace.memSnapshot_eq_of_clean_double_collect`
([AfekAttiyaDolevGafniMerrittShavit1993], Lemma 3.1, p. 9), shared by `TracePreservation` and
re-exported through `AtomicSnapshot`.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.memSnapshot_eq_of_clean_double_collect`: clean
  double-collect snapshot theorem (`Lemma 3.1`).
-/

public section

namespace Cslib.Distributed.SetAgreement

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.1, p. 9][AfekAttiyaDolevGafniMerrittShavit1993]): suppose for each process
`j : P`, `a j = (τ.stateAt (tA j)).reg j` and `b j = (τ.stateAt (tB j)).reg j` with
`tA j ≤ u ≤ w ≤ tB j ≤ τ.events.length`. If `∀ j, (a j).seq = (b j).seq`, then for every state index
`v` with `u ≤ v ≤ w`, `memSnapshot (τ.stateAt v).reg = fun j => (b j).data`. -/
theorem memSnapshot_eq_of_clean_double_collect (τ : SnapshotTrace ord dInit)
    {tA tB : P → ℕ} {u w : ℕ}
    (htA : ∀ j, tA j ≤ u) (huw : u ≤ w) (htB : ∀ j, w ≤ tB j)
    (hbound : ∀ j, tB j ≤ τ.events.length)
    (hseq : ∀ j, ((τ.stateAt (tA j)).reg j).seq = ((τ.stateAt (tB j)).reg j).seq)
    {v : ℕ} (huv : u ≤ v) (hvw : v ≤ w) :
    memSnapshot (τ.stateAt v).reg = fun j => ((τ.stateAt (tB j)).reg j).data := by
  funext j
  have hle : tA j ≤ tB j := le_trans (htA j) (le_trans huw (htB j))
  have hreg := (τ.seq_mono_and_const_of_eq j hle (hbound j)).2 (hseq j) v
    (le_trans (htA j) huv) (le_trans hvw (htB j))
  exact congrArg SnapshotReg.data hreg

end SnapshotTrace

end Cslib.Distributed.SetAgreement
