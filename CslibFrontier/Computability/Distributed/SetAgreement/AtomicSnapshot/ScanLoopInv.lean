/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TraceWrites

/-!
# Internal double-collect loop invariant

Internal invariant `ScanLoopInv` and per-step preservation lemmas (`readA`, `finishA`, `readB`,
`restart`) for active `scan` executions; never re-exported through `AtomicSnapshot`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotTrace.HasActiveOpId`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv`: active-operation and collect-loop
  invariants.

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv.mono_hi`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv.readA`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv.finishA`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv.readB`,
  `Cslib.Distributed.SetAgreement.SnapshotTrace.ScanLoopInv.restart`: step preservation.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- Whether local state `ps` belongs to an active operation with history index `id`. -/
abbrev HasActiveOpId {P Data : Type*} (ps : ProcSnapshotState P Data) (id : ℕ) : Prop :=
  (∃ st, ps = .scanning st ∧ st.opId = id) ∨
    (∃ val snap, ps = .readyToWrite id val snap)

omit [Fintype P] [DecidableEq P] in
/-- Uniqueness of active operation ID carried by `ps`. -/
theorem active_opId_unique {ps : ProcSnapshotState P Data} {id₁ id₂ : ℕ}
    (h₁ : HasActiveOpId ps id₁) (h₂ : HasActiveOpId ps id₂) : id₁ = id₂ := by
  rcases h₁ with ⟨st₁, rfl, rfl⟩ | ⟨v₁, sn₁, rfl⟩ <;>
    rcases h₂ with ⟨st₂, hp₂, rfl⟩ | ⟨v₂, sn₂, hp₂⟩ <;> cases hp₂ <;> rfl

/-- Double-collect loop invariant for active scan `st` over trace window `[lo, hi]`
(typically instantiated with `lo = τ.lastIdleStep i hi`). -/
@[expose]
def ScanLoopInv (τ : SnapshotTrace ord dInit) (lo hi : ℕ)
    (st : ActiveScan P Data) : Prop :=
  ∃ iterStart, lo + 1 ≤ iterStart ∧ iterStart ≤ hi ∧
    (∀ k ∈ st.moved, ∃ w₁, lo + 1 ≤ w₁ ∧ w₁ < iterStart ∧ τ.isWriteStep k w₁) ∧
    (st.phase = .collectA →
      ∀ k, k ∉ st.rem →
        ∃ tA, iterStart ≤ tA ∧ tA ≤ hi ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
    (st.phase = .collectB →
      ∃ u, iterStart ≤ u ∧ u ≤ hi ∧
        (∀ k, ∃ tA, iterStart ≤ tA ∧ tA ≤ u ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
        (∀ k, k ∉ st.rem →
          ∃ tB, u ≤ tB ∧ tB ≤ hi ∧ st.collectBVal k = (τ.stateAt tB).reg k))

/-- `ScanLoopInv` is monotone in its upper trace-step bound `hi`. -/
theorem ScanLoopInv.mono_hi {τ : SnapshotTrace ord dInit} {lo hi hi' : ℕ}
    {st : ActiveScan P Data} (hle : hi ≤ hi') (h : ScanLoopInv τ lo hi st) :
    ScanLoopInv τ lo hi' st := by
  obtain ⟨iterS, hlo, hhi, hmov, hcA, hcB⟩ := h
  refine ⟨iterS, hlo, hhi.trans hle, hmov, fun hA k hk => ?_, fun hB => ?_⟩
  · obtain ⟨tA, a1, a2, a3⟩ := hcA hA k hk
    exact ⟨tA, a1, a2.trans hle, a3⟩
  · obtain ⟨u, u1, u2, ha, hb⟩ := hcB hB
    exact ⟨u, u1, u2.trans hle, ha, fun k hk =>
      let ⟨tB, b1, b2, b3⟩ := hb k hk; ⟨tB, b1, b2.trans hle, b3⟩⟩

/-- `ScanLoopInv` step: reading register `j` during `collectA`. -/
theorem ScanLoopInv.readA {τ : SnapshotTrace ord dInit} {lo t : ℕ}
    {st : ActiveScan P Data} {j : P} {rest : List P}
    (hph : st.phase = .collectA) (hrem : st.rem = j :: rest)
    (h : ScanLoopInv τ lo t st) :
    ScanLoopInv τ lo (t + 1)
      { st with phase := .collectA, rem := rest,
                collectAVal := Function.update st.collectAVal j ((τ.stateAt t).reg j) } := by
  obtain ⟨iterS, hi₁, hi₂, hmov, hcA, _⟩ := h
  refine ⟨iterS, hi₁, by omega, hmov, fun _ k hk => ?_, fun hB => by cases hB⟩
  dsimp only at hk ⊢
  by_cases hkj : k = j
  · subst hkj; exact ⟨t, hi₂, by omega, Function.update_self _ _ _⟩
  · obtain ⟨tA, a1, a2, a3⟩ := hcA hph k (by simp [hrem, hkj, hk])
    exact ⟨tA, a1, by omega, (Function.update_of_ne hkj _ _).trans a3⟩

/-- `ScanLoopInv` step: transitioning from completed `collectA` (`rem = []`) to `collectB`. -/
theorem ScanLoopInv.finishA {τ : SnapshotTrace ord dInit} {lo t : ℕ}
    {st : ActiveScan P Data} (hph : st.phase = .collectA) (hrem : st.rem = [])
    (h : ScanLoopInv τ lo t st) :
    ScanLoopInv τ lo (t + 1) { st with phase := .collectB, rem := ord.elems } := by
  obtain ⟨iterS, hi₁, hi₂, hmov, hcA, _⟩ := h
  refine ⟨iterS, hi₁, by omega, hmov, (fun hA => by cases hA), fun _ =>
    ⟨t, hi₂, by omega, fun k => hcA hph k (by simp [hrem]),
      fun k hk => absurd (ord.complete k) hk⟩⟩

/-- `ScanLoopInv` step: reading register `j` during `collectB`. -/
theorem ScanLoopInv.readB {τ : SnapshotTrace ord dInit} {lo t : ℕ}
    {st : ActiveScan P Data} {j : P} {rest : List P}
    (hph : st.phase = .collectB) (hrem : st.rem = j :: rest)
    (h : ScanLoopInv τ lo t st) :
    ScanLoopInv τ lo (t + 1)
      { st with phase := .collectB, rem := rest,
                collectBVal := Function.update st.collectBVal j ((τ.stateAt t).reg j) } := by
  obtain ⟨iterS, hi₁, hi₂, hmov, _, hcB⟩ := h
  obtain ⟨u, hu₁, hu₂, ha_all, hb_rem⟩ := hcB hph
  refine ⟨iterS, hi₁, by omega, hmov, (fun hA => by cases hA), fun _ =>
    ⟨u, hu₁, by omega, ha_all, fun k hk => ?_⟩⟩
  dsimp only at hk ⊢
  by_cases hkj : k = j
  · subst hkj; exact ⟨t, hu₂, by omega, Function.update_self _ _ _⟩
  · obtain ⟨tB, b1, b2, b3⟩ := hb_rem k (by simp [hrem, hkj, hk])
    exact ⟨tB, b1, by omega, (Function.update_of_ne hkj _ _).trans b3⟩

/-- `ScanLoopInv` step: adding all changed processes to `moved` and restarting `collectA`. -/
theorem ScanLoopInv.restart {τ : SnapshotTrace ord dInit} {lo t : ℕ}
    (ht : t ≤ τ.events.length) {st : ActiveScan P Data}
    (hph : st.phase = .collectB) (hrem : st.rem = [])
    (h : ScanLoopInv τ lo t st) :
    ScanLoopInv τ lo (t + 1)
      { st with
          moved := st.moved ∪ univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq
          phase := .collectA
          rem := ord.elems } := by
  obtain ⟨iterS, hi₁, hi₂, hmov, _, hcB⟩ := h
  obtain ⟨u, hu₁, hu₂, ha_all, hb_rem⟩ := hcB hph
  refine ⟨t + 1, by omega, le_rfl, fun k hk => ?_,
    fun _ k hk => absurd (ord.complete k) hk, fun hB => by cases hB⟩
  rcases mem_union.mp hk with hk_old | hk_new
  · obtain ⟨w₁, h1, h2, h3⟩ := hmov k hk_old
    exact ⟨w₁, h1, by omega, h3⟩
  · obtain ⟨tA, htA₁, htA₂, htA_eq⟩ := ha_all k
    obtain ⟨tB, htB₁, htB₂, htB_eq⟩ := hb_rem k (by simp [hrem])
    obtain ⟨w₁, hw₁_lo, hw₁_hi, hw₁_w⟩ := τ.exists_writeStep_of_seq_ne k (htA₂.trans htB₁)
      (htB₂.trans ht) (htA_eq ▸ htB_eq ▸ (mem_filter.mp hk_new).2)
    exact ⟨w₁, by omega, by omega, hw₁_w⟩

end SnapshotTrace

end Cslib.Distributed.SetAgreement
