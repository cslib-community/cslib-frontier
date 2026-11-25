/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Table
import Mathlib.Data.List.GetD

/-!
# Constructive row witnesses for table contraction

Section 5.3 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 12–13,
retains rows with at most one changed internal coordinate. The witness routine below scans
the actual original rows. Zero and one deviations respectively give equality and a unique
changed actual port, including at unbounded finite arity.
-/

public section

namespace Cslib.Logic.PL.CSP.Table

/-- Recover a local original-row witness by scanning the explicit stored table. -/
@[expose] def contractWitness (table : Table) (reference : List Bool) (positions : List ℕ)
    (row : List Bool) : Option (List Bool) :=
  table.rows.find? fun old => decide (deviations reference old positions ≤ 1 ∧
    project old (outsidePositions reference.length positions) ++
      [decide (deviations reference old positions = 1)] = row)

/-- Every accepted contracted row has an executable original stored-row witness. -/
theorem contractWitness_spec {table : Table} {reference row : List Bool} {positions : List ℕ}
    (hc : canContract table reference positions = true)
    (hr : (contract table reference positions).sem row = true) :
    ∃ old, contractWitness table reference positions row = some old ∧ old ∈ table.rows ∧
      deviations reference old positions ≤ 1 ∧
      project old (outsidePositions reference.length positions) ++
        [decide (deviations reference old positions = 1)] = row := by
  obtain ⟨old, hm, hd, he⟩ := (sem_contract_eq_true hc).mp hr
  cases hw : contractWitness table reference positions row with
  | none => exact (List.find?_eq_none.mp hw old hm (decide_eq_true ⟨hd, he⟩)).elim
  | some found =>
    have h := List.find?_some hw
    exact ⟨found, rfl, List.mem_of_find?_eq_some hw, of_decide_eq_true h⟩

/-- Zero internal deviations means agreement at every selected original coordinate. -/
theorem deviations_eq_zero_iff (reference row : List Bool) (positions : List ℕ) :
    deviations reference row positions = 0 ↔
      ∀ j ∈ positions, row.getD j false = reference.getD j false := by
  simp [deviations, List.countP_eq_zero]

/-- Exactly one deviation gives a unique changed original coordinate; all other selected
coordinates agree. This uses the actual position list, not an interval of variable names. -/
theorem deviations_eq_one {reference row : List Bool} {positions : List ℕ}
    (h : deviations reference row positions = 1) :
    ∃ j ∈ positions, row.getD j false ≠ reference.getD j false ∧
      ∀ k ∈ positions, k ≠ j → row.getD k false = reference.getD k false := by
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp (List.countP_eq_length_filter.symm.trans h)
  obtain ⟨hjp, hjn⟩ := List.mem_filter.mp (hj ▸ List.mem_singleton_self j)
  refine ⟨j, hjp, by simpa using hjn, fun k hkp hkj => by_contra fun hne => hkj ?_⟩
  exact List.mem_singleton.mp (hj ▸ List.mem_filter.mpr ⟨hkp, by simpa using hne⟩)

/-- Reading a projected coordinate at its actual index recovers the original bit. -/
theorem project_getD_idxOf (row : List Bool) (positions : List ℕ) {j : ℕ}
    (hj : j ∈ positions) : (project row positions).getD (positions.idxOf j) false =
      row.getD j false := by
  simp [project, List.getD_eq_getElem?_getD, hj]

/-- A full-width row is determined by its outside projection and its internal bits. -/
theorem eq_of_project_eq_of_eqOn {reference row : List Bool} {positions : List ℕ}
    (hl : row.length = reference.length)
    (hp : project row (outsidePositions reference.length positions) =
      project reference (outsidePositions reference.length positions))
    (hi : ∀ j ∈ positions, row.getD j false = reference.getD j false) : row = reference := by
  refine List.ext_getElem hl fun j hj hr => ?_
  suffices row.getD j false = reference.getD j false by
    simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hr] using this
  by_cases hm : j ∈ positions
  · exact hi j hm
  · have ho : j ∈ outsidePositions reference.length positions := by simp [outsidePositions, hm, hr]
    simpa only [project_getD_idxOf _ _ ho] using
      congrArg (fun r => r.getD ((outsidePositions reference.length positions).idxOf j) false) hp

/-- The actual last connector bit determines the exact number of internal deviations in the
computed row witness; its outside projection is precisely the supplied finite row. -/
theorem contractWitness_projection {table : Table} {reference current : List Bool}
    {positions : List ℕ} {bit : Bool} (hc : canContract table reference positions = true)
    (hr : (contract table reference positions).sem
      (project current (outsidePositions reference.length positions) ++ [bit]) = true) :
    ∃ old, contractWitness table reference positions
        (project current (outsidePositions reference.length positions) ++ [bit]) = some old ∧
      table.sem old = true ∧ deviations reference old positions = bit.toNat ∧
      project old (outsidePositions reference.length positions) =
        project current (outsidePositions reference.length positions) := by
  obtain ⟨old, hw, hm, hd, he⟩ := contractWitness_spec hc hr
  obtain ⟨hproj, hbit⟩ := List.append_inj he (by simp [project])
  have hbits := List.singleton_inj.mp hbit
  refine ⟨old, hw, sem_eq_true.mpr ⟨(canContract_eq_true.mp hc).1, hm⟩, ?_, hproj⟩
  cases bit
  · have : deviations reference old positions ≠ 1 := by simpa using hbits
    simp only [Bool.toNat_false]; omega
  · simpa only [decide_eq_true_eq, Bool.toNat_true] using hbits

/-- At connector zero, contraction preserves exactly the feasible rows with the reference
internal bits. All outside coordinates may change arbitrarily. -/
theorem sem_contract_zero_iff {table : Table} {reference current : List Bool}
    {positions : List ℕ} (hc : canContract table reference positions = true)
    (hl : current.length = reference.length)
    (hi : ∀ j ∈ positions, current.getD j false = reference.getD j false) :
    (contract table reference positions).sem
        (project current (outsidePositions reference.length positions) ++ [false]) = true ↔
      table.sem current = true := by
  refine ⟨fun hr => ?_, fun hv => (sem_contract_eq_true hc).mpr ?_⟩
  · obtain ⟨old, _, hv, hd, hp⟩ := contractWitness_projection hc hr
    have hlen : old.length = current.length := by
      rw [(wellFormed_eq_true.mp (sem_eq_true.mp hv).1) old (sem_eq_true.mp hv).2, hl,
        (wellFormed_eq_true.mp (canContract_eq_true.mp hc).1) reference
          (canContract_eq_true.mp hc).2.1]
    exact eq_of_project_eq_of_eqOn hlen (hl ▸ hp)
      (fun j hj => ((deviations_eq_zero_iff ..).mp hd j hj).trans (hi j hj).symm) ▸ hv
  · exact ⟨current, (sem_eq_true.mp hv).2, by simp [(deviations_eq_zero_iff ..).mpr hi]⟩

end Cslib.Logic.PL.CSP.Table
