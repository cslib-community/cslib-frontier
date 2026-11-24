/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Emit
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanSet
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native suffix selection

## Main results

* `PrunedQuery.exec_suffix`: one real quotient computation and timestamp insertion,
  within ten native instructions, with its complete memory and register frame.
* `PrunedQuery.exec_selectDigit`, `PrunedQuery.exec_selectDigit_skip`: the native child-digit
  filter shared by the scan and the accumulation.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by shortening a query and attempting its insertion. -/
def SuffixLocal (i : Fin registers) : Prop := EmitLocal i ∨ i = suffix

instance (i : Fin registers) : Decidable (SuffixLocal i) :=
  inferInstanceAs (Decidable (EmitLocal i ∨ i = suffix))

/-- The selected suffix is divided from the actual loaded query, then deduplicated by its
actual memory timestamp. No query-set computation is supplied as a hypothesis. -/
theorem exec_suffix {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (h1 : x.regs one = 1) (h10 : x.regs ten = 10)
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w (putSuffix child) x y 10 ∧ y.regs suffix = shortened child q ∧
      y.regs childCount =
        (if x.mem (x.regs stamps + shortened child q) = x.regs epoch then
          x.regs childCount else x.regs childCount + 1) ∧
      y.mem =
        (if x.mem (x.regs stamps + shortened child q) = x.regs epoch then x.mem else
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch)) ∧
      (∀ i, ¬SuffixLocal i → y.regs i = x.regs i) := by
  have hqfit : Fits w (shortened child q) := hs.of_le (by omega)
  cases child <;> (
    refine WP.exists_execWithin ?_
    unfold putSuffix
    simp only [Bool.false_eq_true, ↓reduceIte]
    wram_exec [hq, h10, (by simpa [shortened] using hqfit : Fits w _)]
    wram_call (exec_emit _ (by wram_simp [h1]) (by wram_simp; simpa [shortened] using hs)
      (by wram_simp; exact hl) (by wram_simp; exact hn)) with y ⟨hc, hm, hf⟩
    wram_simp at hc hm
    refine ⟨by omega, ?_, by simpa [shortened] using hc, by simpa [shortened] using hm,
      fun i hi => ?_⟩
    · simp only [shortened, Bool.false_eq_true, ↓reduceIte]
      regs_frame
    · simp only [SuffixLocal, not_or] at hi
      rw [hf i hi.1]
      wram_simp)

/-- The native child-digit filter, shared by the scan and the accumulation: a selected query
passes the comparison with digit nine, or else the comparison with the current term, and
runs `C`. -/
theorem exec_selectDigit {w T q : ℕ} {C : Code .standard registers} {x y : Data registers}
    (hd : x.regs digit = q % 10) (h9 : x.regs nine = 9) (hsel : selected true (x.regs term) q)
    (hy : ExecWithin w C x y T) :
    ExecWithin w (ram[ if digit = nine then [ ⟪C⟫ ] else [
      if digit = term then [ ⟪C⟫ ] else [ temporary ← temporary ] ] ]) x y (T + 3) := by
  by_cases hfirst : q % 10 = 9
  · refine WP.execWithin ?_
    wram_exec [hd, h9, hfirst]
    wram_call hy
    exact ⟨by omega, trivial⟩
  · have hsecond : q % 10 = x.regs term := hsel.resolve_left hfirst
    refine WP.execWithin ?_
    wram_exec [hd, h9, hfirst, hsecond]
    wram_call hy
    exact ⟨by omega, trivial⟩

/-- An unselected query fails both comparisons of the child-digit filter and runs its no-op. -/
theorem exec_selectDigit_skip {w q : ℕ} {C : Code .standard registers} {x : Data registers}
    (hd : x.regs digit = q % 10) (h9 : x.regs nine = 9)
    (hsel : ¬selected true (x.regs term) q) :
    ExecWithin w (ram[ if digit = nine then [ ⟪C⟫ ] else [
      if digit = term then [ ⟪C⟫ ] else [ temporary ← temporary ] ] ])
      x (x.set temporary (x.regs temporary)) 5 := by
  have hfirst : q % 10 ≠ 9 := fun h => hsel (Or.inl h)
  have hsecond : q % 10 ≠ x.regs term := fun h => hsel (Or.inr h)
  wram_exec [hd, h9, hfirst, hsecond]

/-- Execute the actual query filter and unique insertion. The numerical selection is proved
from the two real digit comparisons; it is not a supplied child-set certificate. -/
theorem exec_scanDispatch {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.regs query = q) (hdigit : x.regs digit = q % 10)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w (scanDispatch child) x y 14 ∧
      y.regs childCount =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          x.regs childCount + 1 else x.regs childCount) ∧
      y.mem =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch) else x.mem) ∧
      (∀ i, ¬SuffixLocal i → y.regs i = x.regs i) := by
  by_cases hsel : selected child (x.regs term) q
  · obtain ⟨y, hy, _, hc, hm, hyr⟩ := exec_suffix child x q hq h1 h10 hs hl hn
    have he : ExecWithin w (scanDispatch child) x y 14 := by
      cases child with
      | false => exact hy.mono (by decide)
      | true => exact (exec_selectDigit hdigit h9 hsel hy).mono (by decide)
    refine ⟨y, he, ?_, ?_, hyr⟩
    · by_cases hseen : x.mem (x.regs stamps + shortened child q) = x.regs epoch <;>
        simpa [hsel, hseen] using hc
    · by_cases hseen : x.mem (x.regs stamps + shortened child q) = x.regs epoch <;>
        simpa [hsel, hseen] using hm
  · have hchild : child = true := by
      cases child <;> simp_all [selected]
    subst hchild
    have he : ExecWithin w (scanDispatch true) x (x.set temporary (x.regs temporary)) 5 :=
      exec_selectDigit_skip hdigit h9 hsel
    refine ⟨x.set temporary (x.regs temporary), he.mono (by decide), ?_, ?_, fun i _ => ?_⟩
    · wram_simp
      simp [hsel]
    · simp [hsel]
    · simp only [Data.set_regs, Function.update_eq_self]

/-- All scan-step scratch registers; caller pointers, counts and the current epoch are kept. -/
def ScanStepLocal (i : Fin registers) : Prop :=
  SuffixLocal i ∨ i = query ∨ i = digit ∨ i = index

instance (i : Fin registers) : Decidable (ScanStepLocal i) :=
  inferInstanceAs (Decidable (SuffixLocal i ∨ i = query ∨ i = digit ∨ i = index))

/-- One complete native scan step includes source indexing, the actual load and digit
computation, conditional deduplicated insertion, and the loop-counter increment. -/
theorem exec_scanStep {w : ℕ} (child : Bool) (x : Data registers) (q : ℕ)
    (hq : x.mem (x.regs listBase + x.regs index) = q)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (h10fit : Fits w 10) (hread : Fits w (x.regs listBase + x.regs index))
    (hs : Fits w (x.regs stamps + shortened child q))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) (hi : Fits w (x.regs index + 1)) :
    ∃ y, ExecWithin w (scanStep child) x y 18 ∧ y.regs index = x.regs index + 1 ∧
      y.regs childCount =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          x.regs childCount + 1 else x.regs childCount) ∧
      y.mem =
        (if selected child (x.regs term) q ∧
            x.mem (x.regs stamps + shortened child q) ≠ x.regs epoch then
          Function.update (Function.update x.mem
            (x.regs childList + x.regs childCount) (shortened child q))
            (x.regs stamps + shortened child q) (x.regs epoch) else x.mem) ∧
      (∀ i, ¬ScanStepLocal i → y.regs i = x.regs i) := by
  have hmod : Fits w (q % 10) := h10fit.of_le (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  refine WP.exists_execWithin ?_
  unfold scanStep scanLoad
  wram_exec [hq, h10, hread, hmod]
  wram_call (exec_scanDispatch child _ q (by wram_simp) (by wram_simp)
    (by wram_simp [h1]) (by wram_simp [h10]) (by wram_simp [h9])
    (by wram_simp; exact hs) (by wram_simp; exact hl) (by wram_simp; exact hn))
    with u ⟨hc, hm, hf⟩
  wram_simp at hc hm
  wram_exec * [hi]
  refine ⟨by wram_simp, by wram_simp [hc], hm, fun i h => ?_⟩
  simp only [ScanStepLocal, not_or] at h
  rcases h with ⟨hsuf, hq', hd', hi'⟩
  wram_simp
  rw [hf i hsuf]
  simp only [SuffixLocal, EmitLocal, not_or] at hsuf
  rcases hsuf with ⟨⟨had, -⟩, -⟩
  wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
