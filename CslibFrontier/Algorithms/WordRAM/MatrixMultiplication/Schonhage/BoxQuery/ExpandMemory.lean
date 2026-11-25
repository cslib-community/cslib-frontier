/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Push
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory

/-!
# Real stack readback after child expansion

The native indexed dispatch pushes digits eight down through zero. Consequently the
logical frontier pops zero through eight. The pure store identities below connect
that actual write order to the existing prefix descriptors and preserve older tasks.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem indexed_ne_P0 (d : Fin 9) :
    Encoding.termDigits ⟨d.val, by omega⟩ ≠ Term.P0 := by decide +revert

/-- Actual indexed stores prepend exactly the reverse of their push-order child list. -/
theorem StackMemory.indexedChildren {L F : ℕ} {η : OutStr L} {rest : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F rest μ) (xs : List Term)
    (hi : (outAt η xs.length).IsInner) (ds : List (Fin 9)) :
    StackMemory η F
      ((ds.map fun d => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]).reverse ++ rest)
      (writeIndexedChildren F (xs.length + 1) (prefixCode xs) (usedFrom η 0 xs)
        (starsFrom η 0 xs) (10 ^ xs.length) (10 ^ (xs.length + 1)) rest.length ds μ) := by
  induction ds generalizing rest μ with
  | nil => simpa only [List.map_nil, List.reverse_nil, List.nil_append,
      writeIndexedChildren] using h
  | cons d ds ih =>
    let lam := Encoding.termDigits (⟨d.val, by omega⟩ : Fin 10)
    have hp : lam ≠ .P0 := indexed_ne_P0 d
    have hu : usedFrom η 0 (xs ++ [lam]) = usedFrom η 0 xs + 1 := by
      rw [usedFrom_append_one]; simp [hi, hp]
    have he : starsFrom η 0 (xs ++ [lam]) = starsFrom η 0 xs := by
      rw [starsFrom_append_one]; simp [hp]
    have hpush' : StackMemory η F ((xs ++ [lam]) :: rest)
        (writeTask F rest.length (xs.length + 1) (prefixCode xs + d.val * 10 ^ xs.length)
          (usedFrom η 0 xs + 1) (starsFrom η 0 xs) (10 ^ (xs.length + 1)) μ) := by
      simpa only [List.length_append, List.length_singleton, prefixCode_append, lam,
        Equiv.symm_apply_apply, hu, he] using h.push (xs ++ [lam])
    simpa only [writeIndexedChildren, List.length_cons, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, lam] using ih hpush'

/-- The fixed reverse digit list is exactly the desired zero-through-eight logical frontier. -/
theorem reverse_nineChildren (xs : List Term) :
    (((List.ofFn fun i : Fin 9 => (⟨8 - i.val, by omega⟩ : Fin 9)).map
      fun d => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]).reverse) =
      List.ofFn (fun d : Fin 9 => xs ++ [Encoding.termDigits ⟨d.val, by omega⟩]) := by
  rfl

/-- The actual P0 descriptor has the exact prefix counters needed by the finite traversal. -/
theorem StackMemory.p0Child {L F : ℕ} {η : OutStr L} {rest : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F rest μ) (xs : List Term)
    (hi : (outAt η xs.length).IsInner) :
    StackMemory η F ((xs ++ [.P0]) :: rest)
      (writeTask F rest.length (xs.length + 1) (prefixCode xs + 9 * 10 ^ xs.length)
        (usedFrom η 0 xs) (if usedFrom η 0 xs = 0 then starsFrom η 0 xs + 1
          else starsFrom η 0 xs) (10 ^ (xs.length + 1)) μ) := by
  have hd : (Encoding.termDigits.symm Term.P0).val = 9 := by decide
  have hu : usedFrom η 0 (xs ++ [.P0]) = usedFrom η 0 xs := by simp [usedFrom_append_one]
  have he : starsFrom η 0 (xs ++ [.P0]) =
      if usedFrom η 0 xs = 0 then starsFrom η 0 xs + 1 else starsFrom η 0 xs := by
    rw [starsFrom_append_one]; split <;> simp_all
  simpa only [List.length_append, List.length_singleton, prefixCode_append, hd, hu, he] using
    h.push (xs ++ [Term.P0])

/-- The actual private-term descriptor preserves both inner counters. -/
theorem StackMemory.privateChild {L F : ℕ} {η : OutStr L} {rest : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F rest μ) (xs : List Term)
    (hi : ¬(outAt η xs.length).IsInner) :
    StackMemory η F ((xs ++ [(outAt η xs.length).privateTerm]) :: rest)
      (writeTask F rest.length (xs.length + 1)
        (prefixCode xs + (PrunedQuery.outputDigits.symm (outAt η xs.length)).val *
          10 ^ xs.length) (usedFrom η 0 xs) (starsFrom η 0 xs)
        (10 ^ (xs.length + 1)) μ) := by
  have hu : usedFrom η 0 (xs ++ [(outAt η xs.length).privateTerm]) = usedFrom η 0 xs := by
    simp [usedFrom_append_one, hi]
  have he : starsFrom η 0 (xs ++ [(outAt η xs.length).privateTerm]) = starsFrom η 0 xs := by
    simp [starsFrom_append_one, hi]
  have hc : (Encoding.termDigits.symm (outAt η xs.length).privateTerm).val =
      (PrunedQuery.outputDigits.symm (outAt η xs.length)).val := rfl
  simpa only [List.length_append, List.length_singleton, prefixCode_append, hc, hu, he] using
    h.push (xs ++ [(outAt η xs.length).privateTerm])

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
