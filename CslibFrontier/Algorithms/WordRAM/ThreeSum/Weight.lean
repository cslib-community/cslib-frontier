/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ThreeSum.Convolution
public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Native weight selection for the Convolution-3SUM reduction

Directly adapts `pickStmt` and `putStmt` of Anthropic's [pinned graph builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean).
This code uses the existing unsigned word RAM,
its sign-and-magnitude encoding, and its proved subtraction block. No source machine is copied.

One input register holds a signed index, which may be negative or out of range. The code reads
only when the index is nonnegative and below `N`; otherwise it uses the filler. It optionally
negates the selected value and stores it at a supplied destination. Addresses and lengths are
unsigned; index, filler and input values are encoded signed integers. The nine arithmetic
registers are scratch, and the five argument registers are preserved. Destination/input overlap
is allowed for this single read-then-write operation; graph-building loops need their own frame.

The theorem charges selection, optional negation and the store, excluding a final halt.
`Exec.executes` adds one instruction for that halt. Computing the index, arranging
arguments, traversing matrices and invoking Exact Triangle are not included. This is a graph
construction kernel, not a complete reduction or a subquadratic 3SUM solver.

## Main definitions

* `Weight.select`: guarded read, falling back to the encoded filler.
* `Weight.store`: select, optionally negate, and store one graph weight.

## Main results

* `Weight.exec_store`: at most twenty-eight native instructions at width `w + 2`.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Weight

open Cslib.WordRAM
open Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum (pick)

/-- Encoded signed index to read. -/
abbrev index : Fin 14 := ⟨9, by decide⟩
/-- Unsigned input length. -/
abbrev len : Fin 14 := ⟨10, by decide⟩
/-- Unsigned input base address. -/
abbrev base : Fin 14 := ⟨11, by decide⟩
/-- Encoded fallback value. -/
abbrev filler : Fin 14 := ⟨12, by decide⟩
/-- Unsigned destination address. -/
abbrev dest : Fin 14 := ⟨13, by decide⟩

/-- Select a signed input word into `right`, rejecting negative indices before any load. -/
def select : Code .standard 14 := ram[
  two ← #2; zero ← #0; magA ← index / two; signA ← index % two;
  right ← filler;
  if signA = zero then [
    if magA < len then [ magA ← base + magA; right ← *magA ]
    else [ right ← right ] ] else [ right ← right ] ]

/-- Store a selected weight, optionally negated; all five argument registers are preserved. -/
def store (negate : Bool) : Code .standard 14 :=
  .seq (.seq select (.op (.const left 0)))
    (.seq (if negate then subtract else .op (.copy result right)) (.op (.store dest result)))

private theorem exec_select {w N b : ℕ} {μ : ℕ → ℤ} {fill z : ℤ} (x : Data 14)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (haddr : Fits (w + 2) (b + N)) :
    ∃ y, ExecWithin (w + 2) select x y 9 ∧
      y.regs right = encode (pick N μ fill z) ∧ y.mem = x.mem := by
  have h2 : Fits (w + 2) 2 := (show Fits 2 2 from by decide).mono (by omega)
  have hsign : Fits (w + 2) (if z < 0 then 1 else 0) := by
    split_ifs <;> exact (show Fits 2 _ from by decide).mono (by omega)
  have hmag : Fits (w + 2) z.natAbs :=
    ((encode_fits hz).mono (by omega)).of_le (by unfold encode; split_ifs <;> omega)
  refine WP.exists_execWithin ?_
  wram_exec [select, hindex, hlen, hbase, hfiller, encode_div_two, encode_mod_two]
  · have hnn : 0 ≤ z := by
      by_contra h
      rw [not_le] at h
      simp only [h, ↓reduceIte, one_ne_zero] at *
    have hlt : z < N := by omega
    have heq : z.natAbs = z.toNat := by omega
    wram_simp [heq, hmem z.toNat (by omega)]
    simp [pick, hnn, hlt]
  · have hnot : ¬(0 ≤ z ∧ z < N) := fun ⟨hnn, hlt⟩ => hc (by omega)
    wram_simp [hfiller]
    simp [pick, hnot]
  · have hneg : ¬0 ≤ z := by split_ifs at hc <;> omega
    wram_simp [hfiller]
    simp [pick, hneg]

/-- A selected signed weight is stored within twenty-eight unsigned instructions. All address
arithmetic is charged, but computing the signed index and preparing arguments are caller costs.
The signed bounds are satisfiable even for negative, zero and out-of-range indices. -/
theorem exec_store {w N b d : ℕ} {μ : ℕ → ℤ} {fill z : ℤ} (negate : Bool) (x : Data 14)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hdest : x.regs dest = d) (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (hfill : GenericRAM.Signed.Fits w fill)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i)) (haddr : Fits (w + 2) (b + N)) :
    ∃ y, ExecWithin (w + 2) (store negate) x y 28 ∧
      y.mem = Function.update x.mem d
        (encode (if negate then -pick N μ fill z else pick N μ fill z)) ∧
      ∀ i : Fin 14, 9 ≤ i.val → y.regs i = x.regs i := by
  have hval : GenericRAM.Signed.Fits w (pick N μ fill z) := by
    unfold pick
    split_ifs with h
    · exact hμ _ (by omega)
    · exact hfill
  have hpres : ∀ i : Fin 14, 9 ≤ i.val → (store negate).Preserves i := by
    cases negate <;> decide
  obtain ⟨y, he, hym⟩ : ∃ y, ExecWithin (w + 2) (store negate) x y 28 ∧
      y.mem = Function.update x.mem d
        (encode (if negate then -pick N μ fill z else pick N μ fill z)) := by
    refine WP.exists_execWithin ?_
    wram_exec [store]
    wram_call (exec_select x hindex hlen hbase hfiller hmem hz haddr) framed
      with v m ⟨hvr, hvm⟩
    cases negate <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · wram_exec [hvr, hvm, hdest]
      wram_simp [hvm]
    · wram_exec
      wram_call (exec_subtract (GenericRAM.Signed.fits_zero hz.1) hval _
        (by wram_simp [encode]; decide) (by wram_simp [hvr])) framed with v₁ m₁ ⟨hyr, hym, _⟩
      wram_simp at hym
      wram_exec [hyr, hym, hvm, hdest]
      wram_simp [GenericRAM.Signed.Arithmetic.eval, zero_sub, hym, hvm]
  exact ⟨y, he, hym, fun i hi => he.regs_eq (hpres i hi)⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Weight
