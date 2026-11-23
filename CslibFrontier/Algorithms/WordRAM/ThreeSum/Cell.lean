/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Weight
import CslibFrontier.Computability.GenericRAM.Signed.Fits
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# One cell of the three Convolution-3SUM matrices

This directly adapts `fillCells` of Anthropic's pinned graph builder at
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, using native unsigned word-RAM instructions.
The row and column, all three input indices, and the three destination addresses are computed
by the program. A negative BC index is replaced with the negative sentinel `-1`: both select
the filler. Registers 22 through 25 are additional scratch; registers 14 through 21 belong to
the caller. The AB and BC destinations follow the input, preserving it for subsequent reads.
The final AC write may alias the input; the complete matrix loop uses disjoint blocks.

## Main definitions

* `Cell.step`: compute and write one cell of each matrix.

## Main results

* `Cell.exec_step`: exact memory effect and a constant charged native instruction bound.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Cell

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum (pick)

/-- Current row-major cell. -/
abbrev cell : Fin 28 := 14
/-- Number of vertices per part. -/
abbrev side : Fin 28 := 15
/-- Instance number. -/
abbrev inst : Fin 28 := 16
/-- Base address of matrix AB. -/
abbrev matAB : Fin 28 := 17
/-- Base address of matrix BC. -/
abbrev matBC : Fin 28 := 18
/-- Base address of matrix AC. -/
abbrev matAC : Fin 28 := 19
/-- Input length. -/
abbrev len : Fin 28 := 10
/-- Input base address. -/
abbrev base : Fin 28 := 11
/-- Signed encoded filler. -/
abbrev filler : Fin 28 := 12

/-- Encoded source index. -/
abbrev index : Fin 28 := 9
/-- Current destination address. -/
abbrev dest : Fin 28 := 13
/-- Saved encoded filler. -/
abbrev saved : Fin 28 := 22
/-- Encoded negation of the filler. -/
abbrev negFill : Fin 28 := 23
/-- Computed row of the current cell. -/
abbrev row : Fin 28 := 24
/-- Computed column of the current cell. -/
abbrev col : Fin 28 := 25
/-- Place the fourteen weight registers at the start of the cell register file. -/
def embedding (i : Fin 14) : Fin 28 := ⟨i.val, by omega⟩
private theorem embedding_injective : Function.Injective embedding := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 28 => k.val) h

/-- The existing weight kernel embedded in the larger register file. -/
def writeWeight (negate : Bool) : Code .standard 28 :=
  (Weight.store negate).rename embedding

private theorem weight_preserves (negate : Bool) :
    ∀ i : Fin 28, 9 ≤ i.val → (writeWeight negate).Preserves i := by
  cases negate <;> decide

private theorem exec_weight {w N b d : ℕ} {μ : ℕ → ℤ} {fill z : ℤ}
    (negate : Bool) (x : Data 28)
    (hindex : x.regs index = encode z) (hlen : x.regs len = N)
    (hbase : x.regs base = b) (hfiller : x.regs filler = encode fill)
    (hdest : x.regs dest = d) (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hz : GenericRAM.Signed.Fits w z) (hfill : GenericRAM.Signed.Fits w fill)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i)) (haddr : Fits (w + 2) (b + N)) :
    ∃ y, ExecWithin (w + 2) (writeWeight negate) x y 28 ∧
      y.mem = Function.update x.mem d
        (encode (if negate then -pick N μ fill z else pick N μ fill z)) ∧
      ∀ i : Fin 28, 9 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, he, hm, -⟩ := Weight.exec_store negate (x.comap embedding)
    hindex hlen hbase hfiller hdest hmem hz hfill hμ haddr
  have hr := he.rename embedding_injective
  exact ⟨_, hr, hm, fun i hi => hr.regs_eq (weight_preserves negate i hi)⟩

/-- Save the filler, compute the coordinates and prepare its negation operands. -/
def prepareSetup : Code .standard 28 := ram[
  saved ← filler; row ← cell / side; col ← cell % side; left ← #0; right ← filler ]

/-- Compute the row and column, save the filler, and form its signed negation. -/
def prepare : Code .standard 28 := ram[
  ⟪prepareSetup⟫; ⟪subtract⟫; negFill ← result ]

/-- Write the AB cell, including encoding its index and calculating its address. -/
def setupAB : Code .standard 28 := ram[ index ← cell + cell; dest ← matAB + cell ]

/-- Write the AB cell after computing its index and destination. -/
def putAB : Code .standard 28 := ram[ ⟪setupAB⟫; ⟪writeWeight false⟫ ]

/-- Write BC, testing for a negative index before unsigned subtraction. -/
def setupBC : Code .standard 28 := ram[
  index ← col * side; index ← index + inst;
  if index < row then [ index ← #3 ] else [
    index ← index - row; index ← index + index ];
  dest ← matBC + cell ]

/-- Write BC after computing its guarded signed index and destination. -/
def putBC : Code .standard 28 := ram[ ⟪setupBC⟫; ⟪writeWeight false⟫ ]

/-- Write AC with negated filler before negating the selected value, then restore the filler. -/
def setupAC : Code .standard 28 := ram[
  index ← row + col; index ← index * side; index ← index + inst;
  index ← index + index; dest ← matAC + cell; filler ← negFill ]

/-- Write AC and restore the caller's positive filler. -/
def putAC : Code .standard 28 := ram[
  ⟪setupAC⟫; ⟪writeWeight true⟫; filler ← saved ]

/-- Compute and write all three entries at the current row-major cell. -/
def step : Code .standard 28 := ram[
  ⟪prepare⟫; ⟪putAB⟫; ⟪putBC⟫; ⟪putAC⟫ ]

private theorem step_preserves : ∀ i : Fin 28,
    i.val = 10 ∨ i.val = 11 ∨ (14 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val →
      step.Preserves i := by decide +kernel

private theorem encode_nat (k : ℕ) : encode (k : ℤ) = k + k := by
  simp [encode, two_mul]

private theorem picked_index {N a b : ℕ} {μ : ℕ → ℤ} {F : ℤ} :
    pick N μ F (if a < b then -1 else (a - b : ℕ)) =
      pick N μ F ((a : ℤ) - b) := by
  by_cases h : a < b
  · simp [h, pick]
  · simp only [h, ↓reduceIte, show ((a - b : ℕ) : ℤ) = (a : ℤ) - b by omega]

private theorem exec_prepare {w q t : ℕ} {F : ℤ} (x : Data 28)
    (hq : x.regs cell = q) (ht : x.regs side = t) (hf : x.regs filler = encode F)
    (hrow : Fits (w + 2) (q / t)) (hcol : Fits (w + 2) (q % t))
    (hF : GenericRAM.Signed.Fits w F) :
    ∃ y, ExecWithin (w + 2) prepare x y 23 ∧ y.mem = x.mem ∧
      y.regs row = q / t ∧ y.regs col = q % t ∧
      y.regs saved = encode F ∧ y.regs negFill = encode (-F) := by
  refine WP.exists_execWithin ?_
  unfold prepare prepareSetup
  wram_exec [hq, ht, hf]
  wram_call (exec_subtract (GenericRAM.Signed.fits_zero hF.1) hF _
    (by wram_simp [encode]; decide) (by wram_simp)) framed with v m ⟨hur, hum, _⟩
  wram_exec [hur, hum]
  wram_simp [hum, GenericRAM.Signed.Arithmetic.eval, zero_sub]

private theorem exec_AB {w N b d q : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matAB = d)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hfiller : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hq : GenericRAM.Signed.Fits w (q : ℤ)) (hF : GenericRAM.Signed.Fits w F)
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putAB x y 30 ∧
      y.mem = Function.update x.mem (d + q) (encode (pick N μ F q)) := by
  have hqfit : Fits (w + 2) (q + q) := by
    simpa only [encode_nat] using (encode_fits hq).mono (by omega : w + 1 ≤ w + 2)
  refine WP.exists_execWithin ?_
  unfold putAB setupAB
  wram_exec [hcell, hmat]
  wram_call (exec_weight (d := d + q) false _
    (by wram_simp [encode_nat]) (by wram_simp [hlen]) (by wram_simp [hbase])
    (by wram_simp [hfiller]) (by wram_simp) (by wram_simp; exact hmem)
    hq hF hμ haddr) with y ⟨hym, _⟩
  wram_simp at hym
  exact ⟨by omega, hym⟩

private theorem exec_BC {w N b d q r c t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matBC = d)
    (hrow : x.regs row = r) (hcol : x.regs col = c)
    (ht : x.regs side = t) (hs : x.regs inst = s)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hfiller : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w ((c * t + s : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w F) (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putBC x y 35 ∧
      y.mem = Function.update x.mem (d + q) (encode (pick N μ F ((c * t + s : ℕ) - (r : ℤ)))) := by
  let a := c * t + s
  have hfit : Fits (w + 2) (a + a) := by
    simpa only [encode_nat] using (encode_fits hidx).mono (by omega : w + 1 ≤ w + 2)
  have h3 : Fits (w + 2) 3 := (show Fits 2 3 from by decide).mono (by omega)
  refine WP.exists_execWithin ?_
  unfold putBC setupBC
  wram_exec [hcell, hmat, hrow, hcol, ht, hs]
  · have hix : GenericRAM.Signed.Fits w (-1 : ℤ) :=
      ⟨hidx.1, by have := hidx.2.1; have := hidx.2.2; omega, by have := hidx.2.2; omega⟩
    wram_call (exec_weight (d := d + q) (z := -1) false _
      (by wram_simp [encode]; decide) (by wram_simp [hlen]) (by wram_simp [hbase])
      (by wram_simp [hfiller]) (by wram_simp) (by wram_simp; exact hmem)
      hix hF hμ haddr) with y ⟨hym, _⟩
    wram_simp at hym
    exact ⟨by omega, by simpa only [← picked_index, hc, ↓reduceIte, Bool.false_eq_true] using hym⟩
  · have hix : GenericRAM.Signed.Fits w ((a - r : ℕ) : ℤ) :=
      hidx.of_natAbs_le (by rw [Int.natAbs_natCast]; dsimp [a]; omega)
    wram_call (exec_weight (d := d + q) (z := (a - r : ℕ)) false _
      (by wram_simp [encode_nat, a]) (by wram_simp [hlen]) (by wram_simp [hbase])
      (by wram_simp [hfiller]) (by wram_simp) (by wram_simp; exact hmem)
      hix hF hμ haddr) with y ⟨hym, _⟩
    wram_simp at hym
    exact ⟨by omega, by simpa only [← picked_index, hc, ↓reduceIte, Bool.false_eq_true] using hym⟩

private theorem exec_AC {w N b d q r c t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (hmat : x.regs matAC = d)
    (hrow : x.regs row = r) (hcol : x.regs col = c)
    (ht : x.regs side = t) (hs : x.regs inst = s)
    (hlen : x.regs len = N) (hbase : x.regs base = b)
    (hsaved : x.regs saved = encode F) (hneg : x.regs negFill = encode (-F))
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w (((r + c) * t + s : ℕ) : ℤ))
    (hpos : 0 < t) (hF : GenericRAM.Signed.Fits w (-F))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N)) (hd : Fits (w + 2) (d + q)) :
    ∃ y, ExecWithin (w + 2) putAC x y 35 ∧
      y.mem = Function.update x.mem (d + q)
        (encode (-pick N μ (-F) ((r + c) * t + s : ℕ))) ∧
      y.regs filler = encode F := by
  let a := (r + c) * t + s
  have hfit : Fits (w + 2) (a + a) := by
    simpa only [encode_nat] using (encode_fits hidx).mono (by omega : w + 1 ≤ w + 2)
  have hrc_le : r + c ≤ a := by dsimp [a]; nlinarith
  refine WP.exists_execWithin ?_
  unfold putAC setupAC
  wram_exec [hcell, hmat, hrow, hcol, ht, hs, hneg]
  wram_call (exec_weight (d := d + q) (z := (a : ℤ)) true _
    (by wram_simp [encode_nat, a]) (by wram_simp [hlen]) (by wram_simp [hbase])
    (by wram_simp) (by wram_simp) (by wram_simp; exact hmem)
    hidx hF hμ haddr) framed with v m ⟨hum, _⟩
  wram_exec [hsaved]
  wram_simp [hum, a]

/-- All index computations, three guarded loads, optional signed negation, stores and argument
preparation take at most 128 native instructions. The final halt is excluded. Input cells precede
the AB and BC destinations, and the AC destination may alias the input; the three writes occur
in AB, BC, AC order. -/
theorem exec_step {w N b ab bc ac q t s : ℕ} {μ : ℕ → ℤ} {F : ℤ} (x : Data 28)
    (hcell : x.regs cell = q) (ht : x.regs side = t) (hs : x.regs inst = s)
    (hab : x.regs matAB = ab) (hbc : x.regs matBC = bc) (hac : x.regs matAC = ac)
    (hlen : x.regs len = N) (hbase : x.regs base = b) (hf : x.regs filler = encode F)
    (hmem : ∀ i < N, x.mem (b + i) = encode (μ i))
    (hq : q < t * t) (hidx : GenericRAM.Signed.Fits w ((2 * (t * t) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w F) (hnF : GenericRAM.Signed.Fits w (-F))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (haddr : Fits (w + 2) (b + N))
    (habfit : Fits (w + 2) (ab + q)) (hbcfit : Fits (w + 2) (bc + q))
    (hacfit : Fits (w + 2) (ac + q))
    (hbelowAB : b + N ≤ ab) (hbelowBC : b + N ≤ bc) :
    ∃ y, ExecWithin (w + 2) step x y 128 ∧
      y.mem = Function.update (Function.update (Function.update x.mem
        (ab + q) (encode (pick N μ F q)))
        (bc + q) (encode (pick N μ F ((q % t * t + s : ℕ) - ((q / t : ℕ) : ℤ)))))
        (ac + q) (encode (-pick N μ (-F) ((q / t + q % t) * t + s : ℕ))) ∧
      y.regs filler = x.regs filler ∧
      ∀ i : Fin 28, i.val = 10 ∨ i.val = 11 ∨
        (14 ≤ i.val ∧ i.val ≤ 21) ∨ 26 ≤ i.val → y.regs i = x.regs i := by
  have htpos : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hrow : q / t < t := Nat.div_lt_of_lt_mul hq
  have hcol : q % t < t := Nat.mod_lt q htpos
  have hrow_mul : q / t * t ≤ t * t := Nat.mul_le_mul_right t hrow.le
  have hcol_mul : q % t * t ≤ t * t := Nat.mul_le_mul_right t hcol.le
  have hnat (k : ℕ) (hk : k ≤ 2 * (t * t) + s + 1) : GenericRAM.Signed.Fits w (k : ℤ) :=
    hidx.of_natAbs_le (by rwa [Int.natAbs_natCast])
  have hfits (k : ℕ) (hk : k ≤ 2 * (t * t) + s + 1) : Fits (w + 2) k :=
    ((encode_fits (hnat k hk)).mono (by omega)).of_le (by rw [encode_nat]; omega)
  obtain ⟨y, he, hym, hyf⟩ : ∃ y, ExecWithin (w + 2) step x y 128 ∧
      y.mem = Function.update (Function.update (Function.update x.mem
        (ab + q) (encode (pick N μ F q)))
        (bc + q) (encode (pick N μ F ((q % t * t + s : ℕ) - ((q / t : ℕ) : ℤ)))))
        (ac + q) (encode (-pick N μ (-F) ((q / t + q % t) * t + s : ℕ))) ∧
      y.regs filler = x.regs filler := by
    refine WP.exists_execWithin ?_
    unfold step
    wram_exec
    wram_call (exec_prepare x hcell ht hf
      (hfits _ (Nat.le_trans (Nat.div_le_self _ _) (by omega)))
      (hfits _ (Nat.le_trans (Nat.mod_le _ _) (by omega))) hF)
      framed with v₁ m₁ ⟨hpm, hpr, hpc, hpF, hpnF⟩
    refine WP.seq ?_
    wram_call (exec_AB _ (by wram_simp [hcell]) (by wram_simp [hab]) (by wram_simp [hlen])
      (by wram_simp [hbase]) (by wram_simp [hf]) (by wram_simp [hpm]; exact hmem)
      (hnat _ (by omega)) hF hμ haddr habfit) framed with v₂ m₂ ham
    have hamem : ∀ i < N, m₂ (b + i) = encode (μ i) := fun i hi => by
      rw [ham, Function.update_of_ne (by omega), hpm]; exact hmem i hi
    refine WP.seq ?_
    wram_call (exec_BC (r := q / t) (c := q % t) (t := t) (s := s) _
      (by wram_simp [hcell]) (by wram_simp [hbc]) (by wram_simp [hpr])
      (by wram_simp [hpc]) (by wram_simp [ht]) (by wram_simp [hs]) (by wram_simp [hlen])
      (by wram_simp [hbase]) (by wram_simp [hf]) (by wram_simp; exact hamem)
      (hnat _ (by omega)) hF hμ haddr hbcfit) framed with v₃ m₃ hvm
    have hvmem : ∀ i < N, m₃ (b + i) = encode (μ i) := fun i hi => by
      rw [hvm, Function.update_of_ne (by omega)]; exact hamem i hi
    wram_call (exec_AC (r := q / t) (c := q % t) (t := t) (s := s) _
      (by wram_simp [hcell]) (by wram_simp [hac]) (by wram_simp [hpr])
      (by wram_simp [hpc]) (by wram_simp [ht]) (by wram_simp [hs]) (by wram_simp [hlen])
      (by wram_simp [hbase]) (by wram_simp [hpF]) (by wram_simp [hpnF])
      (by wram_simp; exact hvmem)
      (hnat _ (by rw [Nat.add_mul]; omega)) htpos hnF hμ haddr hacfit) with y ⟨hym, hyf⟩
    wram_simp at hym
    exact ⟨by omega, by rw [hym, hvm, ham, hpm], hyf.trans hf.symm⟩
  exact ⟨y, he, hym, hyf, fun i hi => he.regs_eq (step_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Cell
