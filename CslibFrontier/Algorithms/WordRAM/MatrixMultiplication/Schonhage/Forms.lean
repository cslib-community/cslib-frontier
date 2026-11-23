/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
public import CslibFrontier.Foundations.Algebra.FiniteMagnitude
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native execution of the encoding forms

The form code reads seven strided entries and uses only the existing native signed arithmetic
blocks. These results account for those blocks' actual instructions and their scratch registers.

## Main results

* `Encoding.exec_summand`: a coefficient in `{0, 1, -1}` takes at most 23 instructions.

## References

The linear forms are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Registers outside the signed workspace and the form's three local registers. -/
def FormFrame (x y : Data 32) : Prop :=
  y.mem = x.mem ∧ ∀ i, 9 ≤ i.val → i ≠ address → i ≠ accumulator → i ≠ temporary →
    y.regs i = x.regs i

/-- Form frames compose without changing any memory cell. -/
theorem FormFrame.trans {x y z : Data 32} (hxy : FormFrame x y) (hyz : FormFrame y z) :
    FormFrame x z :=
  ⟨hyz.1.trans hxy.1, fun i hi ha hc ht =>
    (hyz.2 i hi ha hc ht).trans (hxy.2 i hi ha hc ht)⟩

private theorem fits_of_abs_lt {w : ℕ} (hw : 0 < w) {a : ℤ}
    (ha : |a| < (2 : ℤ) ^ (w - 1)) : GenericRAM.Signed.Fits w a := by
  have h := abs_lt.mp ha
  exact ⟨hw, h.1.le, h.2⟩

/-- A single coefficient is executed by real loads and signed arithmetic. The seven address
computations fit whenever the one-past-end address fits. The two operands must fit the signed
source range; the sum itself may use the two extra target bits supplied by the arithmetic block. -/
theorem exec_summand {w : ℕ} (x : Data 32) (s : Fin 7) (c a v : ℤ) (base n : ℕ)
    (hc : c = 0 ∨ c = 1 ∨ c = -1)
    (hacc : x.regs accumulator = encode a) (hbase : x.regs group = base)
    (hn : x.regs stride = n) (hmem : x.mem (base + s.val * n) = encode v)
    (ha : GenericRAM.Signed.Fits w a) (hv : GenericRAM.Signed.Fits w v)
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (summand s c) x y 23 ∧
      y.regs accumulator = encode (a + c * v) ∧ FormFrame x y := by
  have hmul : Fits (w + 2) (s.val * n) := haddr.of_le (by nlinarith [s.isLt])
  have hsum : Fits (w + 2) (base + s.val * n) := haddr.of_le (by nlinarith [s.isLt])
  rcases hc with rfl | rfl | rfl
  · refine WP.exists_execWithin ?_
    unfold summand
    simp only [↓reduceIte]
    wram_exec [hacc]
    exact ⟨by wram_simp; simp, rfl, fun i _ _ hi _ => by wram_simp⟩
  · refine WP.exists_execWithin ?_
    unfold summand
    simp only [show ¬(1 : ℤ) = 0 by decide, ↓reduceIte]
    wram_exec [hn, hbase, hacc, hmem, hmul, hsum]
    wram_call (exec_add ha hv _ (by wram_simp) (by wram_simp)) with y ⟨hyr, hym, hyreg⟩
    wram_exec [hyr]
    refine ⟨by wram_simp; simp [GenericRAM.Signed.Arithmetic.eval], hym, fun i hi hia hic hit => ?_⟩
    wram_simp
    rw [hyreg i (Or.inr hi)]
    wram_simp
  · refine WP.exists_execWithin ?_
    unfold summand
    simp only [show ¬(-1 : ℤ) = 0 by decide, show ¬(-1 : ℤ) = 1 by decide, ↓reduceIte]
    wram_exec [hn, hbase, hacc, hmem, hmul, hsum]
    wram_call (exec_subtract ha hv _ (by wram_simp) (by wram_simp)) with y ⟨hyr, hym, hyreg⟩
    wram_exec [hyr]
    refine ⟨by wram_simp; simp [GenericRAM.Signed.Arithmetic.eval, sub_eq_add_neg], hym,
      fun i hi hia hic hit => ?_⟩
    wram_simp
    rw [hyreg i (Or.inr hi)]
    wram_simp

/-- Execute any finite list of the fixed digit/coefficients. Partial sums are bounded by
`|a| + length * B`; the theorem derives each arithmetic operand's fit from that inequality. -/
theorem exec_sumCode {w : ℕ} (hw : 0 < w) (pairs : List (Fin 7 × ℤ))
    (x : Data 32) (a B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hc : ∀ sc ∈ pairs, sc.2 = 0 ∨ sc.2 = 1 ∨ sc.2 = -1)
    (hacc : x.regs accumulator = encode a) (hbase : x.regs group = base)
    (hn : x.regs stride = n) (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfitB : B < (2 : ℤ) ^ (w - 1))
    (hfit : |a| + pairs.length * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (sumCode pairs) x y (23 * pairs.length + 1) ∧
      y.regs accumulator = encode (a + (pairs.map fun sc => sc.2 * v sc.1).sum) ∧
      FormFrame x y := by
  induction pairs generalizing x a with
  | nil =>
    refine WP.exists_execWithin ?_
    unfold sumCode
    wram_exec [hacc]
    exact ⟨by wram_simp; simp, rfl, fun i _ _ hi _ => by wram_simp⟩
  | cons sc rest ih =>
    obtain ⟨s, c⟩ := sc
    have hc0 := hc (s, c) (by simp)
    have hcv : |c * v s| ≤ B := by
      rcases hc0 with rfl | rfl | rfl <;> simpa using (by first | exact hB | exact hv s)
    have ha : GenericRAM.Signed.Fits w a :=
      fits_of_abs_lt hw (by have := abs_nonneg a; simp only [List.length_cons,
        Nat.cast_add, Nat.cast_one] at hfit; nlinarith [Nat.cast_nonneg (α := ℤ) rest.length])
    have hvs := fits_of_abs_lt hw ((hv s).trans_lt hfitB)
    have hfit' : |a + c * v s| + rest.length * B < (2 : ℤ) ^ (w - 1) := by
      have ht := abs_add_le a (c * v s)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hfit
      nlinarith
    refine WP.exists_execWithin ?_
    unfold sumCode
    wram_call (exec_summand x s c a (v s) base n hc0 hacc hbase hn (hmem s) ha hvs haddr hseven)
      with y ⟨hyacc, hym, hyr⟩
    wram_call (ih y (a + c * v s) (fun sc hsc => hc sc (by simp [hsc])) hyacc (by regs_frame)
      (by regs_frame) (fun s => by rw [hym]; exact hmem s) hfit') with z ⟨hzacc, hzframe⟩
    refine ⟨by simp only [List.length_cons]; omega, ?_, FormFrame.trans ⟨hym, hyr⟩ hzframe⟩
    simpa only [List.map_cons, List.sum_cons, add_assoc] using hzacc

/-- A complete coefficient row, including initialization, costs at most 163 instructions.
All seven entries have absolute value at most `B`, so every partial sum has magnitude at
most `7B`; this ordinary explicit width condition is sufficient for every signed operation. -/
theorem exec_form {w : ℕ} (hw : 0 < w) (side : Bool) (t : Fin 10)
    (x : Data 32) (B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hbase : x.regs group = base) (hn : x.regs stride = n)
    (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfit : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hseven : Fits (w + 2) 7) :
    ∃ y, ExecWithin (w + 2) (form side t) x y 163 ∧
      y.regs accumulator = encode (∑ s, coefficients side t s * v s) ∧ FormFrame x y := by
  refine WP.exists_execWithin ?_
  unfold form
  wram_exec
  wram_call (exec_sumCode hw (List.ofFn fun s => (s, coefficients side t s)) _ 0 B base n v
    (by intro sc hsc; obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hsc; exact coefficients_values side t s)
    (by wram_simp; rfl) (by wram_simp [hbase]) (by wram_simp [hn]) hmem
    hB hv (by linarith) (by simpa using hfit) haddr hseven) with y ⟨hacc, hym, hyr⟩
  simp only [List.length_ofFn]
  refine ⟨by omega, ?_, hym, fun i hi hia hic hit => ?_⟩
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, zero_add] using hacc
  · rw [hyr i hi hia hic hit]
    wram_simp

/-- The finite term dispatch costs at most three instructions per inspected row in addition
to the row's 163-instruction bound. All ten forms share the same native register file. -/
theorem exec_dispatch {w : ℕ} (hw : 0 < w) (side : Bool) (rows : List (Fin 10))
    (t : Fin 10) (ht : t ∈ rows) (x : Data 32) (B : ℤ) (base n : ℕ) (v : Fin 7 → ℤ)
    (hterm : x.regs term = t.val) (hbase : x.regs group = base) (hn : x.regs stride = n)
    (hmem : ∀ s, x.mem (base + s.val * n) = encode (v s))
    (hB : 0 ≤ B) (hv : ∀ s, |v s| ≤ B) (hfit : 7 * B < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (base + 7 * n)) (hten : Fits (w + 2) 10) :
    ∃ y, ExecWithin (w + 2) (dispatch side rows) x y (3 * rows.length + 163) ∧
      y.regs accumulator = encode (∑ s, coefficients side t s * v s) ∧ FormFrame x y := by
  induction rows generalizing x with
  | nil => simp at ht
  | cons q rest ih =>
    have hqfit : Fits (w + 2) q.val := hten.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold dispatch
    wram_exec [hterm, hqfit]
    · have hqt : t = q := Fin.ext hc
      subst hqt
      wram_call (exec_form hw side t _ B base n v (by wram_simp [hbase]) (by wram_simp [hn])
        hmem hB hv hfit haddr (hten.of_le (by decide))) with y ⟨hacc, hym, hyr⟩
      refine ⟨by simp only [List.length_cons]; omega, hacc, hym, fun i hi hia hic hit => ?_⟩
      rw [hyr i hi hia hic hit]
      wram_simp
    · have htrest : t ∈ rest :=
        (List.mem_cons.mp ht).resolve_left (fun h => hc (congrArg Fin.val h))
      wram_call (ih htrest _ (by wram_simp [hterm]) (by wram_simp [hbase]) (by wram_simp [hn])
        hmem) with y ⟨hacc, hym, hyr⟩
      refine ⟨by simp only [List.length_cons]; omega, hacc, hym, fun i hi hia hic hit => ?_⟩
      rw [hyr i hi hia hic hit]
      wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
