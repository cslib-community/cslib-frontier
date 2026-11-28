/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Record
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Slot
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Readback
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Admission
import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# One-slot record construction, call, heap reset and return

`exec_step` composes one streaming loop body: constructing the next logical chunk/piece record in
the single physical slot (`construct`), selecting constant physical ordinal zero (`select`),
running the box-product and original-weight verifier (`FixedPrime.record`), resetting the heap
pointer to `Instances.output` (`reset`), and updating the scan counter, witness flag and early-stop
limit (`FixedPrime.receive`).
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open FixedPrime
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- One actual construction, physical-slot call, reclamation and native return. The charge
includes every bridge instruction; the loop's two instructions appear on the left. -/
theorem exec_step {w m n g p A i : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : FixedPrime.admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (cursor : Cursor n (D m) g p (fun q => values.getD q 0) (x.comap producerBank))
    (hproduced : x.regs (producerBank Instances.produced) = i)
    (hslotHeap : x.regs (producerBank Instances.heap) = x.regs (producerBank Instances.output))
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hi : x.regs Reg.index = i) (hiM : i < a.regs Instances.produced)
    (hl : x.regs Reg.limit = a.regs Instances.produced) (h1 : x.regs Reg.one = 1)
    (hscans : x.regs Reg.scans ≤ i * (n * n + 1))
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0) (D m) g p)
    (hord : RecordProduct.recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = i) :
    let V := fun q => values.getD q 0
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let Q := RecordProduct.recordQueryCount n (D m) p V idx
    ∃ y S T, ExecWithin (w + 2) step x y T ∧
      T + 2 ≤ FixedPrime.recordBase (m := m) hn V a.mem idx +
        (40 * (n * D m) + 67) +
        (42 * pieceSize (D m) g + 28) * S ∧
      y.regs Reg.index = i + 1 ∧
      y.regs Reg.limit = (if y.regs Reg.found = 1 then i + 1 else a.regs Instances.produced) ∧
      y.regs Reg.one = 1 ∧
      y.regs Reg.scans = x.regs Reg.scans + S ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      S ≤ FixedPrime.recordFailures (m := m) (g := g) hn V a.mem idx + y.regs Reg.found ∧
      S ≤ n * n + 1 ∧
      (y.regs Reg.found = 1 ↔ FixedPrime.recordHit (m := m) (n := n) (g := g) V idx) ∧
      (y.regs Reg.found = 1 →
        y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
        V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessB)) +
          V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) +
          V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
      (∀ u, u < a.regs Instances.output ∨
        a.regs Instances.output + (6 + 2 * (n * D m)) +
          CallableProduct.windowSize n Q ≤ u → y.mem u = x.mem u) ∧
      Cursor n (D m) g p V (y.comap producerBank) ∧
      y.regs (producerBank Instances.produced) = i + 1 ∧
      y.regs (producerBank Instances.heap) = y.regs (producerBank Instances.output) := by
  let V := fun q => values.getD q 0
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  have hout' : x.regs (producerBank Instances.output) = a.regs Instances.output := by
    rw [← Data.comap_regs, cursor.output, cursor.chunks, hout.2.2.2.1]
  have htotal : x.regs (producerBank Instances.total) = a.regs Instances.produced := by
    rw [← Data.comap_regs, cursor.total, cursor.chunks, cursor.pieces, hout.2.2.2.2.1]
  have hprep : PreparationInput.width n (D m) g p A ≤ w + 2 := by
    have hr := FixedPrime.record_admitted hW
    unfold RecordWitness.admissionWidth RecordProduct.admissionWidth at hr
    omega
  have budget := (PreparationInput.fits_at_width n (D m) g p A).2.mono hprep
  have hf : Function.Injective producerBank := Fin.castLE_injective (by decide)
  obtain ⟨residues, descriptor⟩ := catalogue_readback V
    (.init (PreparationInput.input n (D m) g p values)) a (x.comap producerBank)
    hout hp0 cursor hmem idx hidx
  obtain ⟨c, hc, ccursor, ci, ch, cd, cL, cR, cm⟩ := exec_construct V
    (x.comap producerBank) hD hg hp0 cursor hslotHeap idx hidx
    (hproduced.trans hord.symm) residues descriptor
    (budget.of_le (cursor.visit_budget_le hD hDn hg hslotHeap
      (by simpa only [Data.comap_regs, hproduced, htotal] using hiM)))
  simp only [Data.comap_regs, Data.comap_mem] at ci ch cd cL cR cm
  have haout := hout.2.2.2.1
  have haprod := hout.2.2.2.2.1
  have hcout : c.regs Instances.output = a.regs Instances.output := by
    simpa only [ccursor.chunks, haout] using ccursor.output
  have hcheap : c.regs Instances.heap = a.regs Instances.output + (6 + 2 * (n * D m)) :=
    hout' ▸ ch
  let s := c.extend producerBank x
  have hs : ExecWithin (w + 2) construct x s (40 * (n * D m) + 66) := hc.rename hf
  have sr (j : Fin 64) : s.regs (producerBank j) = c.regs j := hf.extend_apply _ _ j
  have scontrol (j : Fin 416) (hj : 64 ≤ j.val) : s.regs j = x.regs j :=
    Data.extend_castLE_regs_of_le (hrs := by decide) c x j hj
  let dst := recordBank (RecordWitness.productBank RecordProduct.Reg.ordinal)
  let z := s.set dst 0
  have hz : ExecWithin (w + 2) select s z 1 := ExecWithin.const (fits_zero _)
  have zset (j : Fin 416) (hj : j ≠ dst) : z.regs j = s.regs j := Data.set_regs_of_ne hj _
  have zdst : z.regs dst = 0 := Data.set_regs_self _ _ _
  obtain ⟨zh, zo⟩ :
      z.regs (producerBank Instances.heap) = a.regs Instances.output + (6 + 2 * (n * D m)) ∧
      z.regs (producerBank Instances.output) = a.regs Instances.output := by
    clear hc hs; regs_frame
  have zm : z.mem = c.mem := rfl
  have zmem : Set.EqOn z.mem a.mem (Set.Iio (a.regs Instances.output)) := fun u hu =>
    (cm u (Or.inl (by simpa only [hout', Set.mem_Iio] using hu))).trans (hmem hu)
  have slot_le : z.regs (producerBank Instances.heap) ≤ a.regs Instances.heap := by
    have := Nat.mul_le_mul_right (6 + 2 * (n * D m)) (show 1 ≤ a.regs Instances.produced by omega)
    rw [zh, hout.2.2.2.2.2.1, ← haout, ← haprod]
    omega
  obtain ⟨r, S, hr, rs, rf, hS, hcoarse, hit, wit, frame, bank, ctrl⟩ :=
    exec_record values hlen hD hg hp hN hv hW a z hout zmem hheap idx hidx zdst zo zh slot_le
      (by simpa only [Block.Realizes, Block.read, hout', Data.comap_mem, zm, V]
            using And.intro cd (And.intro cL cR))
  have rlow (j : Fin 416) (hj : j.val < 64) : r.regs j = z.regs j := bank ⟨j.val, hj⟩
  let t := r.set (producerBank Instances.heap) (r.regs (producerBank Instances.output))
  have ht : ExecWithin (w + 2) reset r t 1 := exec_reset r
  have tset (j : Fin 416) (hj : j ≠ producerBank Instances.heap) : t.regs j = r.regs j :=
    Data.set_regs_of_ne hj _
  have theap : t.regs (producerBank Instances.heap) = r.regs (producerBank Instances.output) :=
    Data.set_regs_self _ _ _
  obtain ⟨ti, tl, ts_reg, tscans, tflag, t1⟩ :
      t.regs Reg.index = i ∧ t.regs Reg.limit = a.regs Instances.produced ∧
      t.regs Reg.scans = x.regs Reg.scans ∧ t.regs (recordBank RecordWitness.Reg.scans) = S ∧
      t.regs (recordBank RecordWitness.Reg.found) = r.regs (recordBank RecordWitness.Reg.found) ∧
      t.regs Reg.one = 1 := by clear hc hs hr; regs_frame
  have fits := FixedPrime.return_fits hW
    (FixedPrime.produced_le V hout hD hDn hg) hiM hscans hcoarse
  obtain ⟨y, hy, ym, yi, yl, ys, yf, ypres⟩ :=
    FixedPrime.exec_receive t ti tl ts_reg tscans tflag t1 fits.1 fits.2
  obtain ⟨y1, yprod, yheap_eq, wA, wB, wC⟩ :
      y.regs Reg.one = 1 ∧
      y.regs (producerBank Instances.produced) = i + 1 ∧
      y.regs (producerBank Instances.heap) = y.regs (producerBank Instances.output) ∧
      y.regs (recordBank RecordWitness.Reg.witnessA) =
        r.regs (recordBank RecordWitness.Reg.witnessA) ∧
      y.regs (recordBank RecordWitness.Reg.witnessB) =
        r.regs (recordBank RecordWitness.Reg.witnessB) ∧
      y.regs (recordBank RecordWitness.Reg.witnessC) =
        r.regs (recordBank RecordWitness.Reg.witnessC) := by clear hc hs hr hy; regs_frame
  have ycursor : Cursor n (D m) g p V (y.comap producerBank) :=
    ccursor.transfer fun j _ _ _ hheap =>
      (ypres _ (Or.inl (j.isLt.trans (by decide)))).trans
        ((Data.set_regs_of_ne (fun he => hheap (hf he)) _).trans
          ((bank j).trans ((Data.set_regs_of_ne
            (fun he => absurd (congrArg Fin.val he) (by change j.val ≠ 64; omega)) _).trans
            (hf.extend_apply _ _ j))))
  let Q := RecordProduct.recordQueryCount n (D m) p V idx
  let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m) hDn
  let T := 40 * (n * D m) + 66 +
    (RecordBoxProduct.timeBound (m := m)
      (RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q) +
      5 * Nat.sqrt (D m) + 8 * Q + (42 * pieceSize (D m) g + 28) * S + 52) + 8
  have he : ExecWithin (w + 2) step x y T :=
    (hs.seq (hz.seq (hr.seq (ht.seq hy)))).mono (by dsimp only [T, Q, V]; omega)
  refine ⟨y, S, T, he, by dsimp only [T, Q, FixedPrime.recordBase, V]; omega,
    yi, yf ▸ yl, y1, ys, yf ▸ rf, yf ▸ hS, hcoarse,
    by simpa only [yf, FixedPrime.recordHit, weightSum] using hit,
    fun hh => by simpa only [wA, wB, wC] using wit (yf ▸ hh),
    fun u hu => (congrFun ym u).trans
      ((frame u (by rw [zh]; omega)).trans (cm u (by rw [hout']; omega))),
    ycursor, yprod, yheap_eq⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
