/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.FusionTree.WordRAM.Node.Initial
public import CslibFrontier.DataStructure.FusionTree.WordRAM.Node.Correction
import Batteries.Data.Nat.Bitwise.Lemmas
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Constant-time full-key fusion-node queries

This width-indexed standard-basis RAM program returns the true inclusive rank of every
bounded query in a sorted internal node. Its constants are actual preprocessing witnesses,
loaded from the contiguous eighteen-word header. The program charges header loads, all
register transfers, both stride-two full-key neighbor loads, multiword highest-bit arithmetic,
and the second compression and rank. Memory and the original query and pointer are preserved.

The large-width branch assumes `2 ≤ n ≤ branching w` and `9 ≤ Nat.log 2 w`. Leaves,
small-width binary nodes and tree traversal are separate. No preprocessing-time bound is
claimed. No correctness or execution oracle is a parameter of the representation.

## Main definitions

* `NodeProgram.boundaryQuery`, `NodeProgram.correction`, `NodeProgram.finish`: second sketch-rank
  query at the prefix boundary, neighbor correction and output writeback stages.
* `NodeProgram.code`: the actual node query, depending only on physical width.

## Main results

* `NodeProgram.exec`: true inclusive full-key rank within 201000 standard instructions.
* `NodeProgram.exists_preprocessing`: actual fitting preprocessing witnesses for this query.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.DataStructure.FusionTree.WordRAM.NodeProgram

open Cslib.WordRAM Cslib.BitString Cslib.DataStructure.FusionTree

/-- The zero query bit needs a strict upper-boundary rank; the one bit needs an inclusive
lower-boundary rank. Both calls include query compression and all transfers. -/
def boundaryQuery : Code .standard registers :=
  .branch (.eq (boundaryBank 9) zero)
    (secondQuery true (boundaryBank 8)) (secondQuery false (boundaryBank 7))

/-- On a miss, compute the highest differing bit and query its sibling boundary. -/
def correction (w : ℕ) : Code .standard registers :=
  .seq (highest w) (.seq boundaries boundaryQuery)

/-- Exact hits return the first cut. Misses execute the actual full-key correction. -/
def finish (w : ℕ) : Code .standard registers :=
  .branch (.eq divergence zero) (.op (.copy out cut)) (correction w)

/-- Complete width-indexed internal-node query. Node-dependent constants occur only in RAM. -/
def code (w : ℕ) : Code .standard registers := .seq readHeader (.seq initial (finish w))

private theorem size_sketchQuery (strict : Bool) : (sketchQuery strict).size = 119 := by
  have hcomp : compress.size = 102 := by
    simp only [compress, Code.size, Code.size_rename, size_moves, CompressProgram.size_code]; rfl
  cases strict <;> simp [sketchQuery, rank, Code.size, size_moves, hcomp] <;> rfl

/-- One width-independent code-size bound includes both branches of every conditional. -/
theorem size_code (w : ℕ) : (code w).size ≤ 201000 := by
  have hread : readHeader.size = 55 := by
    simp only [readHeader, Code.size, Code.size_rename]; rfl
  have hnb : neighbors.size = 28 := by
    simp only [neighbors, Code.size, Code.size_rename, size_moves]; rfl
  have hinit : initial.size = 152 := by
    simp only [initial, saveNeighbor, Code.size, size_sketchQuery, hnb]
  have hbnd : boundaries.size = 13 := by
    simp only [boundaries, Code.size, Code.size_rename, size_moves]; rfl
  have hbq : boundaryQuery.size = 244 := by
    simp only [boundaryQuery, secondQuery, Code.size, size_sketchQuery]
  have hm := MSB.Program.size_scalarCode w
  simp only [code, finish, correction, highest, Code.size, Code.size_rename,
    hread, hinit, hbnd, hbq]
  omega

private theorem preserves_bank {k offset : ℕ} {hk : offset + k ≤ registers} (ho : 40 ≤ offset)
    (c : Code .standard k) {i : Fin registers} (hhi : i.val < 39) :
    (c.rename (bank offset hk)).Preserves i :=
  c.preserves_rename_of_offset _ (fun _ => rfl) i (Or.inl (by omega))

private theorem preserves_moves {xs : List (Fin registers × Fin registers)} {i : Fin registers}
    (hxs : ∀ p ∈ xs, 40 ≤ p.1.val) (hhi : i.val < 39) : (moves xs).Preserves i := by
  induction xs with
  | nil => intro h; have : (39 : ℕ) = i.val := congrArg Fin.val (Option.some.inj h); omega
  | cons p ps ih =>
    refine ⟨fun h => ?_, ih fun q hq => hxs q (List.mem_cons_of_mem p hq)⟩
    have := hxs p List.mem_cons_self
    have := congrArg Fin.val (Option.some.inj h)
    omega

private theorem preserves_sketchQuery (strict : Bool) {i : Fin registers} (hhi : i.val < 39) :
    (sketchQuery strict).Preserves i :=
  ⟨⟨preserves_moves (by simp [compressionInputs, compressBank, bank]) hhi,
    preserves_bank (by decide) _ hhi⟩,
   ⟨preserves_moves (by cases strict <;> simp [rankInputs, rankBank, bank]) hhi,
    preserves_bank (by decide) _ hhi⟩⟩

/-- Registers 31 through 38 belong to the outer traversal. They are outside every node
workspace; the terminal self-copy used by `moves` occupies register 39 instead. -/
private theorem preserves_caller (w : ℕ) (i : Fin registers) (hlo : 31 ≤ i.val)
    (hhi : i.val < 39) : (code w).Preserves i := by
  have ne_i {d : Fin registers} (hd : d.val < 31 ∨ 40 ≤ d.val) : some d ≠ some i := by
    intro h; have := congrArg Fin.val (Option.some.inj h); omega
  have low {d : Fin registers} (hd : d.val < 31 := by decide) := ne_i (Or.inl hd)
  have high {d : Fin registers} (hd : 40 ≤ d.val := by decide) := ne_i (Or.inr hd)
  have hsecond (strict : Bool) (src : Fin registers) : (secondQuery strict src).Preserves i :=
    ⟨low, preserves_sketchQuery strict hhi, low⟩
  have hnb : neighbors.Preserves i :=
    ⟨preserves_moves (by simp [neighborInputs, neighborBank, bank]) hhi,
      ⟨high, high, high⟩, preserves_bank (by decide) _ hhi⟩
  have hread : readHeader.Preserves i :=
    ⟨low, ReadHeaderProgram.code.preserves_rename_of_offset _ (fun _ => rfl) i (Or.inr (by omega))⟩
  have hinit : initial.Preserves i :=
    ⟨low, preserves_sketchQuery false hhi, low, hnb, low, low, low⟩
  have hcorr : (correction w).Preserves i :=
    ⟨⟨high, preserves_bank (by decide) _ hhi, low⟩,
      ⟨preserves_moves (by simp [boundaryInputs, boundaryBank, bank]) hhi,
        preserves_bank (by decide) _ hhi⟩,
      hsecond true _, hsecond false _⟩
  exact ⟨hread, hinit, low, hcorr⟩

/-- Every actual execution frames the caller's eight traversal registers. -/
theorem caller_regs_eq {w t : ℕ} {x y : Data registers} (he : Exec w (code w) x y t)
    (i : Fin registers) (hlo : 31 ≤ i.val) (hhi : i.val < 39) : y.regs i = x.regs i :=
  he.regs_eq (preserves_caller w i hlo hhi)

/-- A miss executes the concrete highest-bit and boundary programs, returning the
mathematical sibling-boundary rank. All incoming workspace registers may be arbitrary. -/
private theorem exec_correction {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hw : 3 ≤ w) (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Ready p q a x) (hq : Fits w q) (j : Fin n)
    (hj : keys j ≠ q) (hd : x.regs divergence = keys j ^^^ q) (hz : x.regs zero = 0) :
    ∃ y, ExecWithin w (correction w) x y 200138 ∧
      y.regs out = boundaryRank w keys q j ∧ Ready p q a y ∧ y.mem = x.mem := by
  let d := highestDiff w (keys j) q
  have hdiv : Fits w (keys j ^^^ q) := Nat.xor_lt_two_pow (hk j) hq
  obtain ⟨u, heu, hu, hum, hup⟩ := exec_highest hw x hdiv hd
  have hru : Ready p q a u := hx.except_scratch position (by decide) (by decide) hum hup
  have hpos : u.regs position = d :=
    hu.trans (highestDiff_eq_log2_xor (hk j) hq hj).symm
  have hdw : d < w := (highestDiff_spec (hk j) hq hj).1
  obtain ⟨v, hev, hfv, hl, hh, hb⟩ := exec_boundaries u hq hdw hru.query_eq hpos
  have hrv := hru.frame hfv
  have hvzero : v.regs zero = 0 := by regs_frame
  obtain ⟨hlfit, hhfit⟩ := boundary_fits hq hdw
  by_cases hbit : q.testBit (highestDiff w (keys j) q) = false
  · have htest : (Cond.eq (boundaryBank 9) zero).Holds v := by
      simpa only [Cond.holds_eq, hb, hvzero, bit_eq_zero_iff] using hbit
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_secondQuery p true (boundaryBank 8)
      (by omega) hn hs hk hnB hlarge v hrv hhfit hh
    refine ⟨y, heu.seq (hev.within.seq
      ((ExecWithin.branch_pos (neg := secondQuery false (boundaryBank 7)) htest hey.within).mono
        (by decide : 122 ≤ 123))), ?_, hry, hym.trans (hfv.1.trans hum)⟩
    simpa [sketchCut, boundaryRank, hbit] using hy
  · have htest : ¬(Cond.eq (boundaryBank 9) zero).Holds v := by
      simpa only [Cond.holds_eq, hb, hvzero, bit_eq_zero_iff] using hbit
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_secondQuery p false (boundaryBank 7)
      (by omega) hn hs hk hnB hlarge v hrv hlfit hl
    refine ⟨y, heu.seq (hev.within.seq
      (ExecWithin.branch_neg (pos := secondQuery true (boundaryBank 8)) htest hey.within)),
      ?_, hry, hym.trans (hfv.1.trans hum)⟩
    simpa [sketchCut, boundaryRank, Bool.eq_true_of_ne_false hbit, sketchRank] using hy

/-- Every bounded query receives its true inclusive full-key rank. The physical program
depends only on `w`, and 201000 bounds the actual instruction count uniformly in `w`, `n`,
the keys, their preprocessing witnesses and the query. Registers 0 and 1 and all memory
are preserved. The address premise covers the last full key in the stride-two table. -/
theorem exec {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hn : 2 ≤ n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hr : Rep p a x.mem) (hq : Fits w q)
    (ha : Fits w (a + 18 + (n - 1) * 2))
    (hxq : x.regs query = q) (hxa : x.regs pointer = a) :
    ∃ y, ExecWithin w (code w) x y 201000 ∧ y.regs out = upperRank keys q ∧
      y.mem = x.mem ∧ y.regs query = q ∧ y.regs pointer = a := by
  have hn0 : 0 < n := by omega
  have hw : 3 ≤ w := by
    have hb := branching_capacity hlarge
    have hB := two_le_branching w
    have hp : branching w ≤ branching w ^ 5 := Nat.le_self_pow (by decide) _
    omega
  obtain ⟨u, heu, hru, hum⟩ := exec_readHeader p x hr (ha.of_le (by omega)) hxq hxa
  obtain ⟨v, hev, hrv, hvm, hcut, hz, j, hj, hd, hnear, hbest⟩ :=
    exec_initial p (by omega) hn0 hs hk hnB hlarge u hru hq ha
  have hcorrect := NodeSemantics.correct hs hk hq j hbest
  by_cases hhit : keys j = q
  · have htest : (Cond.eq divergence zero).Holds v := by
      simp only [Cond.holds_eq, hd, hz, hhit, Nat.xor_self]
    let y := v.set out (sketchRank w keys q)
    have hey : Exec (B := .standard) w (.op (.copy out cut)) v y 1 := by
      simpa only [hcut] using (Exec.copy (B := .standard) (w := w) (d := out) (s := cut) (x := v))
    have hry : Ready p q a y := hrv.set_scratch out _ (by decide) (by decide)
    refine ⟨y, (heu.within.seq (hev.seq (Exec.branch_pos htest hey).within)).mono (by decide), ?_,
      hvm.trans hum, hry.query_eq, hry.pointer_eq⟩
    simpa only [y, Data.set_regs, Function.update_self, hhit, ↓reduceIte] using hcorrect
  · have htest : ¬(Cond.eq divergence zero).Holds v := by
      simp only [Cond.holds_eq, hd, hz]
      exact fun h => hhit (Nat.xor_eq_zero_iff.mp h)
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_correction p hw hn0 hs hk hnB hlarge v hrv hq j
      hhit hd hz
    refine ⟨y, (heu.within.seq (hev.seq (ExecWithin.branch_neg htest hey))).mono (by decide), ?_,
      hym.trans (hvm.trans hum), hry.query_eq, hry.pointer_eq⟩
    exact hy.trans (by simpa only [ite_eq_right hhit] using hcorrect)

/-- Real preprocessing witnesses exist, all fifteen stored words fit, and the same
width-indexed program answers every bounded query on every memory realizing those witnesses.
The witness construction has no preprocessing-time assertion. -/
theorem exists_preprocessing {w n : ℕ} {keys : Fin n → ℕ}
    (hn : 2 ≤ n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w) :
    ∃ p : NodeParameters w keys, (∀ j, Fits w (p.words j)) ∧
      ∀ (q a : ℕ) (x : Data registers), Rep p a x.mem → Fits w q →
        Fits w (a + 18 + (n - 1) * 2) → x.regs query = q → x.regs pointer = a →
        ∃ y, ExecWithin w (code w) x y 201000 ∧ y.regs out = upperRank keys q ∧
          y.mem = x.mem ∧ y.regs query = q ∧ y.regs pointer = a := by
  obtain ⟨p⟩ := NodeParameters.exists_parameters hn hs hk hnB hlarge
  exact ⟨p, p.words_fit hn hs hk hnB hlarge,
    fun _ _ x hr hq ha hxq hxa => exec p hn hs hk hnB hlarge x hr hq ha hxq hxa⟩

end Cslib.DataStructure.FusionTree.WordRAM.NodeProgram
