/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
public import CslibFrontier.Computability.WordRAM.Function
public import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Foundations.Data.List.Forall2
import CslibFrontier.Foundations.Data.Nat.Bitwise.Projection
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.GetD

/-!
# Word-RAM dense Gaussian elimination over `𝔽₂` with one row per word

A checked standard-basis Word-RAM implementation of the dense elimination decider
`Cslib.Complexity.XORSAT.Dense.decide`, with a word-parallel instruction bound.

**Representation and width condition.** A well-formed `m × n` instance (`Instance`: every row has
the declared width `n`) is laid out in input memory as `[n, m]` followed by one word per row,
`rowWord e`, with coefficient `j` at bit `j` and the right-hand side at bit `n`. Admitted widths
(`FitsWidth`) satisfy `w ≥ n + 1`, so that one row fits in one word, and fit the row addresses
`3, …, m + 2`. Each `^^^` instruction therefore processes a whole row of `n + 1` coefficient
bits: the bound `30 (m + 1) (n + 1)` counts word instructions under this one-row-per-word
convention, and is not the Θ(m n²) bit-operation cost. The packed input is an uncharged
representation convention (the Word-RAM input placement convention); it differs from the
multi-tape encoding `encInput` of `XORSAT.Dense`, and this module makes no claim about running
time on that bit encoding.

**Domain.** The packed words cannot record row lengths, so the domain is restricted to
well-formed instances. On that domain the row-width conjunct of `XORSAT.Dense.decide` is constantly
`true`, and the program computes exactly the elimination part; `mem_satisfiable_iff` relates the
decided set to `{q : Input | Width q.width q.rows ∧ Satisfiable q.width q.rows}`.

**Algorithm.** For each column `c < n`, the program scans the rows for the first word with bit
`c` set (the pivot of `XORSAT.Dense.step`), then XORs the pivot into every row with bit `c` set
(the pivot row itself becomes zero in its live bits, matching `clear p p`). It finally checks that
no row has bit `n` set. Every address calculation, load, store, shift, mask, XOR, comparison, loop
test and the final `halt` is charged by the Word-RAM semantics.

## Main definitions

* `Cslib.Algorithms.WordRAM.XORSATDense.rowWord`: the packed word of a dense row.
* `Cslib.Algorithms.WordRAM.XORSATDense.RowRel`: a packed word represents a partially eliminated
  row.
* `Cslib.Algorithms.WordRAM.XORSATDense.colStep`, `cols`: elimination columns on packed rows.
* `Cslib.Algorithms.WordRAM.XORSATDense.Instance`, `encode`, `FitsWidth`: well-formed instances,
  their word layout and the admitted widths.
* `Cslib.Algorithms.WordRAM.XORSATDense.program`: a fixed `Program .standard 14`.

## Main results

* `Cslib.Algorithms.WordRAM.XORSATDense.rowRel_rowWord`: the packed word of a row of length `n`
  represents it before elimination.
* `Cslib.Algorithms.WordRAM.XORSATDense.forall₂_cols`, `decide_eq_cols`: packed elimination
  represents `XORSAT.Dense.step^[c]` bit for bit and agrees with `XORSAT.Dense.decide`.
* `Cslib.Algorithms.WordRAM.XORSATDense.computesInTime_decide`: `program` computes
  `(XORSAT.Dense.decide q).toNat` in at most `30 (m + 1) (n + 1)` instructions at every admitted
  width `w ≥ n + 1`.
* `Cslib.Algorithms.WordRAM.XORSATDense.decidesInTime_decide`,
  `uniformDecidableInTime_decide`: uniform Word-RAM decision of dense XOR-SAT satisfiability within
  the same bound, with `inputAdmissible`.

## References

* [H. Chen, *A rendezvous of logic, complexity, and algebra*][Chen2006CSP], the elimination
  argument formalized in `XORSAT.Dense`.
-/

public section

namespace Cslib.Algorithms.WordRAM.XORSATDense

open Cslib.Complexity.XORSAT.Dense

/-! ## Packed rows -/

/-- The packed word of a dense row: coefficients at bits `0, …, n - 1`, right-hand side at bit
`n`, where `n` is the number of coefficients (least significant bit first, `lsbValue`). -/
@[expose]
def rowWord (e : Row) : ℕ := Cslib.BitString.lsbValue (e.coeffs ++ [e.rhs])

/-! ## Packed rows representing a partially eliminated row -/

/-- After `c` elimination columns of an `n`-column system, the word `x` represents the row `e`
(which has `n - c` remaining coefficients): bit `c + j` is coefficient `j`, bit `n` is the
right-hand side, and `x` has at most `n + 1` bits. Bits below `c` are unconstrained. -/
structure RowRel (n c x : ℕ) (e : Row) : Prop where
  len : e.coeffs.length = n - c
  coeff : ∀ j < n - c, x.testBit (c + j) = e.coeffs.getD j false
  rhs : x.testBit n = e.rhs
  lt : x < 2 ^ (n + 1)

/-- The packed word of a row with `n` coefficients represents it before elimination. -/
theorem rowRel_rowWord {n : ℕ} {e : Row} (h : e.coeffs.length = n) :
    RowRel n 0 (rowWord e) e where
  len := by simpa using h
  coeff j hj := by
    rw [rowWord, Cslib.BitString.testBit_lsbValue, zero_add]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  rhs := by
    rw [rowWord, Cslib.BitString.testBit_lsbValue]
    simp [List.getD_eq_getElem?_getD, h]
  lt := by
    have := Cslib.BitString.lsbValue_lt (e.coeffs ++ [e.rhs])
    unfold rowWord
    simpa [h] using this

private theorem RowRel.testBit_eq_headD {n c x : ℕ} {e : Row} (h : RowRel n c x e) (hc : c < n) :
    x.testBit c = e.coeffs.headD false := by
  have := h.coeff 0 (by omega)
  rw [Nat.add_zero] at this
  rw [this]
  cases e.coeffs <;> rfl

/-! ## One elimination column on packed rows -/

/-- The pivot word for column `c`: the first row with bit `c` set, or `0` if there is none. -/
@[expose]
def pivotWord (c : ℕ) (W : List ℕ) : ℕ := (W.find? fun x => x.testBit c).getD 0

/-- Eliminate column `c` from one packed row using the pivot word `pv`. -/
@[expose]
def elimWord (c pv x : ℕ) : ℕ := if x.testBit c then x ^^^ pv else x

/-- One elimination column on packed rows. -/
@[expose]
def colStep (c : ℕ) (W : List ℕ) : List ℕ := W.map (elimWord c (pivotWord c W))

/-- Packed rows after the first `c` elimination columns. -/
@[expose]
def cols (W : List ℕ) : ℕ → List ℕ
  | 0 => W
  | c + 1 => colStep c (cols W c)

private theorem all_eq_of_forall₂ {α β : Type*} {R : α → β → Prop} {p : α → Bool}
    {q : β → Bool} (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.all p = l₂.all q
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [List.all_cons, hpq _ _ h, all_eq_of_forall₂ hpq t]

/-- `find?` on related lists returns related results when the predicates agree. -/
private theorem find?_rel {α β : Type*} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (l₁.find? p = none ∧ l₂.find? q = none) ∨
        ∃ a b, l₁.find? p = some a ∧ l₂.find? q = some b ∧ R a b
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | a :: _, b :: _, .cons h t => by
    have hab := hpq a b h
    by_cases ha : p a = true
    · exact .inr ⟨a, b, by simp [ha], by simp [← hab, ha], h⟩
    · have hb : q b = false := by rw [← hab]; simpa using ha
      have ha' : p a = false := by simpa using ha
      simpa [List.find?_cons, ha', hb] using find?_rel hpq t

private theorem getD_zipWith_xor (a b : List Bool) (j : ℕ) (ha : j < a.length)
    (hb : j < b.length) :
    (a.zipWith Bool.xor b).getD j false = (a.getD j false ^^ b.getD j false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]

/-- A non-pivot row with bit `c` clear just drops coefficient `c`. -/
private theorem rowRel_drop {n c x : ℕ} {e : Row} (h : RowRel n c x e) (hc : c < n) :
    RowRel n (c + 1) x ⟨e.coeffs.tail, e.rhs⟩ where
  len := by simp [h.len]; omega
  coeff j hj := by
    have := h.coeff (j + 1) (by omega)
    rw [show c + (j + 1) = c + 1 + j by omega] at this
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_tail] using this
  rhs := h.rhs
  lt := h.lt

/-- XOR of two related rows is related to the cleared row. -/
private theorem rowRel_xor {n c x y : ℕ} {e p : Row} (hx : RowRel n c x e)
    (hy : RowRel n c y p) (hc : c < n) :
    RowRel n (c + 1) (x ^^^ y) ⟨e.coeffs.tail.zipWith Bool.xor p.coeffs.tail, e.rhs ^^ p.rhs⟩ where
  len := by simp [hx.len, hy.len]; omega
  coeff j hj := by
    have h1 := hx.coeff (j + 1) (by omega)
    have h2 := hy.coeff (j + 1) (by omega)
    rw [show c + (j + 1) = c + 1 + j by omega] at h1 h2
    rw [Nat.testBit_xor, h1, h2, getD_zipWith_xor _ _ _ (by simp [hx.len]; omega)
      (by simp [hy.len]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_tail]
  rhs := by rw [Nat.testBit_xor, hx.rhs, hy.rhs]
  lt := Nat.xor_lt_two_pow hx.lt hy.lt

/-- One packed elimination column represents one `XORSAT.Dense.step`. -/
private theorem forall₂_colStep {n c : ℕ} (hc : c < n) {W : List ℕ} {F : System}
    (h : List.Forall₂ (RowRel n c) W F) :
    List.Forall₂ (RowRel n (c + 1)) (colStep c W) (step F) := by
  have hpq : ∀ x e, RowRel n c x e → x.testBit c = e.coeffs.headD false :=
    fun x e hxe => hxe.testBit_eq_headD hc
  unfold colStep pivotWord step
  rcases find?_rel hpq h with ⟨hW, hF⟩ | ⟨xp, ep, hW, hF, hp⟩
  · rw [hW, hF, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    have hmem := (List.forall₂_and_left (p := fun x => x ∈ W) W F).2 ⟨fun _ hx => hx, h⟩
    refine hmem.imp fun x e ⟨hx, hxe⟩ => ?_
    have hxc : x.testBit c = false := by
      simpa using List.find?_eq_none.mp hW x hx
    have hec : e.coeffs.headD false = false := (hpq x e hxe) ▸ hxc
    simp only [elimWord, clear, hxc, hec, Bool.false_eq_true, ↓reduceIte]
    exact rowRel_drop hxe hc
  · rw [hW, hF, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h.imp fun x e hxe => ?_
    have hxe' := hpq x e hxe
    by_cases hb : x.testBit c = true
    · have he : e.coeffs.headD false = true := hxe' ▸ hb
      simp only [Option.getD_some, elimWord, clear, hb, he, ↓reduceIte]
      exact rowRel_xor hxe hp hc
    · have hb' : x.testBit c = false := by simpa using hb
      have he : e.coeffs.headD false = false := hxe' ▸ hb'
      simp only [elimWord, clear, hb', he, Bool.false_eq_true, ↓reduceIte]
      exact rowRel_drop hxe hc

/-- After `c ≤ n` packed columns, the packed rows represent `step^[c]` of the system. -/
theorem forall₂_cols {n : ℕ} {W : List ℕ} {F : System}
    (h : List.Forall₂ (RowRel n 0) W F) : ∀ c ≤ n,
      List.Forall₂ (RowRel n c) (cols W c) (step^[c] F)
  | 0, _ => by simpa [cols] using h
  | c + 1, hc => by
    rw [cols, Function.iterate_succ_apply']
    exact forall₂_colStep (by omega) (forall₂_cols h c (by omega))

/-- Packing every row of a system of width `n` gives related words. -/
private theorem forall₂_rowWord {n : ℕ} {F : System} (h : Width n F) :
    List.Forall₂ (RowRel n 0) (F.map rowWord) F :=
  List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun e he => rowRel_rowWord (h e he))

/-- On a well-formed instance, the dense decider is the right-hand-side check on the packed rows
after `width` packed columns. -/
theorem decide_eq_cols (q : Input) (hq : Width q.width q.rows) :
    decide q = (cols (q.rows.map rowWord) q.width).all (fun x => !x.testBit q.width) := by
  have hwidth : q.rows.all (fun e => Decidable.decide (e.coeffs.length = q.width)) = true :=
    List.all_eq_true.mpr fun e he => decide_eq_true (hq e he)
  unfold Cslib.Complexity.XORSAT.Dense.decide
  rw [hwidth, Bool.true_and]
  exact (all_eq_of_forall₂ (fun x e hxe => by rw [hxe.rhs])
    (forall₂_cols (forall₂_rowWord hq) q.width le_rfl)).symm

/-! ## The Word-RAM program -/

section Program

open Cslib.WordRAM

/-- Number of columns `n`. -/
private abbrev rN : Fin 14 := 0
/-- Number of rows `m`. -/
private abbrev rM : Fin 14 := 1
/-- Base address `3` of the packed rows. -/
private abbrev rBase : Fin 14 := 2
/-- Constant one. -/
private abbrev rOne : Fin 14 := 3
/-- Constant zero. -/
private abbrev rZero : Fin 14 := 4
/-- Current column `c`. -/
private abbrev rC : Fin 14 := 5
/-- Current row `k`. -/
private abbrev rK : Fin 14 := 6
/-- Row address. -/
private abbrev rA : Fin 14 := 7
/-- Current row word. -/
private abbrev rX : Fin 14 := 8
/-- Tested bit. -/
private abbrev rB : Fin 14 := 9
/-- Pivot word. -/
private abbrev rPiv : Fin 14 := 10
/-- Whether a pivot has been found. -/
private abbrev rFound : Fin 14 := 11
/-- Answer. -/
private abbrev rOk : Fin 14 := 12
/-- Scratch register. -/
private abbrev rT : Fin 14 := 13

/-- One step of the pivot search: remember row `k` if it is the first with bit `c` set. -/
private def searchBody : Code .standard 14 := ram[
  rA ← rBase + rK; rX ← *rA; rB ← rX >>> rC; rB ← rB &&& rOne;
  if rB = rOne then [ if rFound = rZero then [ rPiv ← rX; rFound ← rOne ] else [ rT ← rT ] ]
    else [ rT ← rT ];
  rK ← rK + rOne ]

private theorem exec_searchBody {w : ℕ} (y : Data 14) (v : ℕ)
    (hone : y.regs rOne = 1) (hzero : y.regs rZero = 0)
    (ha : Fits w (y.regs rBase + y.regs rK)) (hk : Fits w (y.regs rK + 1))
    (hv : y.mem (y.regs rBase + y.regs rK) = v) (hvf : Fits w v) (h1 : Fits w 1) :
    ∃ z, ExecWithin w searchBody y z 12 ∧ z.mem = y.mem ∧
      (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧
      z.regs rK = y.regs rK + 1 ∧
      z.regs rPiv = (if v.testBit (y.regs rC) = true ∧ y.regs rFound = 0 then v
        else y.regs rPiv) ∧
      z.regs rFound = (if v.testBit (y.regs rC) = true ∧ y.regs rFound = 0 then 1
        else y.regs rFound) := by
  have hb : Fits w (v.testBit (y.regs rC)).toNat := h1.of_le (Bool.toNat_le _)
  have hs : Fits w (v >>> y.regs rC) := hvf.of_le (Nat.shiftRight_le _ _)
  refine WP.exists_execWithin ?_
  wram_exec [searchBody, hone, hzero, ha, hk, hv, hvf, hb, hs, h1, Nat.shiftRight_and_one]
  all_goals
    refine ⟨by wram_simp, fun i hi => by
        fin_cases i <;> first | exact absurd hi (by decide) | wram_simp,
      by wram_simp, ?_, ?_⟩ <;> wram_simp <;> simp_all

/-! ### Pure facts used by the loop invariants -/

private theorem getD_mem {W : List ℕ} {j : ℕ} (hj : j < W.length) : W.getD j 0 ∈ W := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

private theorem take_succ_eq {W : List ℕ} {k : ℕ} (hk : k < W.length) :
    W.take (k + 1) = W.take k ++ [W.getD k 0] := by
  rw [List.take_succ_eq_append_getElem hk, List.getD_eq_getElem _ _ hk]

/-- Pivot search over the first `k` rows. -/
private def prefPiv (c : ℕ) (W : List ℕ) (k : ℕ) : Option ℕ := (W.take k).find? fun x => x.testBit c

private theorem prefPiv_succ {c : ℕ} {W : List ℕ} {k : ℕ} (hk : k < W.length) :
    prefPiv c W (k + 1) =
      (prefPiv c W k).or (if (W.getD k 0).testBit c then some (W.getD k 0) else none) := by
  unfold prefPiv
  rw [take_succ_eq hk, List.find?_append]
  generalize W.getD k 0 = v
  cases h : v.testBit c <;> simp [h]

private theorem prefPiv_length (c : ℕ) (W : List ℕ) :
    (prefPiv c W W.length).getD 0 = pivotWord c W := by
  simp [prefPiv, pivotWord]

private theorem pivotWord_lt {c B : ℕ} {W : List ℕ} (hB : 0 < B) (h : ∀ x ∈ W, x < B) :
    pivotWord c W < B := by
  unfold pivotWord
  cases hf : W.find? (fun x => x.testBit c) with
  | none => simpa using hB
  | some u => simpa using h u (List.mem_of_find?_eq_some hf)

private theorem getD_colStep {c : ℕ} {W : List ℕ} {j : ℕ} (hj : j < W.length) :
    (colStep c W).getD j 0 = elimWord c (pivotWord c W) (W.getD j 0) := by
  rw [colStep, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

/-- The pivot search: after the loop, `rPiv` holds `pivotWord c W`. -/
private def search : Code .standard 14 :=
  .seq (ram[ rK ← #0; rFound ← #0; rPiv ← #0 ]) (.loop (.lt rK rM) searchBody)

private theorem exec_search {w : ℕ} (W : List ℕ) (y : Data 14)
    (hm : y.regs rM = W.length) (hbase : y.regs rBase = 3) (hone : y.regs rOne = 1)
    (hzero : y.regs rZero = 0) (hmfit : Fits w (W.length + 3))
    (hmem : ∀ j < W.length, y.mem (3 + j) = W.getD j 0)
    (hWfit : ∀ x ∈ W, Fits w x) :
    ∃ z, ExecWithin w search y z (14 * W.length + 5) ∧ z.mem = y.mem ∧
      (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧
      z.regs rPiv = pivotWord (y.regs rC) W := by
  have h1 : Fits w 1 := hmfit.of_le (by omega)
  set c := y.regs rC with hc
  let P (k : ℕ) (z : Data 14) : Prop :=
    (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧ z.mem = y.mem ∧
      z.regs rPiv = (prefPiv c W k).getD 0 ∧
      z.regs rFound = (if (prefPiv c W k).isSome then 1 else 0)
  have hbody (z : Data 14) (hz : P (z.regs rK) z) (hlt : z.regs rK < W.length) :
      ∃ z', ExecWithin w searchBody z z' 12 ∧ P (z.regs rK + 1) z' ∧
        z'.regs rK = z.regs rK + 1 := by
    obtain ⟨hr, hzm, hpiv, hfound⟩ := hz
    have hzb : z.regs rBase = 3 := (hr rBase (by decide)).trans hbase
    have hzc : z.regs rC = c := hr rC (by decide)
    obtain ⟨z', he, hm', hr', hk', hpiv', hfound'⟩ := exec_searchBody z (W.getD (z.regs rK) 0)
      ((hr rOne (by decide)).trans hone) ((hr rZero (by decide)).trans hzero)
      (hmfit.of_le (by rw [hzb]; omega)) (hmfit.of_le (by omega))
      (by rw [hzm, hzb]; exact hmem _ hlt) (hWfit _ (getD_mem hlt)) h1
    refine ⟨z', he, ⟨fun i hi => (hr' i hi).trans (hr i hi), hm'.trans hzm, ?_, ?_⟩, hk'⟩
    · rw [hpiv', hzc, hfound, prefPiv_succ hlt, hpiv]
      generalize W.getD (z.regs rK) 0 = v
      cases prefPiv c W (z.regs rK) <;> cases v.testBit c <;> simp
    · rw [hfound', hzc, hfound, prefPiv_succ hlt]
      generalize W.getD (z.regs rK) 0 = v
      cases prefPiv c W (z.regs rK) <;> cases v.testBit c <;> simp
  refine WP.exists_execWithin ?_
  wram_exec [search]
  wram_call (ExecWithin.loop_count P (fun z hz => ((hz.1 rM (by decide)).trans hm)) hbody
    (by wram_simp; omega)
    ⟨fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | wram_simp,
      by wram_simp, by wram_simp; simp [prefPiv], by wram_simp; simp [prefPiv]⟩)
    with z ⟨⟨hr, hzm, hpiv, _⟩, _⟩
  exact ⟨by wram_simp; omega, hzm, hr, by rw [hpiv, prefPiv_length]⟩

/-- Eliminate column `c` from row `k` using the pivot word, and store it back. -/
private def elimBody : Code .standard 14 := ram[
  rA ← rBase + rK; rX ← *rA; rB ← rX >>> rC; rB ← rB &&& rOne;
  if rB = rOne then [ rX ← rX ^^^ rPiv ] else [ rT ← rT ];
  *rA ← rX; rK ← rK + rOne ]

private theorem exec_elimBody {w : ℕ} (y : Data 14) (v : ℕ)
    (hone : y.regs rOne = 1)
    (ha : Fits w (y.regs rBase + y.regs rK)) (hk : Fits w (y.regs rK + 1))
    (hv : y.mem (y.regs rBase + y.regs rK) = v) (hvf : Fits w v) (h1 : Fits w 1)
    (hx : Fits w (v ^^^ y.regs rPiv)) :
    ∃ z, ExecWithin w elimBody y z 12 ∧
      z.mem = Function.update y.mem (y.regs rBase + y.regs rK)
        (elimWord (y.regs rC) (y.regs rPiv) v) ∧
      (∀ i : Fin 14, (i.val < 6 ∨ i = rPiv) → z.regs i = y.regs i) ∧
      z.regs rK = y.regs rK + 1 := by
  have hb : Fits w (v.testBit (y.regs rC)).toNat := h1.of_le (Bool.toNat_le _)
  have hs : Fits w (v >>> y.regs rC) := hvf.of_le (Nat.shiftRight_le _ _)
  refine WP.exists_execWithin ?_
  wram_exec [elimBody, hone, ha, hk, hv, hvf, hb, hs, h1, hx, Nat.shiftRight_and_one]
  all_goals
    refine ⟨?_, fun i hi => by
      rcases hi with hi | rfl
      · fin_cases i <;> first | exact absurd hi (by decide) | wram_simp
      · wram_simp, by wram_simp⟩
    wram_simp
    simp_all [elimWord]

/-- The elimination pass over all rows for the current column. -/
private def elim : Code .standard 14 := .seq (ram[ rK ← #0 ]) (.loop (.lt rK rM) elimBody)

private theorem exec_elim {w n : ℕ} (W : List ℕ) (y : Data 14)
    (hm : y.regs rM = W.length) (hbase : y.regs rBase = 3) (hone : y.regs rOne = 1)
    (hmfit : Fits w (W.length + 3)) (hn : Fits w (2 ^ (n + 1) - 1))
    (hmem : ∀ j < W.length, y.mem (3 + j) = W.getD j 0)
    (hWlt : ∀ x ∈ W, x < 2 ^ (n + 1)) (hpv : y.regs rPiv < 2 ^ (n + 1)) :
    ∃ z, ExecWithin w elim y z (14 * W.length + 3) ∧
      (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧
      ∀ j < W.length, z.mem (3 + j) = elimWord (y.regs rC) (y.regs rPiv) (W.getD j 0) := by
  have h1 : Fits w 1 := hmfit.of_le (by omega)
  have hWfit : ∀ x ∈ W, Fits w x := fun x hx => hn.of_le (by have := hWlt x hx; omega)
  set c := y.regs rC with hc
  set pv := y.regs rPiv with hpvdef
  let mem (k : ℕ) : ℕ → ℕ :=
    fun a => if 3 ≤ a ∧ a < 3 + k then elimWord c pv (y.mem a) else y.mem a
  let P (k : ℕ) (z : Data 14) : Prop :=
    (∀ i : Fin 14, (i.val < 6 ∨ i = rPiv) → z.regs i = y.regs i) ∧ z.mem = mem k
  have hbody (z : Data 14) (hz : P (z.regs rK) z) (hlt : z.regs rK < W.length) :
      ∃ z', ExecWithin w elimBody z z' 12 ∧ P (z.regs rK + 1) z' ∧
        z'.regs rK = z.regs rK + 1 := by
    obtain ⟨hr, hzm⟩ := hz
    have hzb : z.regs rBase = 3 := (hr rBase (by decide)).trans hbase
    have hzc : z.regs rC = c := hr rC (by decide)
    have hzp : z.regs rPiv = pv := hr rPiv (by decide)
    have hread : z.mem (z.regs rBase + z.regs rK) = W.getD (z.regs rK) 0 := by
      rw [hzm, hzb]
      simp only [mem, show ¬(3 ≤ 3 + z.regs rK ∧ 3 + z.regs rK < 3 + z.regs rK) from by omega,
        ↓reduceIte]
      exact hmem _ hlt
    have hvlt := hWlt _ (getD_mem hlt)
    obtain ⟨z', he, hm', hr', hk'⟩ := exec_elimBody z (W.getD (z.regs rK) 0)
      ((hr rOne (by decide)).trans hone)
      (hmfit.of_le (by rw [hzb]; omega)) (hmfit.of_le (by omega)) hread
      (hWfit _ (getD_mem hlt)) h1
      (hn.of_le (by rw [hzp]; have := Nat.xor_lt_two_pow hvlt hpv; omega))
    refine ⟨z', he, ⟨fun i hi => (hr' i hi).trans (hr i hi), ?_⟩, hk'⟩
    rw [hm', hzm, hzb, hzc, hzp]
    funext a
    by_cases ha : a = 3 + z.regs rK
    · subst ha
      rw [Function.update_self]
      simp only [mem, show 3 ≤ 3 + z.regs rK ∧ 3 + z.regs rK < 3 + (z.regs rK + 1) from
        ⟨by omega, by omega⟩, and_self, ↓reduceIte, hmem _ hlt]
    · rw [Function.update_of_ne ha]
      simp only [mem]
      split_ifs <;> first | rfl | omega
  refine WP.exists_execWithin ?_
  wram_exec [elim]
  wram_call (ExecWithin.loop_count P (fun z hz => ((hz.1 rM (by decide)).trans hm)) hbody
    (by wram_simp; omega)
    ⟨fun i hi => by rcases hi with hi | rfl
                    · fin_cases i <;> first | exact absurd hi (by decide) | wram_simp
                    · wram_simp,
      by wram_simp; funext a; simp only [mem]; split_ifs <;> first | rfl | omega⟩)
    with z ⟨⟨hr, hzm⟩, _⟩
  refine ⟨by wram_simp; omega, fun i hi => hr i (.inl hi), fun j hj => ?_⟩
  rw [hzm]
  simp only [mem, show 3 ≤ 3 + j ∧ 3 + j < 3 + W.length from ⟨by omega, by omega⟩, and_self,
    ↓reduceIte, hmem j hj]

/-- One elimination column: pivot search, elimination pass, next column. -/
private def colBody : Code .standard 14 := .seq search (.seq elim (ram[ rC ← rC + rOne ]))

private theorem exec_colBody {w n : ℕ} (W : List ℕ) (y : Data 14)
    (hm : y.regs rM = W.length) (hbase : y.regs rBase = 3) (hone : y.regs rOne = 1)
    (hzero : y.regs rZero = 0) (hmfit : Fits w (W.length + 3))
    (hn : Fits w (2 ^ (n + 1) - 1)) (hc : Fits w (y.regs rC + 1))
    (hmem : ∀ j < W.length, y.mem (3 + j) = W.getD j 0)
    (hWlt : ∀ x ∈ W, x < 2 ^ (n + 1)) :
    ∃ z, ExecWithin w colBody y z (28 * W.length + 9) ∧
      (∀ i : Fin 14, i.val < 5 → z.regs i = y.regs i) ∧ z.regs rC = y.regs rC + 1 ∧
      ∀ j < W.length, z.mem (3 + j) = (colStep (y.regs rC) W).getD j 0 := by
  have hWfit : ∀ x ∈ W, Fits w x := fun x hx => hn.of_le (by have := hWlt x hx; omega)
  obtain ⟨y₁, he₁, hm₁, hr₁, hp₁⟩ := exec_search W y hm hbase hone hzero hmfit hmem hWfit
  have hpv : y₁.regs rPiv < 2 ^ (n + 1) := by
    rw [hp₁]; exact pivotWord_lt (Nat.two_pow_pos _) hWlt
  obtain ⟨y₂, he₂, hr₂, hm₂⟩ := exec_elim (n := n) W y₁
    ((hr₁ rM (by decide)).trans hm) ((hr₁ rBase (by decide)).trans hbase)
    ((hr₁ rOne (by decide)).trans hone) hmfit hn (fun j hj => by rw [hm₁]; exact hmem j hj)
    hWlt hpv
  have hc₂ : y₂.regs rC = y.regs rC := (hr₂ rC (by decide)).trans (hr₁ rC (by decide))
  have ho₂ : y₂.regs rOne = 1 := (hr₂ rOne (by decide)).trans ((hr₁ rOne (by decide)).trans hone)
  have hinc : ∃ z, ExecWithin w (ram[ rC ← rC + rOne ]) y₂ z 1 ∧ z.mem = y₂.mem ∧
      (∀ i : Fin 14, i.val < 5 → z.regs i = y₂.regs i) ∧ z.regs rC = y₂.regs rC + 1 := by
    have hc' : Fits w (y₂.regs rC + 1) := by rw [hc₂]; exact hc
    refine WP.exists_execWithin ?_
    wram_exec [ho₂, hc']
    exact ⟨rfl, fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | wram_simp,
      by wram_simp⟩
  obtain ⟨z, he₃, hm₃, hr₃, hc₃⟩ := hinc
  refine ⟨z, (he₁.seq (he₂.seq he₃)).mono (by omega),
    fun i hi => (hr₃ i hi).trans ((hr₂ i (by omega)).trans (hr₁ i (by omega))),
    by rw [hc₃, hc₂], fun j hj => ?_⟩
  rw [hm₃, hm₂ j hj, getD_colStep hj, hp₁, (hr₁ rC (by decide))]

/-- All `n` elimination columns. -/
private def eliminate : Code .standard 14 := .loop (.lt rC rN) colBody

/-- Check that no row has right-hand-side bit `n` set. -/
private def checkBody : Code .standard 14 := ram[
  rA ← rBase + rK; rX ← *rA; rB ← rX >>> rN; rB ← rB &&& rOne;
  if rB = rOne then [ rOk ← rZero ] else [ rT ← rT ];
  rK ← rK + rOne ]

private theorem exec_checkBody {w : ℕ} (y : Data 14) (v : ℕ)
    (hone : y.regs rOne = 1) (hzero : y.regs rZero = 0)
    (ha : Fits w (y.regs rBase + y.regs rK)) (hk : Fits w (y.regs rK + 1))
    (hv : y.mem (y.regs rBase + y.regs rK) = v) (hvf : Fits w v) (h1 : Fits w 1) :
    ∃ z, ExecWithin w checkBody y z 12 ∧ z.mem = y.mem ∧
      (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧
      z.regs rK = y.regs rK + 1 ∧
      z.regs rOk = (if v.testBit (y.regs rN) = true then 0 else y.regs rOk) := by
  have hb : Fits w (v.testBit (y.regs rN)).toNat := h1.of_le (Bool.toNat_le _)
  have hs : Fits w (v >>> y.regs rN) := hvf.of_le (Nat.shiftRight_le _ _)
  refine WP.exists_execWithin ?_
  wram_exec [checkBody, hone, hzero, ha, hk, hv, hvf, hb, hs, h1, Nat.shiftRight_and_one]
  all_goals
    refine ⟨by wram_simp, fun i hi => by
        fin_cases i <;> first | exact absurd hi (by decide) | wram_simp,
      by wram_simp, ?_⟩
    wram_simp
    simp_all

/-- The final check over all rows. -/
private def check : Code .standard 14 :=
  .seq (ram[ rOk ← #1; rK ← #0 ]) (.loop (.lt rK rM) checkBody)

private theorem exec_check {w : ℕ} (W : List ℕ) (y : Data 14)
    (hm : y.regs rM = W.length) (hbase : y.regs rBase = 3) (hone : y.regs rOne = 1)
    (hzero : y.regs rZero = 0) (hmfit : Fits w (W.length + 3))
    (hmem : ∀ j < W.length, y.mem (3 + j) = W.getD j 0)
    (hWfit : ∀ x ∈ W, Fits w x) :
    ∃ z, ExecWithin w check y z (14 * W.length + 4) ∧
      z.regs rOk = (W.all fun x => !x.testBit (y.regs rN)).toNat := by
  have h1 : Fits w 1 := hmfit.of_le (by omega)
  set n := y.regs rN with hn
  let P (k : ℕ) (z : Data 14) : Prop :=
    (∀ i : Fin 14, i.val < 6 → z.regs i = y.regs i) ∧ z.mem = y.mem ∧
      z.regs rOk = ((W.take k).all fun x => !x.testBit n).toNat
  have hbody (z : Data 14) (hz : P (z.regs rK) z) (hlt : z.regs rK < W.length) :
      ∃ z', ExecWithin w checkBody z z' 12 ∧ P (z.regs rK + 1) z' ∧
        z'.regs rK = z.regs rK + 1 := by
    obtain ⟨hr, hzm, hok⟩ := hz
    have hzb : z.regs rBase = 3 := (hr rBase (by decide)).trans hbase
    have hzn : z.regs rN = n := hr rN (by decide)
    obtain ⟨z', he, hm', hr', hk', hok'⟩ := exec_checkBody z (W.getD (z.regs rK) 0)
      ((hr rOne (by decide)).trans hone) ((hr rZero (by decide)).trans hzero)
      (hmfit.of_le (by rw [hzb]; omega)) (hmfit.of_le (by omega))
      (by rw [hzm, hzb]; exact hmem _ hlt) (hWfit _ (getD_mem hlt)) h1
    refine ⟨z', he, ⟨fun i hi => (hr' i hi).trans (hr i hi), hm'.trans hzm, ?_⟩, hk'⟩
    rw [hok', hzn, hok, take_succ_eq hlt, List.all_append]
    generalize W.getD (z.regs rK) 0 = v
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    generalize (W.take (z.regs rK)).all (fun x => !x.testBit n) = t
    cases v.testBit n <;> cases t <;> simp
  refine WP.exists_execWithin ?_
  wram_exec [check]
  wram_call (ExecWithin.loop_count P (fun z hz => ((hz.1 rM (by decide)).trans hm)) hbody
    (by wram_simp; omega)
    ⟨fun i hi => by fin_cases i <;> first | exact absurd hi (by decide) | wram_simp,
      by wram_simp, by wram_simp; simp⟩)
    with z ⟨⟨_, _, hok⟩, _⟩
  exact ⟨by wram_simp; omega, by rw [hok, List.take_length]⟩

/-- Read `n` and `m` from the input header and set the constants. -/
private def setup : Code .standard 14 := ram[
  rT ← #1; rN ← *rT; rT ← #2; rM ← *rT; rBase ← #3; rOne ← #1; rZero ← #0; rC ← #0 ]

/-- The whole computation: setup, all elimination columns, the final check. -/
private def code : Code .standard 14 := .seq setup (.seq eliminate check)

/-- The fixed standard-basis program; its answer is register `rOk`. -/
def program : Program .standard 14 := code.program rOk

end Program

/-! ## Instances, encoding and the running-time theorem -/

open Cslib.WordRAM

/-- A dense XOR-SAT instance whose rows all have the declared width. -/
abbrev Instance := {q : Input // Width q.width q.rows}

/-- Word-RAM input layout `[n, m] ++ packed rows`. -/
@[expose]
def encode (q : Instance) : List ℕ := q.1.width :: q.1.rows.length :: q.1.rows.map rowWord

/-- Admitted widths: a packed row (`n + 1` bits) fits in one word, and so do the row addresses
`3, …, m + 2`. This is the word-width condition of the bit-packed representation. -/
@[expose]
def FitsWidth (q : Instance) (w : ℕ) : Prop :=
  q.1.width + 1 ≤ w ∧ Fits w (q.1.rows.length + 3)

private theorem length_cols (W : List ℕ) : ∀ c, (cols W c).length = W.length
  | 0 => rfl
  | c + 1 => by simp [cols, colStep, length_cols W c]

private theorem two_pow_le {n w : ℕ} (h : n + 1 ≤ w) : 2 ^ (n + 1) ≤ 2 ^ w :=
  Nat.pow_le_pow_right (by decide) h

private theorem exec_code {w : ℕ} (q : Instance) (hw : FitsWidth q w) :
    ∃ y, ExecWithin w code (.init (encode q)) y
        (8 + (q.1.width * (28 * q.1.rows.length + 11) + 2) + (14 * q.1.rows.length + 4)) ∧
      y.regs rOk = (decide q.1).toNat := by
  obtain ⟨hn1, hm3⟩ := hw
  set n := q.1.width with hndef
  set m := q.1.rows.length with hmdef
  set W := q.1.rows.map rowWord with hWdef
  have hF : List.Forall₂ (RowRel n 0) W q.1.rows := forall₂_rowWord q.2
  have hWlen : W.length = m := by simp [hWdef, hmdef]
  have hpow := two_pow_le hn1
  have hnfit : Fits w (2 ^ (n + 1) - 1) := by
    change 2 ^ (n + 1) - 1 < 2 ^ w
    have := Nat.two_pow_pos (n + 1); omega
  have hnn : Fits w n := hnfit.of_le (by have := Nat.lt_two_pow_self (n := n + 1); omega)
  have h1 : Fits w 1 := hm3.of_le (by omega)
  have h2 : Fits w 2 := hm3.of_le (by omega)
  have h3 : Fits w 3 := hm3.of_le (by omega)
  have hmm : Fits w m := hm3.of_le (by omega)
  have hi1 : (Data.init (encode q) : Data 14).mem 1 = n := by simp [encode, hndef]
  have hi2 : (Data.init (encode q) : Data 14).mem 2 = m := by simp [encode, hmdef]
  have hirow : ∀ j < m, (Data.init (encode q) : Data 14).mem (3 + j) = W.getD j 0 := by
    intro j _
    rw [show 3 + j = (j + 2) + 1 by omega, Data.init_mem_succ]
    simp [encode, hWdef]
  -- setup
  have hsetup : ∃ y₀, ExecWithin w setup (.init (encode q)) y₀ 8 ∧
      y₀.mem = (Data.init (encode q) : Data 14).mem ∧ y₀.regs rN = n ∧ y₀.regs rM = m ∧
      y₀.regs rBase = 3 ∧ y₀.regs rOne = 1 ∧ y₀.regs rZero = 0 ∧ y₀.regs rC = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [setup, hi1, hi2, h1, h2, h3, hnn, hmm]
    exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp⟩
  obtain ⟨y₀, he₀, hm₀, hN₀, hM₀, hB₀, hO₀, hZ₀, hC₀⟩ := hsetup
  -- all columns
  let P (c : ℕ) (y : Data 14) : Prop :=
    (∀ i : Fin 14, i.val < 5 → y.regs i = y₀.regs i) ∧
      ∀ j < m, y.mem (3 + j) = (cols W c).getD j 0
  have hrel (c : ℕ) (hc : c ≤ n) : ∀ x ∈ cols W c, x < 2 ^ (n + 1) := fun x hx => by
    obtain ⟨_, _, hr⟩ := (forall₂_cols hF c hc).exists_mem_of_mem hx
    exact hr.lt
  have hbody (y : Data 14) (hy : P (y.regs rC) y) (hlt : y.regs rC < n) :
      ∃ z, ExecWithin w colBody y z (28 * m + 9) ∧ P (y.regs rC + 1) z ∧
        z.regs rC = y.regs rC + 1 := by
    obtain ⟨hr, hmem⟩ := hy
    have hlen : (cols W (y.regs rC)).length = m := by rw [length_cols, hWlen]
    obtain ⟨z, he, hr', hc', hmem'⟩ := exec_colBody (n := n) (cols W (y.regs rC)) y
      (by rw [hlen, hr rM (by decide), hM₀]) ((hr rBase (by decide)).trans hB₀)
      ((hr rOne (by decide)).trans hO₀) ((hr rZero (by decide)).trans hZ₀)
      (by rw [hlen]; exact hm3) hnfit (hnn.of_le (by omega))
      (fun j hj => hmem j (by rw [hlen] at hj; exact hj)) (hrel _ (by omega))
    refine ⟨z, by rw [hlen] at he; exact he,
      ⟨fun i hi => (hr' i hi).trans (hr i hi), fun j hj => ?_⟩, hc'⟩
    rw [hmem' j (by rw [hlen]; exact hj)]
    rfl
  obtain ⟨y₁, he₁, ⟨hr₁, hmem₁⟩, _⟩ := ExecWithin.loop_count (body := colBody)
    (index := rC) (limit := rN) P (fun y hy => (hy.1 rN (by decide)).trans hN₀) hbody
    (by rw [hC₀]; omega) ⟨fun _ _ => rfl, fun j hj => by rw [hC₀, hm₀]; exact hirow j hj⟩
  -- final check
  have hlenn : (cols W n).length = m := by rw [length_cols, hWlen]
  obtain ⟨y₂, he₂, hok⟩ := exec_check (cols W n) y₁
    (by rw [hlenn, hr₁ rM (by decide), hM₀]) ((hr₁ rBase (by decide)).trans hB₀)
    ((hr₁ rOne (by decide)).trans hO₀) ((hr₁ rZero (by decide)).trans hZ₀)
    (by rw [hlenn]; exact hm3) (fun j hj => hmem₁ j (by rw [hlenn] at hj; exact hj))
    (fun x hx => hnfit.of_le (by have := hrel n le_rfl x hx; omega))
  refine ⟨y₂, ?_, ?_⟩
  · rw [hlenn] at he₂
    rw [hC₀, show 28 * m + 9 + 2 = 28 * m + 11 by omega] at he₁
    exact (he₀.seq (he₁.seq he₂)).mono (by simp only [Nat.sub_zero]; omega)
  · rw [hok, hr₁ rN (by decide), hN₀, decide_eq_cols q.1 q.2]

/-- **Word-RAM running time of dense Gaussian elimination over `𝔽₂` (one row per word).**
The fixed standard-basis program `program` computes `(XORSAT.Dense.decide q).toNat` on every
well-formed `m × n` instance, laid out as `[n, m]` and one packed word per row, in at most
`30 (m + 1) (n + 1)` word instructions, at every word width `w ≥ n + 1` at which the row
addresses fit (`FitsWidth`). On this domain the row-width check of `decide` is constantly
`true`. -/
theorem computesInTime_decide :
    program.ComputesInTime (fun _ => encode)
      (fun q _ => 30 * (q.1.rows.length + 1) * (q.1.width + 1)) FitsWidth
      (fun q => (decide q.1).toNat) := by
  refine (code.computesInTime_program rOk
    (time := fun q _ =>
      8 + (q.1.width * (28 * q.1.rows.length + 11) + 2) + (14 * q.1.rows.length + 4))
    ?_).mono ?_ (fun _ _ h => h)
  · intro q w hw _
    exact exec_code q hw
  · intro q _
    nlinarith

/-- **Word-RAM decision of dense XOR-SAT.** `program` decides satisfiability of every
well-formed `m × n` dense system in at most `30 (m + 1) (n + 1)` word instructions at admitted
widths, which have `w ≥ n + 1` (one packed row per word). -/
theorem decidesInTime_decide :
    program.DecidesInTime (fun _ => encode) {q : Instance | Satisfiable q.1.width q.1.rows}
      (fun q _ => 30 * (q.1.rows.length + 1) * (q.1.width + 1)) FitsWidth := by
  intro q w hw hin
  obtain ⟨k, hexec, hle⟩ := computesInTime_decide q w hw hin
  refine ⟨(decide q.1).toNat, k, hexec, hle, Bool.toNat_le _, ?_⟩
  have hiff := decide_eq_true_iff q.1
  rw [Set.mem_ofPred_eq]
  cases hd : decide q.1
  · simp only [Bool.toNat_false, zero_ne_one, false_iff]
    exact fun hs => absurd (hiff.mpr ⟨q.2, hs⟩) (by simp [hd])
  · simp only [Bool.toNat_true, true_iff]
    exact (hiff.mp hd).2

/-- On well-formed instances, the decided set is upstream's satisfiable dense systems. -/
theorem mem_satisfiable_iff (q : Instance) :
    q ∈ {q : Instance | Satisfiable q.1.width q.1.rows} ↔
      q.1 ∈ {q : Input | Width q.width q.rows ∧ Satisfiable q.width q.rows} :=
  ⟨fun h => ⟨q.2, h⟩, fun h => h.2⟩

/-- Every well-formed instance has an admitted width at which its encoding fits. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro q
  have hm := Nat.lt_two_pow_self (n := q.1.rows.length + 3)
  have hmw := Nat.pow_le_pow_right (n := 2) (by decide)
    (show q.1.rows.length + 3 ≤ q.1.width + q.1.rows.length + 4 by omega)
  have hnw := Nat.pow_le_pow_right (n := 2) (by decide)
    (show q.1.width + 1 ≤ q.1.width + q.1.rows.length + 4 by omega)
  have hn := Nat.lt_two_pow_self (n := q.1.width + 1)
  refine ⟨q.1.width + q.1.rows.length + 4, ⟨by omega, ?_⟩, ?_, ?_⟩
  · change q.1.rows.length + 3 < 2 ^ (q.1.width + q.1.rows.length + 4)
    omega
  · change (encode q).length < 2 ^ (q.1.width + q.1.rows.length + 4)
    simp only [encode, List.length_cons, List.length_map]
    omega
  · intro v hv
    change v < 2 ^ (q.1.width + q.1.rows.length + 4)
    simp only [encode, List.mem_cons, List.mem_map] at hv
    rcases hv with hv | hv | ⟨e, he, hv⟩
    · omega
    · omega
    · have := (rowRel_rowWord (q.2 e he)).lt
      omega

/-- **Uniform Word-RAM decidability of dense XOR-SAT** by Gaussian elimination with one packed
row per word, in at most `30 (m + 1) (n + 1)` standard-basis word instructions at word widths
`w ≥ n + 1`, bundling width admissibility (`inputAdmissible`). -/
theorem uniformDecidableInTime_decide :
    UniformDecidableInTime .standard {q : Instance | Satisfiable q.1.width q.1.rows}
      (fun _ => encode) (fun q _ => 30 * (q.1.rows.length + 1) * (q.1.width + 1)) FitsWidth :=
  ⟨14, program, decidesInTime_decide, inputAdmissible⟩

end Cslib.Algorithms.WordRAM.XORSATDense
