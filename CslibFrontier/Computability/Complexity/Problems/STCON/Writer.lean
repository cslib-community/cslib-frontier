/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.Header

/-!
# Writing connectivity instances from connectivity instances in logarithmic space

Many logarithmic-space maps from directed `s`–`t` connectivity instances to such instances build
a matrix whose entries are either entries of the input matrix or arithmetic in the header values
and in the row and column. The counter program `Cslib.Complexity.STCONInstance.stconWriter`
writes such an instance. It takes eight expressions over the registers `[n, s, t, r, c]`: the
number of vertices, the source and the target of the output, and, for the entry `(r, c)`, two
guarded input bits and an arithmetic test. The entry is set when a guard is positive and the input
bit at its position is set, or when the test is positive. It reads the header of the input
(`Cslib.Complexity.STCONInstance.headerCode`), writes the unary header of the output, and writes
the matrix entry by entry. When the number of vertices is polynomial in the input length, the
registers hold logarithmically many bits, and the map is computed in logarithmic space
(`Cslib.Complexity.STCONInstance.computableInLogSpace_of_entryExprs`).

## Main definitions

* `Cslib.Complexity.STCONInstance.stconWriter`: the counter program.

## Main results

* `Cslib.Complexity.STCONInstance.computableInLogSpace_of_entryExprs`: an instance whose header
  and entries the expressions describe is computed in logarithmic space.
-/

public section

namespace Cslib.Complexity

namespace STCONInstance

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- **The writer** of a connectivity instance on an encoded connectivity instance. The expressions
are evaluated on the registers `[n, s, t, r, c]`. `numV`, `src` and `tgt` give the number of
vertices, the source and the target of the output. The entry `(r, c)` is set when `guard₁` is
positive and the input bit at `pos₁` is set, or `guard₂` is positive and the input bit at `pos₂` is
set, or `test` is positive. Labels `0` to `5` read the header into the registers `0`, `1` and `2`;
the loops at labels `6`, `11` and `16` write the unary header; the nested loops at labels `21` and
`24` write the matrix, the entry at labels `27` to `33`; label `34` halts. -/
@[expose] def stconWriter (numV src tgt guard₁ pos₁ guard₂ pos₂ test : Expr) : CounterProgram where
  code := List.flatten [
    headerCode 0,
    forCode 6 3 numV 9 10, [emit true 8, emit false 11],
    forCode 11 3 src 14 15, [emit true 13, emit false 16],
    forCode 16 3 tgt 19 20, [emit true 18, emit false 21],
    forCode 21 3 numV 24 34, forCode 24 4 numV 27 23,
    [lt (const 0) guard₁ 28 29,
     read pos₁ 32 29 29,
     lt (const 0) guard₂ 30 31,
     read pos₂ 32 31 31,
     lt (const 0) test 32 33,
     emit true 26,
     emit false 26,
     halt []]]
  registers := 5

/-- The entry `(r, c)` that `stconWriter` writes on the input `I`. -/
@[expose] def entryOf (guard₁ pos₁ guard₂ pos₂ test : Expr) (I : STCONInstance) (r c : ℕ) :
    Bool :=
  (decide (0 < guard₁.eval [I.n, I.s, I.t, r, c]) &&
      I.encode[pos₁.eval [I.n, I.s, I.t, r, c]]?.getD false) ||
    (decide (0 < guard₂.eval [I.n, I.s, I.t, r, c]) &&
      I.encode[pos₂.eval [I.n, I.s, I.t, r, c]]?.getD false) ||
    decide (0 < test.eval [I.n, I.s, I.t, r, c])

variable {numV src tgt guard₁ pos₁ guard₂ pos₂ test : Expr} (I : STCONInstance) {B : ℕ}

local notation "W" => stconWriter numV src tgt guard₁ pos₁ guard₂ pos₂ test

/-- Writing the entry `(r, c)` of the matrix. -/
private theorem reachesOut_entry {r c : ℕ} (hb : ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), r, c], z ≤ B) :
    (W).ReachesOut I.encode ((W).Active B) (27, [I.n, I.s, I.t, r, c])
      (26, [I.n, I.s, I.t, r, c]) [entryOf guard₁ pos₁ guard₂ pos₂ test I r c] := by
  set regs := [I.n, (I.s : ℕ), (I.t : ℕ), r, c]
  have htrue : (W).ReachesOut I.encode ((W).Active B) (32, regs) (26, regs) [true] :=
    ReachesOut.emit (show (W).instr 32 = _ from rfl) hb (ReachesOut.refl _)
  have hfalse : (W).ReachesOut I.encode ((W).Active B) (33, regs) (26, regs) [false] :=
    ReachesOut.emit (show (W).instr 33 = _ from rfl) hb (ReachesOut.refl _)
  -- the arithmetic test, at label `31`
  have h31 : (W).ReachesOut I.encode ((W).Active B) (31, regs) (26, regs)
      [decide (0 < test.eval regs)] := by
    refine ReachesOut.lt (show (W).instr 31 = _ from rfl) hb ?_
    rw [eval_const]
    by_cases ht : 0 < test.eval regs
    · simpa [ht] using htrue
    · simpa [ht] using hfalse
  -- a guarded bit test at `l₁` / `l₁ + 1` short-circuits to `32` (`true`) or falls through to `l₂`
  have hguard {l₁ l₂ : ℕ} {guard pos : Expr} {fall : Bool}
      (hlt : (W).instr l₁ = lt (const 0) guard (l₁ + 1) l₂)
      (hread : (W).instr (l₁ + 1) = read pos 32 l₂ l₂)
      (hfall : (W).ReachesOut I.encode ((W).Active B) (l₂, regs) (26, regs) [fall]) :
      (W).ReachesOut I.encode ((W).Active B) (l₁, regs) (26, regs)
        [(decide (0 < guard.eval regs) && I.encode[pos.eval regs]?.getD false) || fall] := by
    refine ReachesOut.lt hlt hb ?_
    rw [eval_const]
    by_cases hg : 0 < guard.eval regs
    · rw [ite_eq_left hg]
      refine ReachesOut.read hread hb ?_
      rcases I.encode[pos.eval regs]? with _ | _ | _
      · simpa [hg, readLabel] using hfall
      · simpa [hg, readLabel] using hfall
      · simpa [hg, readLabel] using htrue
    · simpa [hg] using hfall
  have h29 := hguard (guard := guard₂) (pos := pos₂) (l₁ := 29) (l₂ := 31) rfl rfl h31
  rw [entryOf, Bool.or_assoc]
  exact hguard (guard := guard₁) (pos := pos₁) (l₁ := 27) (l₂ := 29) rfl rfl h29

/-- **The matrix row by row**, by the nested loops at labels `21` and `24`. -/
private theorem reachesOut_rows {N : ℕ}
    (hN : ∀ r c, numV.eval [I.n, I.s, I.t, r, c] = N) (hnB : I.n ≤ B) (hB : N ≤ B)
    {i₀ : ℕ} (hi₀ : i₀ ≤ B) :
    ∃ regs, (W).ReachesOut I.encode ((W).Active B) (21, [I.n, I.s, I.t, i₀, 0]) (34, regs)
      ((List.range N).flatMap fun r =>
        (List.range N).map (entryOf guard₁ pos₁ guard₂ pos₂ test I r)) ∧
      ∀ x ∈ regs, x ≤ B := by
  have hreg : ∀ {r c : ℕ}, r ≤ B → c ≤ B → ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), r, c], z ≤ B :=
    fun hr hc => I.regs_le hnB hr hc
  have hcode₁ : (W).CodeAt 21 (forCode 21 3 numV 24 34) := codeAt_of_prefix ⟨_, rfl⟩
  have hcode₂ : (W).CodeAt 24 (forCode 24 4 numV 27 23) := codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs, hreach, x, rfl, -, hx⟩ := reachesOut_forCode (w := I.encode)
    (N := N) (o := fun r => (List.range N).map (entryOf guard₁ pos₁ guard₂ pos₂ test I r))
    hcode₁ (fun r regs => ∃ x, regs = [I.n, I.s, I.t, r, x] ∧ r ≤ N ∧ x ≤ N) hB
    (by
      rintro r regs ⟨x, rfl, hr, hx⟩
      exact ⟨rfl, hN r x, by simp, hreg (hr.trans hB) (hx.trans hB)⟩)
    (by
      rintro r hr regs ⟨x, rfl, -, hx⟩
      obtain ⟨regs', hreach, rfl, -⟩ := reachesOut_forCode (w := I.encode)
        (N := N) (o := fun c => [entryOf guard₁ pos₁ guard₂ pos₂ test I r c]) hcode₂
        (fun c regs => regs = [I.n, I.s, I.t, r, c] ∧ c ≤ N) hB
        (by
          rintro c regs ⟨rfl, hc⟩
          exact ⟨rfl, hN r c, by simp, hreg (hr.le.trans hB) (hc.trans hB)⟩)
        (by
          rintro c hc regs ⟨rfl, -⟩
          have hb := hreg (hr.le.trans hB) (hc.le.trans hB)
          exact ⟨_, reachesOut_entry I hb, rfl, hb, by simp, by omega⟩)
        [I.n, I.s, I.t, r, x] (hreg (hr.le.trans hB) (hx.trans hB)) ⟨by simp, by omega⟩
      refine ⟨_, ?_, rfl, hreg (hr.le.trans hB) hB, N, by simp, by omega, le_rfl⟩
      rwa [← List.map_eq_flatMap] at hreach)
    [I.n, I.s, I.t, i₀, 0] (hreg hi₀ (Nat.zero_le _)) ⟨0, by simp, by omega, by omega⟩
  exact ⟨_, hreach, hreg hB (hx.trans hB)⟩

/-- A loop at `b` whose body emits `true` writes the unary number `M`. -/
private theorem reachesOut_ones {b M : ℕ} {e : Expr} (hc : (W).CodeAt b (forCode b 3 e (b + 3)
    (b + 4))) (hemit : (W).instr (b + 3) = emit true (b + 2))
    (he : ∀ u, e.eval [I.n, I.s, I.t, u, 0] = M) (hnB : I.n ≤ B) (hM : M ≤ B) {i : ℕ}
    (hi : i ≤ B) :
    (W).ReachesOut I.encode ((W).Active B) (b, [I.n, I.s, I.t, i, 0])
      (b + 4, [I.n, I.s, I.t, M, 0]) (List.replicate M true) := by
  have hreg : ∀ {u : ℕ}, u ≤ B → ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, 0], z ≤ B :=
    fun hu => I.regs_le hnB hu (Nat.zero_le _)
  obtain ⟨_, hr, rfl, -⟩ := reachesOut_forCode (w := I.encode) (N := M)
    (o := fun _ => [true]) hc (fun u regs => regs = [I.n, I.s, I.t, u, 0] ∧ u ≤ M) hM
    (by
      rintro u regs ⟨rfl, hu⟩
      exact ⟨rfl, he u, by simp, hreg (hu.trans hM)⟩)
    (by
      rintro u hu regs ⟨rfl, -⟩
      exact ⟨_, ReachesOut.emit hemit (hreg (hu.le.trans hM)) (ReachesOut.refl _), rfl,
        hreg (hu.le.trans hM), by simp, by omega⟩)
    [I.n, I.s, I.t, i, 0] (hreg hi) ⟨by simp, by omega⟩
  simpa only [List.flatMap_def, List.map_const', List.length_range,
    List.flatten_replicate_singleton] using hr

/-- **Instances whose header and entries are given by expressions are computed in logarithmic
space.** Let `F` map connectivity instances to connectivity instances on at most `(m + 1) ^ k`
vertices for encoded inputs of length `m`, and let the expressions describe `F` over the registers
`[n, s, t, r, c]`: `numV`, `src` and `tgt` evaluate to the number of vertices, the source and the
target, and the entry `(r, c)` is `entryOf guard₁ pos₁ guard₂ pos₂ test`. Then `stconWriter`
computes `F` in logarithmic space. -/
theorem computableInLogSpace_of_entryExprs {F : STCONInstance → STCONInstance} (k : ℕ)
    (hN : ∀ I r c, numV.eval [I.n, I.s, I.t, r, c] = (F I).n)
    (hS : ∀ I r c, src.eval [I.n, I.s, I.t, r, c] = (F I).s)
    (hT : ∀ I r c, tgt.eval [I.n, I.s, I.t, r, c] = (F I).t)
    (hbound : ∀ I, (F I).n ≤ (I.encode.length + 1) ^ k)
    (hentry : ∀ I (r c : Fin (F I).n),
      (F I).adj r c = entryOf guard₁ pos₁ guard₂ pos₂ test I r c) :
    ComputableInLogSpace F encSTCON encSTCON := by
  refine (W).computableInLogSpace_of_reachesOut (k + 1) fun I => ?_
  simp only [encSTCON_apply]
  set B := (I.encode.length + 1) ^ (k + 1)
  have hlen := I.length_encode
  have hle : (I.encode.length + 1) ^ k ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hB : (F I).n ≤ B := (hbound I).trans hle
  have hsB : ((F I).s : ℕ) ≤ B := (F I).s.isLt.le.trans hB
  have htB : ((F I).t : ℕ) ≤ B := (F I).t.isLt.le.trans hB
  have hn : I.n ≤ B :=
    calc I.n ≤ I.encode.length + 1 := by omega
      _ = (I.encode.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hreg : ∀ {u : ℕ}, u ≤ B → ∀ z ∈ [I.n, (I.s : ℕ), (I.t : ℕ), u, 0], z ≤ B :=
    fun hu => I.regs_le hn hu (Nat.zero_le _)
  have hheader := I.reachesOut_headerCode (P := W) (b := 0) (codeAt_of_prefix ⟨_, rfl⟩) hn
    (rest := [0, 0]) (by simp)
  have hc₁ : (W).CodeAt 6 (forCode 6 3 numV 9 10) := codeAt_of_prefix ⟨_, rfl⟩
  have hc₂ : (W).CodeAt 11 (forCode 11 3 src 14 15) := codeAt_of_prefix ⟨_, rfl⟩
  have hc₃ : (W).CodeAt 16 (forCode 16 3 tgt 19 20) := codeAt_of_prefix ⟨_, rfl⟩
  have h₁ := reachesOut_ones I hc₁ rfl (fun u => hN I u 0) hn hB (i := 0) (Nat.zero_le _)
  have h₂ := reachesOut_ones I hc₂ rfl (fun u => hS I u 0) hn hsB hB
  have h₃ := reachesOut_ones I hc₃ rfl (fun u => hT I u 0) hn htB hsB
  obtain ⟨regs, hrows, hregs⟩ := reachesOut_rows I (hN I) hn hB (i₀ := (F I).t) htB
  have hchain := hheader.trans (h₁.trans
    (ReachesOut.emit (show (W).instr 10 = _ from rfl) (hreg hB) (h₂.trans
      (ReachesOut.emit (show (W).instr 15 = _ from rfl) (hreg hsB) (h₃.trans
        (ReachesOut.emit (show (W).instr 20 = _ from rfl) (hreg htB) hrows))))))
  refine ⟨(34, regs), _, [], hchain, rfl, ?_, hregs⟩
  rw [encode, matrix_eq_flatMap _ (entryOf guard₁ pos₁ guard₂ pos₂ test I)
    (hentry I)]
  simp

end STCONInstance

end Cslib.Complexity
