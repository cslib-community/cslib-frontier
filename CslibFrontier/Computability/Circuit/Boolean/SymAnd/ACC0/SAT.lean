/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.Compile
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.Problems.CircuitSAT
import Cslib.Computability.Circuit.Composition
import CslibFrontier.Computability.Circuit.Depth
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Foundations.Analysis.SpecialFunctions.NthRoot
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Williams's faster-than-brute-force algorithm for `ACC⁰-SAT`

This module formalizes Williams's algorithmic `ACC⁰-SAT` theorem ([Williams2014], Theorem 4.1,
Section 4.2, p. 17 in the author's full version of 31 July 2012): for every constant depth bound
`d` and modulus `m > 0`, there exist constants `0 < ε < δ < 1` and `c₀ > 0` such that
satisfiability of single-output `ACC⁰[m]` circuits (`Unbounded.extSignature` with `MOD_m` gates)
of depth at most `d` and encoding length at most `2 ^ (n ^ ε)` on `n` inputs is decided by a native
multi-tape Turing machine in time `O(2 ^ (n - c₀ * n ^ δ))` (`exists_acc0SAT_decider`).

## Proof outline

Following [Williams2014], Section 4.2:

1. **Partial-assignment OR-expansion (`orExpand`)**: given a circuit `C` on `n` inputs and a
   parameter `ℓ`, enumerate all `2 ^ k` assignments (`k = min ℓ n`) to the last `k` inputs of `C`
   and feed them into `2 ^ k` copies of `C`, combined by a single top-level unbounded fan-in OR
   gate. This reduces the number of free inputs from `n` to `n - k`, multiplies the gate count by
   `2 ^ k` (plus 3 gates: two nullary constant gates `false`/`true` and the top OR gate), increases
   depth by at most `2` (one layer for nullary constants in `Unbounded.extSignature`, one for the
   top OR gate; in [Williams2014] hardwired constants add depth `1`, which is absorbed into the
   existential exponents `ε, δ`), and preserves satisfiability
   (`orExpand_mem_SignatureCircuitSAT_iff`).
2. **Algorithmic `ACC⁰ → SYM ∘ AND` compilation (`compileSymAndFixed`)**: apply Williams's
   Lemma 4.1 (`computableInO_compileSymAndFixed`) at depth `d + 2` and modulus `m` to obtain an
   equivalent `SYM ∘ AND` instance `(x, p)` on `n - k` inputs in quasi-polynomial time.
3. **Multi-tape Yates evaluation (`symAndSAT`)**: evaluate the satisfied-AND counts across all
   `2 ^ (n - k)` inputs in time `O((2 ^ (n - k) + |enc x| ^ c) * (n + 1) ^ c)` via
   `SymAnd.computableInO_countList` ([Williams2014], Lemma 4.2), then stream-evaluate the symmetric
   output gate `p.eval` over the count list via `streamFold_pair_list` with per-element cost
   polynomial in `|enc p| + x.gates.length.size` (which is polynomial in `n`, avoiding any
   quasipolynomial blowup multiplying `2 ^ (n - k)`).

## Encoding convention

In `Unbounded.encExtCircuit 1`, the encoding length `|enc c|` bounds input count, gate count, and
total wire count (matching the circuit description size `s = |C|` in [Williams2014], Theorem 4.1).
We also provide a `Cslib.Complexity.DecidableInTimeO` language corollary
(`decidableInTimeO_ACC0SAT`) for the exact polynomial-time-guarded language `ACC0SAT d m q`, which
contains all satisfiable circuits of depth at most `d` and encoding length at most
`2 ^ (n ^ (1 / q))`.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.orExpand`: OR-expansion of the last `min ℓ n` inputs of a circuit.
* `Cslib.Circuits.Boolean.SymAnd.symAndSAT`: satisfiability of a `(SymAndInstance, SymOutParam)`
  pair.
* `Cslib.Circuits.Boolean.SymAnd.ACC0SAT`: bounded-depth, bounded-size `ACC⁰[m]` satisfiability.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.orExpand_mem_SignatureCircuitSAT_iff`: `orExpand` preserves
  satisfiability.
* `Cslib.Circuits.Boolean.SymAnd.depth_orExpand_le`: `orExpand` increases depth by at most `2`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_orExpand`: multi-tape TM complexity of `orExpand`.
* `Cslib.Circuits.Boolean.SymAnd.symAndSAT_eq_true_iff`: correctness of `symAndSAT`.
* `Cslib.Circuits.Boolean.SymAnd.computableInO_symAndSAT`: multi-tape TM complexity of `symAndSAT`.
* `Cslib.Circuits.Boolean.SymAnd.exists_acc0SAT_decider`: Williams's Theorem 4.1 (promise form).
* `Cslib.Circuits.Boolean.SymAnd.decidableInTimeO_ACC0SAT`: `DecidableInTimeO` language corollary.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity

/-! ### 1. Partial-assignment OR-expansion (`orExpand`) -/

/-- Gate count of `constProg` followed by `N` copies of a size-`s` program. -/
private abbrev copySize (s : ℕ) : ℕ → ℕ
  | 0 => 2
  | N + 1 => copySize s N + s

private theorem copySize_eq (s N : ℕ) : copySize s N = 2 + N * s := by
  induction N with
  | zero => simp [copySize]
  | succ N ih => simp only [copySize, ih, Nat.succ_mul]; omega

/-- A 2-gate program computing the constants `false` (gate 0) and `true` (gate 1). -/
private def constProg (n' : ℕ) : Program Unbounded.extSignature n' 2 :=
  Program.gate
    (Program.gate Program.empty ⟨Unbounded.ExtOp.ac (.or 0), Fin.elim0⟩)
    ⟨Unbounded.ExtOp.ac (.and 0), Fin.elim0⟩

private def constFalseWire (n' : ℕ) : Wire n' 2 := Wire.gate ⟨0, by decide⟩

private def constTrueWire (n' : ℕ) : Wire n' 2 := Wire.gate ⟨1, by decide⟩

private theorem constProg_trace_false {g : ∀ k, BitString k → Bool} {n' : ℕ}
    (x : BitString n') :
    (constProg n').trace (Unbounded.extInterpretation g) x (constFalseWire n') = false :=
  rfl

private theorem constProg_trace_true {g : ∀ k, BitString k → Bool} {n' : ℕ}
    (x : BitString n') :
    (constProg n').trace (Unbounded.extInterpretation g) x (constTrueWire n') = true :=
  rfl

private theorem constProg_wireDepths_le (n' : ℕ) (w : Wire n' 2) :
    (constProg n').wireDepths w ≤ 1 := by
  cases w with
  | input i => simp [Program.wireDepths]
  | gate j => fin_cases j <;> exact le_of_eq rfl

private theorem constProg_code (n' : ℕ) :
    (constProg n').code = [(.ac (.or 0), []), (.ac (.and 0), [])] := by
  simp [constProg, Program.code_gate, Program.code_empty, Line.code]

/-- Lift a wire of `constProg n'` past `N` appended copies of a size-`s` program. -/
private def liftConstWire {n' s : ℕ} : (N : ℕ) → Wire n' 2 → Wire n' (copySize s N)
  | 0, w => w
  | N + 1, w => (liftConstWire N w).castAdd s

private theorem wire_castAdd_toNat {n g k : ℕ} (w : Wire n g) :
    (w.castAdd k).toNat = w.toNat := by
  cases w <;> rfl

private theorem liftConstWire_toNat {n' s : ℕ} (N : ℕ) (w : Wire n' 2) :
    (liftConstWire (s := s) N w).toNat = w.toNat := by
  induction N with
  | zero => rfl
  | succ N ih => rw [liftConstWire, wire_castAdd_toNat, ih]

/-- Feed wire `i : Fin n` of copy `a` either from free input `i` (when `i < n'`) or from the
constant wire encoding bit `i - n'` of `a`. -/
private def feedWire (n' n s N : ℕ) (a : ℕ) (i : Fin n) : Wire n' (copySize s N) :=
  if hi : i.1 < n' then
    Wire.input ⟨i.1, hi⟩
  else if a.testBit (i.1 - n') then
    liftConstWire N (constTrueWire n')
  else
    liftConstWire N (constFalseWire n')

private theorem feedWire_toNat (n' n s N a : ℕ) (i : Fin n) :
    (feedWire n' n s N a i).toNat =
      if i.1 < n' then i.1 else if a.testBit (i.1 - n') then n' + 1 else n' := by
  unfold feedWire
  split_ifs with h1 h2
  · rfl
  · rw [liftConstWire_toNat]; rfl
  · rw [liftConstWire_toNat]; rfl

/-- Raw wire renumbering induced by appending copy `a` of a size-`s`, `n`-input program after
`constProg n'` and `a` prior copies. -/
private def orExpandWire (n' n s a wire : ℕ) : ℕ :=
  if wire < n' then wire
  else if wire < n then (if a.testBit (min (wire - n') n) then n' + 1 else n')
  else n' + (2 + a * s) + (wire - n)

private theorem appendWireCode_feedWire {n' n : ℕ} (hn' : n' ≤ n) (s a wire : ℕ) :
    Program.appendWireCode n' n (copySize s a) (feedWire n' n s a a) wire =
      orExpandWire n' n s a wire := by
  unfold Program.appendWireCode orExpandWire
  by_cases h1 : wire < n
  · simp only [h1, ↓reduceDIte, feedWire_toNat]
    by_cases h2 : wire < n'
    · simp only [h2, ↓reduceIte]
    · have hmin : min (wire - n') n = wire - n' := Nat.min_eq_left (by omega)
      simp only [h2, ↓reduceIte, hmin]
  · have h2 : ¬ wire < n' := by omega
    simp only [h1, h2, ↓reduceDIte, ↓reduceIte, copySize_eq]

/-- Append `N` copies of `P` onto `constProg n'`, feeding copy `a` with `feedWire ... a`. -/
private def appendCopies (n' n s : ℕ) (P : Program Unbounded.extSignature n s) :
    (N : ℕ) → Program Unbounded.extSignature n' (copySize s N)
  | 0 => constProg n'
  | N + 1 => (appendCopies n' n s P N).append (feedWire n' n s N N) P

/-- The output wire of copy `a : Fin N` inside `appendCopies n' n s P N`. -/
private def copyOutWire (n' n s : ℕ) (out : Wire n s) :
    (N : ℕ) → Fin N → Wire n' (copySize s N)
  | 0 => Fin.elim0
  | N + 1 =>
    Fin.lastCases
      (Program.appendedWire (feedWire n' n s N N) out)
      (fun j => (copyOutWire n' n s out N j).castAdd s)

/-- Assignment to `Fin n` taking free bits from `x : BitString n'` and fixed bits from `a : ℕ`. -/
private def assignOfNat (n' n : ℕ) (x : BitString n') (a : ℕ) : BitString n :=
  fun i => if hi : i.1 < n' then x ⟨i.1, hi⟩ else a.testBit (i.1 - n')

private theorem appendCopies_trace_liftConst {U : Type*}
    (I : Interpretation Unbounded.extSignature U)
    (n' n s : ℕ) (P : Program Unbounded.extSignature n s) (x : Fin n' → U)
    (N : ℕ) (w : Wire n' 2) :
    (appendCopies n' n s P N).trace I x (liftConstWire N w) = (constProg n').trace I x w := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [appendCopies, liftConstWire, Program.trace_append_castAdd, ih]

private theorem appendCopies_trace_feedWire {g : ∀ k, BitString k → Bool}
    (n' n s : ℕ) (P : Program Unbounded.extSignature n s) (x : BitString n')
    (N a : ℕ) (i : Fin n) :
    (appendCopies n' n s P N).trace (Unbounded.extInterpretation g) x (feedWire n' n s N a i) =
      assignOfNat n' n x a i := by
  unfold feedWire assignOfNat
  split_ifs with h1 h2
  · rfl
  · rw [appendCopies_trace_liftConst, constProg_trace_true, h2]
  · rw [appendCopies_trace_liftConst, constProg_trace_false]
    cases hb : a.testBit (i.1 - n') <;> simp_all

private theorem appendCopies_trace_copyOutWire {g : ∀ k, BitString k → Bool}
    (n' n s : ℕ) (P : Program Unbounded.extSignature n s) (out : Wire n s)
    (x : BitString n') (N : ℕ) (a : Fin N) :
    (appendCopies n' n s P N).trace (Unbounded.extInterpretation g) x
        (copyOutWire n' n s out N a) =
      P.trace (Unbounded.extInterpretation g) (assignOfNat n' n x a.1) out := by
  induction N with
  | zero => exact a.elim0
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simp only [appendCopies, copyOutWire, Fin.lastCases_last, Fin.val_last]
      rw [Program.trace_append_appendedWire]
      congr 1
      funext i
      exact appendCopies_trace_feedWire n' n s P x N N i
    · simp only [appendCopies, copyOutWire, Fin.lastCases_castSucc, Fin.val_castSucc]
      rw [Program.trace_append_castAdd]
      exact ih j

private theorem program_wireDepths_eq_trace {σ : Signature} {n s : ℕ} (p : Program σ n s)
    (w : Wire n s) :
    p.wireDepths w = p.trace (depthInterpretation 1) (fun _ => 0) w := by
  rw [← p.wireDepthsWith_one]
  cases w <;> rfl

private theorem trace_depth_le_add {σ : Signature} {n s : ℕ} (q : Program σ n s)
    (d_in : Fin n → ℕ) (D : ℕ) (hd : ∀ i, d_in i ≤ D) (w : Wire n s) :
    q.trace (depthInterpretation 1) d_in w ≤ q.wireDepths w + D := by
  induction q with
  | empty =>
    cases w with
    | input i => simpa [Program.wireDepths] using hd i
    | gate j => exact j.elim0
  | gate q line ih =>
    cases w with
    | input i => simpa [Program.wireDepths] using hd i
    | gate j =>
      refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [Program.trace_gate_last, Program.wireDepths_gateWire, Program.depths_gate_last,
          ← Line.depthWith_one]
        exact depthInterpretation_le_add 1 line.op fun a => ih (line.wires a)
      · change (q.gate line).trace (depthInterpretation 1) d_in (Wire.gate k).castSucc ≤
            (q.gate line).wireDepths (Wire.gate k.castSucc) + D
        rw [Program.trace_gate_castSucc, Program.wireDepths_gateWire, Program.depths_gate_castSucc]
        exact ih (Wire.gate k)

private theorem appendCopies_wireDepths_copyOutWire (n' n s : ℕ)
    (P : Program Unbounded.extSignature n s) (out : Wire n s) (N : ℕ) (a : Fin N) :
    (appendCopies n' n s P N).wireDepths (copyOutWire n' n s out N a) ≤ P.wireDepths out + 1 := by
  induction N with
  | zero => exact a.elim0
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simp only [appendCopies, copyOutWire, Fin.lastCases_last]
      rw [program_wireDepths_eq_trace, Program.trace_append_appendedWire]
      refine trace_depth_le_add P _ 1 (fun i => ?_) out
      unfold feedWire
      split_ifs with h1 h2
      · simp
      · rw [appendCopies_trace_liftConst, ← program_wireDepths_eq_trace]
        exact constProg_wireDepths_le n' _
      · rw [appendCopies_trace_liftConst, ← program_wireDepths_eq_trace]
        exact constProg_wireDepths_le n' _
    · simp only [appendCopies, copyOutWire, Fin.lastCases_castSucc]
      rw [program_wireDepths_eq_trace, Program.trace_append_castAdd, ← program_wireDepths_eq_trace]
      exact ih j

private theorem appendCopies_code {n' n : ℕ} (hn' : n' ≤ n) (s : ℕ)
    (P : Program Unbounded.extSignature n s) (N : ℕ) :
    (appendCopies n' n s P N).code =
      [(.ac (.or 0), []), (.ac (.and 0), [])] ++
        ((List.range N).flatMap fun a =>
          P.code.map fun g => (g.1, g.2.map (orExpandWire n' n s a))) := by
  induction N with
  | zero =>
    simp only [appendCopies, List.range_zero, List.flatMap_nil, List.append_nil]
    exact constProg_code n'
  | succ N ih =>
    rw [appendCopies, Program.code_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc]
    congr 2
    refine List.map_congr_left fun g _ => ?_
    congr 1
    refine List.map_congr_left fun wire _ => ?_
    exact appendWireCode_feedWire hn' s N wire

private theorem copyOutWire_toNat {n' n : ℕ} (hn' : n' ≤ n) (s : ℕ) (out : Wire n s)
    (N : ℕ) (a : Fin N) :
    (copyOutWire n' n s out N a).toNat = orExpandWire n' n s a.1 out.toNat := by
  induction N with
  | zero => exact a.elim0
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simp only [copyOutWire, Fin.lastCases_last, Fin.val_last, Program.appendedWire_toNat]
      exact appendWireCode_feedWire hn' s N out.toNat
    · simp only [copyOutWire, Fin.lastCases_castSucc, Fin.val_castSucc, wire_castAdd_toNat]
      exact ih j

/-- **Partial-assignment OR-expansion** ([Williams2014], Section 4.2): fix the last `min ℓ c.1`
inputs of `c` in all `2 ^ min ℓ c.1` ways and combine the resulting `2 ^ min ℓ c.1` copies of `c`
with a single top-level unbounded fan-in OR gate. -/
def orExpand (ℓ : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    Σ n, Circuit Unbounded.extSignature n 1 :=
  let k := min ℓ c.1
  let n' := c.1 - k
  let N := 2 ^ k
  let prog := (appendCopies n' c.1 c.2.size c.2.program N).gate
    ⟨.ac (.or N), copyOutWire n' c.1 c.2.size (c.2.outputs 0) N⟩
  ⟨n', ⟨prog, fun _ => Wire.gate (Fin.last (copySize c.2.size N))⟩⟩

/-- `orExpand ℓ c` has `c.1 - min ℓ c.1` inputs. -/
theorem orExpand_n (ℓ : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (orExpand ℓ c).1 = c.1 - min ℓ c.1 := by rfl

/-- `orExpand ℓ c` has `2 ^ min ℓ c.1 * c.2.size + 3` gates. -/
theorem orExpand_size (ℓ : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (orExpand ℓ c).2.size = 2 ^ min ℓ c.1 * c.2.size + 3 := by
  simp only [orExpand, copySize_eq]
  omega

/-- `orExpand ℓ c` increases circuit depth by at most `2` (one layer for nullary constants, one for
the top-level OR gate). -/
theorem depth_orExpand_le (ℓ : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    (orExpand ℓ c).2.depth ≤ c.2.depth + 2 := by
  rw [← Circuit.depthWith_one, Circuit.depthWith_le_iff]
  intro j
  simp only [orExpand, Program.wireDepthsWith_one, Program.wireDepths_gateWire,
    Program.depths_gate_last, ← Line.depthWith_one, Line.depthWith_eq_sup, Pi.one_apply]
  have hsup : (Finset.univ.sup fun a : Fin (2 ^ min ℓ c.1) =>
      (appendCopies (c.1 - min ℓ c.1) c.1 c.2.size c.2.program (2 ^ min ℓ c.1)).wireDepths
        (copyOutWire (c.1 - min ℓ c.1) c.1 c.2.size (c.2.outputs 0) (2 ^ min ℓ c.1) a)) ≤
      c.2.depth + 1 :=
    Finset.sup_le fun a _ =>
      (appendCopies_wireDepths_copyOutWire (c.1 - min ℓ c.1) c.1 c.2.size c.2.program
          (c.2.outputs 0) (2 ^ min ℓ c.1) a).trans
        (Nat.add_le_add_right (c.2.outputDepths_le_depth 0) 1)
  exact Nat.add_le_add_right hsup 1

private theorem eval_orExpand {g : ∀ k, BitString k → Bool} (ℓ : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) (x : BitString (c.1 - min ℓ c.1)) :
    (orExpand ℓ c).2.eval (Unbounded.extInterpretation g) x 0 = true ↔
      ∃ a : Fin (2 ^ min ℓ c.1),
        c.2.eval (Unbounded.extInterpretation g)
          (assignOfNat (c.1 - min ℓ c.1) c.1 x a.1) 0 = true := by
  dsimp only [orExpand, Circuit.eval, Function.comp_apply]
  rw [Program.trace_gate_last]
  simp only [Unbounded.extInterpretation, Unbounded.interpretation_or, decide_eq_true_eq]
  constructor <;> rintro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
  · rwa [appendCopies_trace_copyOutWire] at ha
  · rwa [appendCopies_trace_copyOutWire]

/-- `orExpand ℓ c` preserves satisfiability under any extra-gate interpretation. -/
theorem orExpand_mem_SignatureCircuitSAT_iff {g : ∀ k, BitString k → Bool} (ℓ : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    orExpand ℓ c ∈ SignatureCircuitSAT (Unbounded.extInterpretation g) ↔
      c ∈ SignatureCircuitSAT (Unbounded.extInterpretation g) := by
  simp only [mem_SignatureCircuitSAT]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (eval_orExpand ℓ c x).1 hx
    exact ⟨assignOfNat (c.1 - min ℓ c.1) c.1 x a.1, ha⟩
  · rintro ⟨y, hy⟩
    set k := min ℓ c.1
    set n' := c.1 - k
    have hn : n' + k = c.1 := Nat.sub_add_cancel (Nat.min_le_right ℓ c.1)
    let x : BitString n' := fun i => y ⟨i.1, by omega⟩
    let yHi : BitString k := fun j => y ⟨n' + j.1, by omega⟩
    let a : Fin (2 ^ k) := BitString.equivFin k yHi
    refine ⟨x, (eval_orExpand ℓ c x).2 ⟨a, ?_⟩⟩
    have hass : assignOfNat n' c.1 x a.1 = y := by
      funext i
      unfold assignOfNat
      split_ifs with hi
      · rfl
      · have hj : i.1 - n' < k := by omega
        have hbit : a.1.testBit (i.1 - n') = yHi ⟨i.1 - n', hj⟩ := by
          have hsym := congrFun ((BitString.equivFin k).symm_apply_apply yHi) ⟨i.1 - n', hj⟩
          simpa only [a, BitString.equivFin_symm_apply] using hsym
        rw [hbit]
        dsimp only [yHi]
        congr 1
        simp only [Fin.ext_iff]
        omega
    rw [hass]
    exact hy

private def orExpandCodeFromRaw
    (p : (ℕ × (List (Unbounded.ExtOp × List ℕ) × List ℕ)) × (ℕ × ℕ)) :
    ℕ × (List (Unbounded.ExtOp × List ℕ) × List ℕ) :=
  let n := p.1.1
  let gatesRaw := p.1.2.1
  let s := gatesRaw.length
  let out0 := p.1.2.2.getD 0 0
  let k := p.2.1
  let N := p.2.2
  let n' := n - k
  let body := (List.range N).flatMap fun a =>
    gatesRaw.map fun g => (g.1, g.2.map (orExpandWire n' n s a))
  let orWires := (List.range N).map fun a => orExpandWire n' n s a out0
  let gates := [(.ac (.or 0), []), (.ac (.and 0), [])] ++ body ++ [(.ac (.or N), orWires)]
  (n', (gates, [n' + (2 + N * s)]))

private theorem orExpandCodeFromRaw_eq (ℓ : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    orExpandCodeFromRaw ((c.1, c.2.code), (min ℓ c.1, 2 ^ min ℓ c.1)) =
      ((orExpand ℓ c).1, (orExpand ℓ c).2.code) := by
  set k := min ℓ c.1
  set n' := c.1 - k
  set N := 2 ^ k
  have hn' : n' ≤ c.1 := Nat.sub_le c.1 k
  have hs : c.2.code.1.length = c.2.size := Circuit.length_code_fst c.2
  have hout0 : c.2.code.2.getD 0 0 = (c.2.outputs 0).toNat := by
    simp [Circuit.code]
  have hcode : (orExpand ℓ c).2.code =
      (([(.ac (.or 0), []), (.ac (.and 0), [])] ++
        ((List.range N).flatMap fun a =>
          c.2.code.1.map fun g => (g.1, g.2.map (orExpandWire n' c.1 c.2.size a)))) ++
        [(.ac (.or N), (List.range N).map fun a =>
          orExpandWire n' c.1 c.2.size a (c.2.outputs 0).toNat)],
       [n' + (2 + N * c.2.size)]) := by
    refine Prod.ext ?_ ?_
    · simp only [orExpand, Circuit.code, Program.code_gate, Line.code]
      have hbody := appendCopies_code hn' c.2.size c.2.program N
      dsimp only [k, n', N] at hbody ⊢
      rw [hbody]
      congr 2
      refine Prod.ext rfl ?_
      refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact copyOutWire_toNat hn' c.2.size (c.2.outputs 0) N ⟨i, by simpa using hi1⟩
    · simp only [orExpand, Circuit.code, List.ofFn_succ, List.ofFn_zero, Wire.toNat_gate,
        Fin.val_last, copySize_eq, k, n', N]
  rw [orExpandCodeFromRaw, hcode]
  simp only [hs, hout0, orExpand_n, k, n', N]

section OrExpandPolyTime

attribute [local irreducible] Turing.MultiTapeTM.ComputableInPolyTime

private theorem computableInPolyTime_orExpandWire :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ => orExpandWire q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)) encNat)
      encNat := by
  let encP := encPair (encPair encUnary encUnary) (encPair encUnary encUnary)
  let encQ := encPair encP encNat
  have hp := ComputableInPolyTime.fst encP encNat
  have hn' := hp.fst'.fst'
  have hn := hp.fst'.snd'
  have hs := hp.snd'.fst'
  have ha := hp.snd'.snd'
  have hw := ComputableInPolyTime.snd encP encNat
  have hn'B := ComputableInPolyTime.unary_to_binary.comp hn'
  have hnB := ComputableInPolyTime.unary_to_binary.comp hn
  have hlt1 := ComputableInPolyTime.binary_lt' hw hn'B
  have hlt2 := ComputableInPolyTime.binary_lt' hw hnB
  have hdiffU := binary_min_unary_left' (ComputableInPolyTime.binary_sub' hw hn'B) hn
  have hbit := ComputableInPolyTime.unary_testBit' ha hdiffU
  have hconst := ComputableInPolyTime.ite hbit
    (ComputableInPolyTime.binary_add' hn'B (ComputableInPolyTime.const 1)) hn'B
  have hbaseU : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ => q.1.1.1 + (2 + q.1.2.2 * q.1.2.1))
      encQ encUnary :=
    ComputableInPolyTime.unary_add.comp
      (hn'.prod (ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.const 2).prod (ComputableInPolyTime.unary_mul.comp (ha.prod hs)))))
  have hshifted := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.unary_to_binary.comp hbaseU)
    (ComputableInPolyTime.binary_sub' hw hnB)
  exact (ComputableInPolyTime.ite hlt1 hw (ComputableInPolyTime.ite hlt2 hconst hshifted)).of_enc_eq
    fun q => congrArg encNat
      (by unfold orExpandWire; simp only [Function.comp_apply, decide_eq_true_eq])

private abbrev RawCirc := ℕ × (List (Unbounded.ExtOp × List ℕ) × List ℕ)

private abbrev encRawCirc : RawCirc ↪ List Bool :=
  encPair encUnary (Circuit.encCode Unbounded.encExtOp)

private theorem computableInPolyTime_orExpandCodeFromRaw :
    ComputableInPolyTime orExpandCodeFromRaw
      (encPair encRawCirc (encPair encUnary encUnary)) encRawCirc := by
  let encP := encPair encRawCirc (encPair encUnary encUnary)
  let encG := Circuit.encGate Unbounded.encExtOp
  have hc := ComputableInPolyTime.fst encRawCirc (encPair encUnary encUnary)
  have hk := (ComputableInPolyTime.snd encRawCirc (encPair encUnary encUnary)).fst'
  have hN := (ComputableInPolyTime.snd encRawCirc (encPair encUnary encUnary)).snd'
  have hn := hc.fst'
  have hgatesRaw := hc.snd'.fst'
  have houtsRaw := hc.snd'.snd'
  have hs : ComputableInPolyTime (fun p : RawCirc × (ℕ × ℕ) => p.1.2.1.length) encP encUnary :=
    (ComputableInPolyTime.length_list encG).comp hgatesRaw
  have hout0 : ComputableInPolyTime (fun p : RawCirc × (ℕ × ℕ) => p.1.2.2.getD 0 0) encP encNat :=
    ComputableInPolyTime.listGetDWithInput houtsRaw (ComputableInPolyTime.const 0) 0
  have hn' : ComputableInPolyTime (fun p : RawCirc × (ℕ × ℕ) => p.1.1 - p.2.1) encP encUnary :=
    ComputableInPolyTime.unary_sub.comp (hn.prod hk)
  have hrangeN := ComputableInPolyTime.range.comp hN
  have hbodyRow : ComputableInPolyTime
      (fun q : (RawCirc × (ℕ × ℕ)) × ℕ =>
        q.1.1.2.1.map fun g =>
          (g.1, g.2.map (orExpandWire (q.1.1.1 - q.1.2.1) q.1.1.1 q.1.1.2.1.length q.2)))
      (encPair encP encUnary) (encList encG) := by
    let encQ := encPair encP encUnary
    have hq1 := ComputableInPolyTime.fst encP encUnary
    have ha := ComputableInPolyTime.snd encP encUnary
    have hgateMap : ComputableInPolyTime
        (fun r : ((RawCirc × (ℕ × ℕ)) × ℕ) × (Unbounded.ExtOp × List ℕ) =>
          (r.2.1, r.2.2.map
            (orExpandWire (r.1.1.1.1 - r.1.1.2.1) r.1.1.1.1 r.1.1.1.2.1.length r.1.2)))
        (encPair encQ encG) encG := by
      let encR := encPair encQ encG
      have hr1 := ComputableInPolyTime.fst encQ encG
      have hr2 := ComputableInPolyTime.snd encQ encG
      have hop := hr2.fst'
      have hws : ComputableInPolyTime
          (fun r : ((RawCirc × (ℕ × ℕ)) × ℕ) × (Unbounded.ExtOp × List ℕ) =>
            r.2.2.map
              (orExpandWire (r.1.1.1.1 - r.1.1.2.1) r.1.1.1.1 r.1.1.1.2.1.length r.1.2))
          encR (encList encNat) := by
        have hpar : ComputableInPolyTime
            (fun r : ((RawCirc × (ℕ × ℕ)) × ℕ) × (Unbounded.ExtOp × List ℕ) =>
              ((r.1.1.1.1 - r.1.1.2.1, r.1.1.1.1), (r.1.1.1.2.1.length, r.1.2)))
            encR (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)) :=
          ((hn'.comp (hq1.comp hr1)).prod (hn.comp (hq1.comp hr1))).prod
            ((hs.comp (hq1.comp hr1)).prod (ha.comp hr1))
        exact ComputableInPolyTime.mapWithInput
          (f := fun (r : ((RawCirc × (ℕ × ℕ)) × ℕ) × (Unbounded.ExtOp × List ℕ)) (wire : ℕ) =>
            orExpandWire (r.1.1.1.1 - r.1.1.2.1) r.1.1.1.1 r.1.1.1.2.1.length r.1.2 wire)
          hr2.snd'
          ((computableInPolyTime_orExpandWire.comp
            ((hpar.comp (ComputableInPolyTime.fst encR encNat)).prod
              (ComputableInPolyTime.snd encR encNat))).of_enc_eq fun _ =>
            congrArg encNat (by simp only [Function.comp_apply]))
      exact hop.prod hws
    exact ComputableInPolyTime.mapWithInput (hgatesRaw.comp hq1) hgateMap
  have hbody : ComputableInPolyTime
      (fun p : RawCirc × (ℕ × ℕ) =>
        (List.range p.2.2).flatMap fun a =>
          p.1.2.1.map fun g =>
            (g.1, g.2.map (orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a)))
      encP (encList encG) :=
    ComputableInPolyTime.flatMapWithInput
      (f := fun (p : RawCirc × (ℕ × ℕ)) (a : ℕ) =>
        p.1.2.1.map fun g =>
          (g.1, g.2.map (orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a)))
      hrangeN hbodyRow
  have horWires : ComputableInPolyTime
      (fun p : RawCirc × (ℕ × ℕ) =>
        (List.range p.2.2).map fun a =>
          orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a (p.1.2.2.getD 0 0))
      encP (encList encNat) := by
    let encQ := encPair encP encUnary
    have hq1 := ComputableInPolyTime.fst encP encUnary
    have ha := ComputableInPolyTime.snd encP encUnary
    have hpar := ((hn'.comp hq1).prod (hn.comp hq1)).prod ((hs.comp hq1).prod ha)
    exact ComputableInPolyTime.mapWithInput
      (f := fun (p : RawCirc × (ℕ × ℕ)) (a : ℕ) =>
        orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a (p.1.2.2.getD 0 0))
      hrangeN
      ((computableInPolyTime_orExpandWire.comp (hpar.prod (hout0.comp hq1))).of_enc_eq fun _ =>
        congrArg encNat (by simp only [Function.comp_apply]))
  have hconstGates : ComputableInPolyTime
      (fun _ : RawCirc × (ℕ × ℕ) =>
        ([(.ac (.or 0), []), (.ac (.and 0), [])] : List (Unbounded.ExtOp × List ℕ)))
      encP (encList encG) :=
    ComputableInPolyTime.const _
  have hlastGate : ComputableInPolyTime
      (fun p : RawCirc × (ℕ × ℕ) =>
        [(.ac (.or p.2.2), (List.range p.2.2).map fun a =>
          orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a (p.1.2.2.getD 0 0))])
      encP (encList encG) :=
    (ComputableInPolyTime.cons encG).comp
      (((Unbounded.computableInPolyTime_extOr.comp hN).prod horWires).prod
        (ComputableInPolyTime.const ([] : List (Unbounded.ExtOp × List ℕ))))
  have hgates : ComputableInPolyTime
      (fun p : RawCirc × (ℕ × ℕ) =>
        ([(.ac (.or 0), []), (.ac (.and 0), [])] ++
          ((List.range p.2.2).flatMap fun a =>
            p.1.2.1.map fun g =>
              (g.1, g.2.map (orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a)))) ++
          [(.ac (.or p.2.2), (List.range p.2.2).map fun a =>
            orExpandWire (p.1.1 - p.2.1) p.1.1 p.1.2.1.length a (p.1.2.2.getD 0 0))])
      encP (encList encG) :=
    (ComputableInPolyTime.listAppend encG).comp
      (((ComputableInPolyTime.listAppend encG).comp (hconstGates.prod hbody)).prod hlastGate)
  have houtFinal : ComputableInPolyTime
      (fun p : RawCirc × (ℕ × ℕ) =>
        [p.1.1 - p.2.1 + (2 + p.2.2 * p.1.2.1.length)])
      encP (encList encNat) :=
    (ComputableInPolyTime.cons encNat).comp
      ((ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.unary_add.comp
          (hn'.prod (ComputableInPolyTime.unary_add.comp
            ((ComputableInPolyTime.const 2).prod
              (ComputableInPolyTime.unary_mul.comp (hN.prod hs))))))).prod
        (ComputableInPolyTime.const ([] : List ℕ)))
  exact (hn'.prod (hgates.prod houtFinal)).of_enc_eq fun p =>
    congrArg encRawCirc (by unfold orExpandCodeFromRaw; rfl)

private theorem computableInPolyTime_orExpandCode :
    ComputableInPolyTime
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × (ℕ × ℕ) =>
        orExpandCodeFromRaw ((p.1.1, p.1.2.code), p.2))
      (encPair (Unbounded.encExtCircuit 1) (encPair encUnary encUnary)) encRawCirc := by
  let encC := Unbounded.encExtCircuit 1
  have hc := ComputableInPolyTime.fst encC (encPair encUnary encUnary)
  have hkn := ComputableInPolyTime.snd encC (encPair encUnary encUnary)
  have har := (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
    Unbounded.encExtOp 1).comp hc
  exact (computableInPolyTime_orExpandCodeFromRaw.comp (har.prod hkn)).of_enc_eq fun p =>
    congrArg encRawCirc (by simp only [Function.comp_apply])

end OrExpandPolyTime

/-- **Multi-tape TM complexity of `orExpand`**: expanding the last `min ℓ c.1` inputs of `c` runs
in time and space `O((|enc c| + 2 ^ min ℓ c.1 + ℓ + 1) ^ C)` for a universal constant `C`. -/
theorem computableInO_orExpand :
    ∃ C, ComputableInO
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ => orExpand p.2 p.1)
      (encPair (Unbounded.encExtCircuit 1) encUnary) (Unbounded.encExtCircuit 1)
      (fun p => ((Unbounded.encExtCircuit 1 p.1).length + 2 ^ min p.2 p.1.1 + p.2 + 1) ^ C)
      (fun p => ((Unbounded.encExtCircuit 1 p.1).length + 2 ^ min p.2 p.1.1 + p.2 + 1) ^ C) := by
  let encC := Unbounded.encExtCircuit 1
  let encIn := encPair encC encUnary
  have hkP : ComputableInPolyTime
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ => min p.2 p.1.1) encIn encUnary :=
    ComputableInPolyTime.unary_min' (ComputableInPolyTime.snd encC encUnary)
      ((Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
        Unbounded.encExtOp 1).fst'.comp
        (ComputableInPolyTime.fst encC encUnary))
  have hkBinP : ComputableInPolyTime
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ => min p.2 p.1.1) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp hkP
  obtain ⟨dk, _, hkDeg⟩ := hkP.exists_degree
  obtain ⟨dkb, _, hkbDeg⟩ := hkBinP.exists_degree
  obtain ⟨dr, _, hrDeg⟩ := computableInPolyTime_orExpandCode.exists_degree
  have hpow : ComputableInO
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ => 2 ^ min p.2 p.1.1)
      encIn encUnary _ _ :=
    computableInO_pow2_unary.comp hkbDeg.inO
  have hargs : ComputableInO
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ =>
        (p.1, (min p.2 p.1.1, 2 ^ min p.2 p.1.1)))
      encIn (encPair encC (encPair encUnary encUnary)) _ _ :=
    (ComputableInO.fst encC encUnary).prod (hkDeg.inO.prod hpow)
  have hcomp : ComputableInO
      (fun p : (Σ n, Circuit Unbounded.extSignature n 1) × ℕ => orExpand p.2 p.1)
      encIn encC _ _ :=
    (hrDeg.inO.comp hargs).of_enc_eq fun p => by
      rw [Circuit.encCircuit_apply, ← orExpandCodeFromRaw_eq p.2 p.1]
      rfl
  let D := max (max dk dkb) 3 + 1
  let C := D * (dr + 1) + 4
  let Kconst := 8 ^ dr + 2 * 3 ^ D + 16
  refine ⟨C, hcomp.mono Kconst (fun p => ?_) (fun p => ?_)⟩
  all_goals
    set E := (Unbounded.encExtCircuit 1 p.1).length
    set k := min p.2 p.1.1
    set B := E + 2 ^ k + p.2 + 1
    have hB1 : 1 ≤ B := Nat.succ_pos _
    have hD4 : 4 ≤ D := by dsimp only [D]; omega
    have hk_le : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hlen_in : (encIn p).length + 1 ≤ 3 * B := by
      dsimp only [encIn, encC]
      rw [length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [E, B]; omega
    have hpow_le : ∀ e ≤ D, ((encIn p).length + 1) ^ e ≤ 3 ^ D * B ^ D := fun e he => by
      calc ((encIn p).length + 1) ^ e ≤ (3 * B) ^ e := Nat.pow_le_pow_left hlen_in e
        _ ≤ (3 * B) ^ D := Nat.pow_le_pow_right (by omega) he
        _ = 3 ^ D * B ^ D := Nat.mul_pow 3 B D
    have hpad_le : (k + 1) * (2 ^ k + (k + 1) ^ 2) ≤ 4 * B ^ 3 := by
      have hk1 : k + 1 ≤ B := by dsimp only [B]; omega
      have h2k : 2 ^ k ≤ B := by dsimp only [B]; omega
      have : B ≤ B ^ 2 := Nat.le_self_pow two_ne_zero B
      calc (k + 1) * (2 ^ k + (k + 1) ^ 2) ≤ B * (2 * B ^ 2) :=
            Nat.mul_le_mul hk1 (by have := Nat.pow_le_pow_left hk1 2; omega)
        _ ≤ 4 * B ^ 3 := by ring_nf; omega
    have harg_len : (encPair (Unbounded.encExtCircuit 1) (encPair encUnary encUnary)
        (p.1, (k, 2 ^ k))).length + 1 ≤ 8 * B := by
      rw [length_encPair, length_encPair, encUnary_apply, encUnary_apply,
        List.length_replicate, List.length_replicate]
      dsimp only [E, B]; omega
    have harg_pow : ((encPair (Unbounded.encExtCircuit 1) (encPair encUnary encUnary)
        (p.1, (k, 2 ^ k))).length + 1) ^ dr ≤ 8 ^ dr * B ^ dr := by
      calc _ ≤ (8 * B) ^ dr := Nat.pow_le_pow_left harg_len dr
        _ = 8 ^ dr * B ^ dr := Nat.mul_pow 8 B dr
    have hBC_D : B ^ D ≤ B ^ C := Nat.pow_le_pow_right hB1 (by dsimp only [C]; nlinarith only [hD4])
    have hBC_dr : B ^ dr ≤ B ^ C :=
      Nat.pow_le_pow_right hB1 (by dsimp only [C]; nlinarith only [hD4])
    have hBC_3 : B ^ 3 ≤ B ^ C := Nat.pow_le_pow_right hB1 (by dsimp only [C]; nlinarith only [hD4])
    have hBC_1 : B ≤ B ^ C := Nat.le_self_pow (by dsimp only [C]; omega) B
    have hdk_le : ((encIn p).length + 1) ^ dk ≤ 3 ^ D * B ^ C :=
      (hpow_le dk (by dsimp only [D]; omega)).trans (Nat.mul_le_mul_left _ hBC_D)
    have hdkb_le : ((encIn p).length + 1) ^ dkb ≤ 3 ^ D * B ^ C :=
      (hpow_le dkb (by dsimp only [D]; omega)).trans (Nat.mul_le_mul_left _ hBC_D)
    have hdr_le : ((encPair (Unbounded.encExtCircuit 1) (encPair encUnary encUnary)
        (p.1, (k, 2 ^ k))).length + 1) ^ dr ≤ 8 ^ dr * B ^ C :=
      harg_pow.trans (Nat.mul_le_mul_left _ hBC_dr)
    have hpad_C : (k + 1) * (2 ^ k + (k + 1) ^ 2) ≤ 4 * B ^ C :=
      hpad_le.trans (Nat.mul_le_mul_left 4 hBC_3)
    have h2k_C : 2 ^ k + k ≤ 2 * B ^ C := by omega
    have hin_C : (encPair encC encUnary p).length ≤ 3 * B ^ C := by
      have : (encPair encC encUnary p).length = (encIn p).length := rfl
      omega
    have hbound : 3 * B ^ C + (3 ^ D * B ^ C + (3 ^ D * B ^ C + 4 * B ^ C)) + 8 ^ dr * B ^ C ≤
        Kconst * (B ^ C + 1) := by
      dsimp only [Kconst]
      have hdist : (8 ^ dr + 2 * 3 ^ D + 16) * (B ^ C + 1) =
          8 ^ dr * B ^ C + 3 ^ D * B ^ C + 3 ^ D * B ^ C + 16 * B ^ C +
            (8 ^ dr + 2 * 3 ^ D + 16) := by ring
      rw [hdist]
      have h0 : 0 ≤ 8 ^ dr + 2 * 3 ^ D + 16 := Nat.zero_le _
      omega
    first
      | exact (Nat.add_le_add
          (Nat.add_le_add hin_C (Nat.add_le_add hdk_le (Nat.add_le_add hdkb_le hpad_C)))
          hdr_le).trans hbound
      | exact (Nat.add_le_add
          (Nat.add_le_add hin_C
            (Nat.add_le_add hdk_le (Nat.add_le_add hdkb_le (h2k_C.trans (by omega)))))
          hdr_le).trans hbound

/-! ### 2. Evaluating `SYM ∘ AND` satisfiability via Yates's algorithm (`symAndSAT`) -/

/-- Satisfiability of a compiled `(SymAndInstance, SymOutParam)` pair: checks whether some entry of
the Yates satisfied-AND count list `q.1.countList` is accepted by `q.2.eval`. -/
@[expose] def symAndSAT (q : SymAndInstance × SymOutParam) : Bool :=
  q.1.countList.any q.2.eval

/-- `symAndSAT (x, p)` is `true` iff `x.toSymAnd p.eval` is satisfiable. -/
theorem symAndSAT_eq_true_iff (q : SymAndInstance × SymOutParam) :
    symAndSAT q = true ↔ ∃ v : BitString q.1.n, (q.1.toSymAnd q.2.eval).eval v = true := by
  simp only [symAndSAT, List.any_eq_true]
  constructor
  · rintro ⟨cnt, hmem, hev⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hmem
    have hget := q.1.getElem_countList q.2.eval k hk
    refine ⟨(BitString.equivFin q.1.n).symm ⟨k, by simpa using hk⟩, ?_⟩
    simpa only [SymAnd.eval, SymAndInstance.toSymAnd, hget] using hev
  · rintro ⟨v, hv⟩
    let k : Fin (2 ^ q.1.n) := BitString.equivFin q.1.n v
    have hk : k.1 < q.1.countList.length := by simp [k.isLt]
    refine ⟨q.1.countList[k.1]'hk, List.getElem_mem hk, ?_⟩
    rw [q.1.getElem_countList q.2.eval k.1 hk]
    have hv' : (BitString.equivFin q.1.n).symm ⟨k.1, by simp [k.isLt]⟩ = v :=
      (BitString.equivFin q.1.n).symm_apply_apply v
    simpa only [SymAnd.eval, SymAndInstance.toSymAnd, hv'] using hv

private def maxNatLen (l : List ℕ) : ℕ :=
  l.foldl (fun acc z => max acc (encNat z).length) 0

private theorem le_foldl_maxNatLen (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl (fun acc z => max acc (encNat z).length) a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons z zs ih => exact (le_max_left a _).trans (ih _)

private theorem mem_le_maxNatLen {l : List ℕ} {z : ℕ} (hz : z ∈ l) :
    (encNat z).length ≤ maxNatLen l := by
  suffices ∀ a, (encNat z).length ≤ l.foldl (fun acc w => max acc (encNat w).length) a from this 0
  induction l with
  | nil => exact absurd hz List.not_mem_nil
  | cons w ws ih =>
    intro a
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact (le_max_right a _).trans (le_foldl_maxNatLen ws _)
    · exact ih hz' _

private theorem maxNatLen_le {l : List ℕ} {B : ℕ} (h : ∀ z ∈ l, (encNat z).length ≤ B) :
    maxNatLen l ≤ B := by
  suffices ∀ a, a ≤ B → l.foldl (fun acc z => max acc (encNat z).length) a ≤ B from
    this 0 (Nat.zero_le B)
  induction l with
  | nil => intro a ha; exact ha
  | cons z zs ih =>
    intro a ha
    simp only [List.foldl_cons]
    exact ih (fun w hw => h w (List.mem_cons_of_mem z hw)) _
      (max_le ha (h z List.mem_cons_self))

private def streamAnyEval (r : SymOutParam × List ℕ) : List Bool :=
  r.2.flatMap fun z => if r.1.eval z then [true] else []

private theorem encList_streamAnyEval (r : SymOutParam × List ℕ) :
    encList encBool (streamAnyEval r) =
      streamEmit (fun p : SymOutParam × ℕ => p.1)
        (fun p => encList encBool (if p.1.eval p.2 then [true] else [])) r.1 r.2 := by
  rcases r with ⟨p, l⟩
  induction l with
  | nil => rfl
  | cons z zs ih =>
    simp only [streamAnyEval, List.flatMap_cons, encList_append, streamEmit] at ih ⊢
    rw [ih]

private theorem length_encList_streamAnyEval_le (r : SymOutParam × List ℕ) :
    (encList encBool (streamAnyEval r)).length ≤ 3 * r.2.length := by
  rcases r with ⟨p, l⟩
  induction l with
  | nil => simp [streamAnyEval, encList_nil]
  | cons z zs ih =>
    simp only [streamAnyEval, List.flatMap_cons, encList_append, List.length_append,
      List.length_cons] at ih ⊢
    cases p.eval z
    · simp only [Bool.false_eq_true, ↓reduceIte, encList_nil, List.length_nil, zero_add]
      omega
    · simp only [↓reduceIte, encList_cons, encList_nil, List.append_nil, length_frame,
        encBool_apply, List.length_singleton]
      omega

private theorem foldl_const_true (bs : List Bool) (b : Bool) :
    bs.foldl (fun _ _ => true) b = (b || !bs.isEmpty) := by
  induction bs generalizing b with
  | nil => simp
  | cons a rest ih => simp [ih]

private theorem encList_isEmpty_eq (l : List Bool) :
    (encList encBool l).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons a rest =>
    rw [encList_cons]
    simp only [List.isEmpty_append, List.isEmpty_cons, Bool.and_eq_false_iff]
    left
    exact List.isEmpty_eq_false_iff.2 (frame_ne_nil _)

private theorem streamAnyEval_isEmpty (r : SymOutParam × List ℕ) :
    (streamAnyEval r).isEmpty = !r.2.any r.1.eval := by
  rcases r with ⟨p, l⟩
  induction l with
  | nil => rfl
  | cons z zs ih =>
    simp only [streamAnyEval, List.flatMap_cons, List.isEmpty_append, List.any_cons] at ih ⊢
    cases p.eval z
    · simp [ih]
    · simp

private theorem foldl_encList_streamAnyEval (r : SymOutParam × List ℕ) :
    (encList encBool (streamAnyEval r)).foldl (fun _ _ => true) false = r.2.any r.1.eval := by
  rw [foldl_const_true, Bool.false_or, encList_isEmpty_eq, streamAnyEval_isEmpty, Bool.not_not]

private theorem computableInO_anyEval :
    ∃ d, ComputableInO (fun r : SymOutParam × List ℕ => r.2.any r.1.eval)
      (encPair encSymOutParam (encList encNat)) encBool
      (fun r => (encPair encSymOutParam (encList encNat) r).length +
        (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d + 1)
      (fun r => (encPair encSymOutParam (encList encNat) r).length +
        (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d + 1) := by
  have hnext : ComputableInPolyTime (fun p : SymOutParam × ℕ => p.1)
      (encPair encSymOutParam encNat) encSymOutParam :=
    ComputableInPolyTime.fst encSymOutParam encNat
  have hemit : ComputableInPolyTime
      (fun p : SymOutParam × ℕ => if p.1.eval p.2 then ([true] : List Bool) else [])
      (encPair encSymOutParam encNat) (encList encBool) :=
    ComputableInPolyTime.ite SymOutParam.computableInPolyTime_eval
      (ComputableInPolyTime.const [true]) (ComputableInPolyTime.const [])
  have hstate_const : ∀ (p : SymOutParam) (l : List ℕ) (j : ℕ),
      streamState p (fun q : SymOutParam × ℕ => q.1) l j = p := fun _ l j =>
    List.foldl_fixed (l.take j)
  obtain ⟨c, d, hsf⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encNat) (encS := encSymOutParam) (encB := encBool)
    (encIn := encPair encSymOutParam (encList encNat))
    (init := Prod.fst) (elems := Prod.snd) (fun _ => rfl)
    hnext hemit (g := streamAnyEval) encList_streamAnyEval
    (lMax := fun r => (encSymOutParam r.1).length + maxNatLen r.2)
    (fun r j _ => by rw [hstate_const]; exact Nat.le_add_right _ _)
    (fun r j hj => (mem_le_maxNatLen (List.getElem_mem hj)).trans (Nat.le_add_left _ _))
  have hr : ∀ r : SymOutParam × List ℕ, r.2.length ≤
      (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d := fun r =>
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _)))
  have hsfO : ComputableInO streamAnyEval (encPair encSymOutParam (encList encNat))
      (encList encBool)
      (fun r => (encPair encSymOutParam (encList encNat) r).length +
        (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d + 1)
      (fun r => (encPair encSymOutParam (encList encNat) r).length +
        (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d + 1) := by
    refine ComputableInO.of_bounds hsf (c + 4) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · exact Nat.mul_le_mul (by omega) (by omega)
    · have h1 : ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d ≤
          (r.2.length + 1) * ((encSymOutParam r.1).length + maxNatLen r.2 + 1) ^ d :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      exact Nat.mul_le_mul (by omega) (by omega)
    · nlinarith only [length_encList_streamAnyEval_le r, hr r]
  have hbitsO : ComputableInO (fun r => encList encBool (streamAnyEval r))
      (encPair encSymOutParam (encList encNat)) encBits _ _ :=
    hsfO.of_enc_eq fun _ => rfl
  have hfoldO : ComputableInO (fun bs : List Bool => bs.foldl (fun _ _ => true) false)
      encBits encBool List.length (fun _ => 0) :=
    ComputableInO.foldl_bits_finite encBool (fun _ _ => true) false
  have hcomp : ComputableInO (fun r : SymOutParam × List ℕ => r.2.any r.1.eval)
      (encPair encSymOutParam (encList encNat)) encBool _ _ :=
    (hfoldO.comp hbitsO).of_enc_eq fun r =>
      congrArg encBool (by simp only [Function.comp_apply, foldl_encList_streamAnyEval])
  refine ⟨d, hcomp.mono 5 (fun r => ?_) (fun r => ?_)⟩
  all_goals
    have := length_encList_streamAnyEval_le r
    have := hr r
    omega

/-- **Multi-tape TM complexity of `symAndSAT`** ([Williams2014], Lemma 4.2 + streaming evaluation):
checking whether a compiled `(SymAndInstance, SymOutParam)` pair is satisfiable runs in time and
space `O((2 ^ x.n + (|enc x| + 1) ^ c) * (x.n + |enc p| + x.gates.length.size + 1) ^ c)`.
Crucially, the factor multiplying `2 ^ x.n` depends only on `x.n`, `|enc p|`, and the bit-length
`x.gates.length.size`, never on the full size `|enc x|`. -/
theorem computableInO_symAndSAT :
    ∃ c, ComputableInO symAndSAT (encPair encSymAndInstance encSymOutParam) encBool
      (fun q => (2 ^ q.1.n + ((encSymAndInstance q.1).length + 1) ^ c) *
        (q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1) ^ c)
      (fun q => (2 ^ q.1.n + ((encSymAndInstance q.1).length + 1) ^ c) *
        (q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1) ^ c) := by
  obtain ⟨c₁, hcnt⟩ := computableInO_countList
  obtain ⟨d₂, hany⟩ := computableInO_anyEval
  have hstage1 : ComputableInO
      (fun q : SymAndInstance × SymOutParam => (q.2, q.1.countList))
      (encPair encSymAndInstance encSymOutParam) (encPair encSymOutParam (encList encNat)) _ _ :=
    (ComputableInO.snd encSymAndInstance encSymOutParam).prod
      (hcnt.comp (ComputableInO.fst encSymAndInstance encSymOutParam))
  have hcomp : ComputableInO symAndSAT (encPair encSymAndInstance encSymOutParam) encBool _ _ :=
    (hany.comp hstage1).of_enc_eq fun q => congrArg encBool rfl
  let c := max c₁ (d₂ + 2) + 1
  refine ⟨c, hcomp.mono 16 (fun q => ?_) (fun q => ?_)⟩
  all_goals
    set E := (encSymAndInstance q.1).length + 1
    set P := q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1
    set T := (2 ^ q.1.n + E ^ c) * P ^ c
    have hE1 : 1 ≤ E := Nat.succ_pos _
    have hP1 : 1 ≤ P := Nat.succ_pos _
    have h2n1 : 1 ≤ 2 ^ q.1.n := Nat.one_le_pow _ _ (by decide)
    have hT1 : 1 ≤ T := Nat.mul_pos (by omega) (Nat.one_le_pow _ _ hP1)
    have hz : ∀ z ∈ q.1.countList, (encNat z).length ≤ q.1.gates.length.size := fun z hz => by
      rw [encNat_apply]
      simpa only [← Nat.size_eq_bits_len] using
        Nat.size_le_size (q.1.countList_le_gates_length hz)
    have hmaxLen : maxNatLen q.1.countList ≤ q.1.gates.length.size := maxNatLen_le hz
    have hlistLen : (encList encNat q.1.countList).length ≤
        2 ^ q.1.n * (2 * q.1.gates.length.size + 1) := by
      simpa only [SymAndInstance.length_countList] using length_encList_le encNat _ hz
    have hpairLen : (encPair encSymOutParam (encList encNat) (q.2, q.1.countList)).length ≤
        2 * (encSymOutParam q.2).length + 2 ^ q.1.n * (2 * q.1.gates.length.size + 1) + 1 := by
      rw [length_encPair]; dsimp only; omega
    have hpairIn : (encPair encSymAndInstance encSymOutParam q).length ≤ 2 * E + P := by
      rw [length_encPair]; dsimp only [E, P]; omega
    have hP_c : P ≤ P ^ c := Nat.le_self_pow (by dsimp only [c]; omega) P
    have hE_c : E ≤ E ^ c := Nat.le_self_pow (by dsimp only [c]; omega) E
    have hPc1 : (q.1.n + 1) ^ c₁ ≤ P ^ c :=
      (Nat.pow_le_pow_left (by dsimp only [P]; omega) c₁).trans
        (Nat.pow_le_pow_right hP1 (by dsimp only [c]; omega))
    have hEc1 : E ^ c₁ ≤ E ^ c := Nat.pow_le_pow_right hE1 (by dsimp only [c]; omega)
    have hcnt_le : (2 ^ q.1.n + E ^ c₁) * (q.1.n + 1) ^ c₁ ≤ T :=
      Nat.mul_le_mul (Nat.add_le_add_left hEc1 _) hPc1
    have hP_d2 : ((encSymOutParam q.2).length + maxNatLen q.1.countList + 1) ^ d₂ ≤ P ^ c :=
      (Nat.pow_le_pow_left (by dsimp only [P]; omega) d₂).trans
        (Nat.pow_le_pow_right hP1 (by dsimp only [c]; omega))
    have hstream_le : (q.1.countList.length + 1) *
        ((encSymOutParam q.2).length + maxNatLen q.1.countList + 1) ^ d₂ ≤ 2 * T := by
      rw [SymAndInstance.length_countList]
      calc (2 ^ q.1.n + 1) * ((encSymOutParam q.2).length + maxNatLen q.1.countList + 1) ^ d₂
          ≤ (2 * 2 ^ q.1.n) * P ^ c := Nat.mul_le_mul (by omega) hP_d2
        _ = 2 * (2 ^ q.1.n * P ^ c) := by ring
        _ ≤ 2 * T := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    have hpair_T : (encPair encSymOutParam (encList encNat) (q.2, q.1.countList)).length ≤
        5 * T := by
      have h1 : 2 ^ q.1.n * (2 * q.1.gates.length.size + 1) ≤ 2 * (2 ^ q.1.n * P) := by
        have : 2 * q.1.gates.length.size + 1 ≤ 2 * P := by dsimp only [P]; omega
        calc 2 ^ q.1.n * (2 * q.1.gates.length.size + 1)
            ≤ 2 ^ q.1.n * (2 * P) := Nat.mul_le_mul_left _ this
          _ = 2 * (2 ^ q.1.n * P) := by ring
      have h2 : 2 ^ q.1.n * P ≤ T :=
        Nat.mul_le_mul (Nat.le_add_right _ _) hP_c
      have h3 : (encSymOutParam q.2).length ≤ T :=
        ((by dsimp only [P]; omega : (encSymOutParam q.2).length ≤ P).trans hP_c).trans
          (Nat.le_mul_of_pos_left _ (by omega))
      omega
    have hin_T : (encPair encSymAndInstance encSymOutParam q).length ≤ 3 * T := by
      have h1 : E ≤ T := (hE_c.trans (Nat.le_add_left _ _)).trans
        (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hP1))
      have h2 : P ≤ T := hP_c.trans (Nat.le_mul_of_pos_left _ (by omega))
      omega
    dsimp only [T] at hT1 hcnt_le hstream_le hpair_T hin_T ⊢
    omega

/-! ### 3. Elementary real-analysis dominance helpers -/

private theorem nthRoot_le_self {r : ℕ} (hr : 0 < r) (n : ℕ) : Nat.nthRoot r n ≤ n := by
  have hpow := Nat.pow_nthRoot_le (n := r) (a := n) (Or.inl hr.ne')
  exact (Nat.le_self_pow hr.ne' _).trans hpow

private theorem nthRoot_anti {r₁ r₂ : ℕ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂) (n : ℕ) :
    Nat.nthRoot r₂ n ≤ Nat.nthRoot r₁ n := by
  by_cases h0 : Nat.nthRoot r₂ n = 0
  · omega
  · have hpow2 : (Nat.nthRoot r₂ n) ^ r₂ ≤ n :=
      Nat.pow_nthRoot_le (n := r₂) (a := n) (Or.inl (by omega))
    have hpow1 : (Nat.nthRoot r₂ n) ^ r₁ ≤ n :=
      (Nat.pow_le_pow_right (by omega) hle).trans hpow2
    have hlt := Nat.lt_pow_nthRoot_add_one hr₁.ne' n
    by_contra hgt
    push Not at hgt
    have hge : Nat.nthRoot r₁ n + 1 ≤ Nat.nthRoot r₂ n := by omega
    have := (Nat.pow_le_pow_left hge r₁).trans hpow1
    omega

private theorem add_one_pow_le_two_pow_mul (y : ℝ) (K : ℕ) (hy : 0 ≤ y) :
    (y + 1) ^ K ≤ (2 : ℝ) ^ K * (y ^ K + 1) := by
  by_cases h1 : y ≤ 1
  · have hle : (y + 1) ^ K ≤ (2 : ℝ) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    have hyK : 0 ≤ y ^ K := pow_nonneg hy K
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
  · push Not at h1
    have hle : (y + 1) ^ K ≤ (2 * y) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    rw [mul_pow] at hle
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]

private theorem nat_rpow_le_rpow_add_one (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (n : ℝ) ^ a ≤ (n : ℝ) ^ b + 1 := by
  cases n with
  | zero =>
    rw [Nat.cast_zero, Real.zero_rpow ha.ne', Real.zero_rpow (ha.trans_le hab).ne']
    norm_num
  | succ k =>
    have h1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hle := Real.rpow_le_rpow_of_exponent_le h1 hab
    linarith

private theorem pow_le_mul_two_rpow_half_rpow (p D : ℕ) (hp : 0 < p) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      ((n : ℝ) + 1) ^ D ≤ M * (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p : ℝ)⁻¹)) := by
  set c : ℝ := (1 / 2 : ℝ) * Real.log 2
  have hc : 0 < c := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hcp : 0 < c ^ (p * D) := pow_pos hc (p * D)
  set M : ℝ := (2 : ℝ) ^ D * (((p * D).factorial : ℝ) / c ^ (p * D)) + 1
  have hM : 0 < M := by positivity
  refine ⟨M, hM, fun n => ?_⟩
  cases n with
  | zero =>
    have hinv : ((p : ℝ)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hp.ne')
    simp only [Nat.cast_zero, zero_add, one_pow, Real.zero_rpow hinv, mul_zero, Real.rpow_zero,
      mul_one]
    have h0 : 0 ≤ (2 : ℝ) ^ D * (((p * D).factorial : ℝ) / c ^ (p * D)) := by positivity
    linarith
  | succ k =>
    set r : ℝ := ((k + 1 : ℕ) : ℝ)
    have hr1 : 1 ≤ r := by dsimp only [r]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hr0 : 0 ≤ r := by linarith
    set x : ℝ := c * r ^ ((p : ℝ)⁻¹)
    have hx : 0 ≤ x := mul_nonneg hc.le (Real.rpow_nonneg hr0 _)
    have hexp : Real.exp x = (2 : ℝ) ^ ((1 / 2 : ℝ) * r ^ ((p : ℝ)⁻¹)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp only [x, c]
      ring
    have hfac := Real.pow_div_factorial_le_exp x hx (p * D)
    rw [hexp] at hfac
    have hxpow : x ^ (p * D) = c ^ (p * D) * r ^ D := by
      dsimp only [x]
      rw [mul_pow]
      congr 1
      rw [pow_mul, Real.rpow_inv_natCast_pow hr0 hp.ne']
    rw [hxpow] at hfac
    have hfac_pos : (0 : ℝ) < ((p * D).factorial : ℝ) := by positivity
    have hrD : r ^ D ≤ (((p * D).factorial : ℝ) / c ^ (p * D)) *
        (2 : ℝ) ^ ((1 / 2 : ℝ) * r ^ ((p : ℝ)⁻¹)) := by
      have hmul := (div_le_iff₀ hfac_pos).1 hfac
      rw [div_mul_eq_mul_div, le_div_iff₀ hcp]
      linarith
    have hstep : (r + 1) ^ D ≤ (2 : ℝ) ^ D * r ^ D := by
      have : (r + 1) ^ D ≤ (2 * r) ^ D := pow_le_pow_left₀ (by linarith) (by linarith) D
      rwa [mul_pow] at this
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ) * r ^ ((p : ℝ)⁻¹)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h1 := mul_le_mul_of_nonneg_left hrD (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) D)
    dsimp only [M]
    nlinarith only [hstep, h1, h2pos]

private theorem two_rpow_sqrt_le_mul_two_rpow_sub (A B : ℝ) (hA : 0 ≤ A) (p : ℕ) (hp : 2 ≤ p) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      (2 : ℝ) ^ (A * (n : ℝ) ^ (1 / 2 : ℝ) + B) ≤
        M * (2 : ℝ) ^ ((n : ℝ) - (1 / 2 : ℝ) * (n : ℝ) ^ ((p : ℝ)⁻¹)) := by
  set C : ℝ := (A + 1 / 2) ^ 2 + B + 1 / 2
  refine ⟨(2 : ℝ) ^ C, Real.rpow_pos_of_pos (by norm_num) C, fun n => ?_⟩
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
  have hp_inv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hp)
  have hroot : (n : ℝ) ^ ((p : ℝ)⁻¹) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + 1 :=
    nat_rpow_le_rpow_add_one n (by positivity) hp_inv
  set t : ℝ := (n : ℝ) ^ (1 / 2 : ℝ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have htsq : t ^ 2 = (n : ℝ) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hquad : 0 ≤ (t - (A + 1 / 2)) ^ 2 := sq_nonneg _
  have hmul_nonneg : 0 ≤ (A + 1 / 2) * t := mul_nonneg (by linarith) ht0
  dsimp only [C]
  nlinarith only [hroot, htsq, hquad, hmul_nonneg]

/-! ### 4. Williams's Theorem 4.1: faster-than-brute-force `ACC⁰-SAT` -/

/-- **Bounded-depth, bounded-size `ACC⁰[m]` circuit satisfiability**: single-output circuits over
`Unbounded.extSignature` with `MOD_m` gates of depth at most `d` and encoding length at most
`2 ^ (Nat.nthRoot q n + 1)` that are satisfiable. Because `n ^ (1 / q) < Nat.nthRoot q n + 1`,
every circuit of depth at most `d` and encoding length at most `2 ^ (n ^ (1 / q))` satisfies the
size bound. -/
@[expose] def ACC0SAT (d m q : ℕ) : Set (Σ n, Circuit Unbounded.extSignature n 1) :=
  {c | c ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) ∧
    c.2.depth ≤ d ∧
    (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot q c.1 + 1)}

private theorem size_sub_one_le_iff (L B : ℕ) : (L - 1).size ≤ B ↔ L ≤ 2 ^ B := by
  cases L with
  | zero => simp
  | succ L =>
    simp only [Nat.add_sub_cancel, Nat.size_le]
    omega

private def acc0GuardRaw (d q : ℕ) (p : (ℕ × ℕ) × ℕ) : Bool :=
  decide (p.1.1 ≤ d) && decide ((p.1.2 - 1).size ≤ Nat.nthRoot q p.2 + 1)

private def acc0Guard (d q : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) : Bool :=
  acc0GuardRaw d q ((c.2.depth, (Unbounded.encExtCircuit 1 c).length), c.1)

private theorem acc0Guard_eq_true_iff (d q : ℕ) (c : Σ n, Circuit Unbounded.extSignature n 1) :
    acc0Guard d q c = true ↔
      c.2.depth ≤ d ∧ (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot q c.1 + 1) := by
  simp only [acc0Guard, acc0GuardRaw, Bool.and_eq_true, decide_eq_true_eq, size_sub_one_le_iff]

private theorem acc0Guard_of_rpow {d q : ℕ} (hq : q ≠ 0)
    (c : Σ n, Circuit Unbounded.extSignature n 1) (hd : c.2.depth ≤ d)
    (hsize : ((Unbounded.encExtCircuit 1 c).length : ℝ) ≤ (2 : ℝ) ^ ((c.1 : ℝ) ^ ((q : ℝ)⁻¹))) :
    acc0Guard d q c = true := by
  rw [acc0Guard_eq_true_iff]
  refine ⟨hd, ?_⟩
  have hlt := Real.rpow_lt_natCast_nthRoot_add_one q c.1 hq
  have hpow : (2 : ℝ) ^ ((c.1 : ℝ) ^ ((q : ℝ)⁻¹)) ≤
      ((2 ^ (Nat.nthRoot q c.1 + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by push_cast; linarith)
  exact_mod_cast hsize.trans hpow

section GuardPolyTime

attribute [local irreducible] Turing.MultiTapeTM.ComputableInPolyTime

private theorem computableInPolyTime_acc0GuardRaw (d q : ℕ) :
    ComputableInPolyTime (acc0GuardRaw d q)
      (encPair (encPair encUnary encUnary) encUnary) encBool := by
  let encP := encPair (encPair encUnary encUnary) encUnary
  have hdep := (ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary).fst'
  have hlen := (ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary).snd'
  have hn := ComputableInPolyTime.snd (encPair encUnary encUnary) encUnary
  have hdepth := ComputableInPolyTime.unary_le' hdep (ComputableInPolyTime.const d)
  have hsub := ComputableInPolyTime.unary_sub.comp (hlen.prod (ComputableInPolyTime.const 1))
  have hsz := ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp hsub)
  have hroot := ComputableInPolyTime.binary_nthRoot' (ComputableInPolyTime.const q)
    (ComputableInPolyTime.unary_to_binary.comp hn)
  have hroot1 := ComputableInPolyTime.binary_add' hroot (ComputableInPolyTime.const 1)
  have hsz_le := ComputableInPolyTime.binary_le'
    (ComputableInPolyTime.unary_to_binary.comp hsz) hroot1
  exact (ComputableInPolyTime.bool_and' hdepth hsz_le).of_enc_eq fun p =>
    congrArg encBool (by unfold acc0GuardRaw; simp only [Function.comp_apply])

private theorem computableInPolyTime_acc0Guard (d q : ℕ) :
    ComputableInPolyTime (acc0Guard d q) (Unbounded.encExtCircuit 1) encBool := by
  let encC := Unbounded.encExtCircuit 1
  have hdep := computableInPolyTime_extCircuit_depth
  have hlen := ComputableInPolyTime.encoding_length encC
  have hn := (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
    Unbounded.encExtOp 1).fst'
  exact ((computableInPolyTime_acc0GuardRaw d q).comp ((hdep.prod hlen).prod hn)).of_enc_eq fun c =>
    congrArg encBool (by unfold acc0Guard; simp only [Function.comp_apply, encC])

private theorem computableInPolyTime_nthRoot_nat_unary (p_root : ℕ) (hp : 0 < p_root) :
    ComputableInPolyTime (fun n : ℕ => Nat.nthRoot p_root n) encUnary encUnary := by
  have hroot := ComputableInPolyTime.binary_nthRoot'
    (ComputableInPolyTime.const (encIn := encUnary) p_root)
    ComputableInPolyTime.unary_to_binary
  exact ComputableInPolyTime.binary_to_unary_bounded hroot ComputableInPolyTime.id'
    (nthRoot_le_self hp)

private theorem computableInPolyTime_nthRoot_unary (p_root : ℕ) (hp : 0 < p_root) :
    ComputableInPolyTime
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => Nat.nthRoot p_root c.1)
      (Unbounded.encExtCircuit 1) encUnary :=
  ((computableInPolyTime_nthRoot_nat_unary p_root hp).comp
    (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).fst').of_enc_eq fun _ =>
    congrArg encUnary (by simp only [Function.comp_apply])

end GuardPolyTime

private def acc0Pipeline (d m p_root : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) : Bool :=
  symAndSAT (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c))

private def acc0Decider (d m p_root q_root : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) : Bool :=
  if acc0Guard d q_root c then acc0Pipeline d m p_root c else false

private theorem acc0Pipeline_eq_true_iff (d : ℕ) {m : ℕ} (hm : 0 < m) (p_root : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) (hd : c.2.depth ≤ d) :
    acc0Pipeline d m p_root c = true ↔
      c ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  set c' := orExpand (Nat.nthRoot p_root c.1) c
  have hd' : c'.2.depth ≤ d + 2 := (depth_orExpand_le _ c).trans (Nat.add_le_add_right hd 2)
  rw [acc0Pipeline, symAndSAT_eq_true_iff,
    ← orExpand_mem_SignatureCircuitSAT_iff (Nat.nthRoot p_root c.1) c, mem_SignatureCircuitSAT]
  have hev := eval_compileSymAndFixed (d + 2) hm c' hd'
  set inst := (compileSymAndFixed (d + 2) m c').1
  set out := (compileSymAndFixed (d + 2) m c').2.eval
  have hn : inst.n = c'.1 := compileSymAndFixed_n (d + 2) m c'
  have hcast : ∀ (n₁ n₂ : ℕ) (h : n₁ = n₂) (S : SymAnd (Fin n₁)),
      (∃ v : BitString n₁, S.eval v = true) ↔
        ∃ v : BitString n₂, (h ▸ S : SymAnd (Fin n₂)).eval v = true := by
    rintro n _ rfl S; exact Iff.rfl
  rw [hcast inst.n c'.1 hn (inst.toSymAnd out), hev]

private theorem acc0Decider_eq_true_iff (d : ℕ) {m : ℕ} (hm : 0 < m) (p_root q_root : ℕ)
    (c : Σ n, Circuit Unbounded.extSignature n 1) :
    acc0Decider d m p_root q_root c = true ↔ c ∈ ACC0SAT d m q_root := by
  simp only [acc0Decider, ACC0SAT, Set.mem_ofPred_eq]
  cases h : acc0Guard d q_root c
  · simp only [Bool.false_eq_true, ↓reduceIte, false_iff]
    rintro ⟨_, hd, hsize⟩
    have := (acc0Guard_eq_true_iff d q_root c).2 ⟨hd, hsize⟩
    rw [h] at this
    exact Bool.false_ne_true this
  · obtain ⟨hd, hsize⟩ := (acc0Guard_eq_true_iff d q_root c).1 h
    simp only [↓reduceIte, acc0Pipeline_eq_true_iff d hm p_root c hd]
    exact ⟨fun hsat => ⟨hsat, hd, hsize⟩, fun ⟨hsat, _, _⟩ => hsat⟩

/-- Encoding length bound for `SymOutParam` in terms of `thresh`, `mods.length`, and max modulus
bit-length. -/
private theorem length_encSymOutParam_le (p : SymOutParam) {B : ℕ}
    (hB : ∀ M ∈ p.mods, M.size ≤ B) :
    (encSymOutParam p).length ≤ 2 * p.thresh.size + p.mods.length * (2 * B + 1) + 1 := by
  rw [encSymOutParam_apply, length_encPair]
  dsimp only
  have hth : (encNat p.thresh).length = p.thresh.size := by
    rw [encNat_apply, Nat.size_eq_bits_len]
  have hmods := length_encList_le encNat p.mods (b := B) fun M hM => by
    rw [encNat_apply]
    simpa only [← Nat.size_eq_bits_len] using hB M hM
  omega

/-- Polynomial bound on the per-element streaming parameter
`q.1.n + |enc q.2| + q.1.gates.length.size + 1` of the compiled `SYM ∘ AND` circuit. -/
private theorem acc0_pipe_poly_bound (d : ℕ) {m : ℕ} (hm : 0 < m) (n ℓ : ℕ)
    (c : Σ n', Circuit Unbounded.extSignature n' 1) (hn : c.1 = n) (hℓ_le_n : ℓ ≤ n)
    (hlog_c' : Nat.log 2 ((orExpand ℓ c).1 + (orExpand ℓ c).2.size) + 2 ≤ 8 * (ℓ + 1)) :
    let K := 5 ^ ((d + 2) * (m + 2)) + 1
    let B₀c := 24 * ((m + 1) ^ 2 + 2)
    let P_const := 40 + (d + 2) * (m + 2) * (2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) +
      ((2 * B₀c) ^ K + 1) + 4
    let q := compileSymAndFixed (d + 2) m (orExpand ℓ c)
    q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1 ≤
      P_const * (n + 1) ^ K := by
  intro K B₀c P_const q
  set c' := orExpand ℓ c
  have hbounds := compileSymAndFixed_bounds (d + 2) hm c'
  dsimp only at hbounds
  obtain ⟨hqn, _, hqgates, hqth, hqmods_len, hqmods_bound⟩ := hbounds
  set K0 := 5 ^ ((d + 2) * (m + 2))
  have hK_eq : K = K0 + 1 := rfl
  have hK2 : 2 ≤ K := by
    have : 1 ≤ K0 := Nat.one_le_pow _ _ (by decide)
    omega
  set ℓ' := Nat.log 2 (c'.1 + c'.2.size) + 1
  set B₀ := 3 * ((m + 1) ^ 2 + ℓ' + 1)
  have hℓ'_le : ℓ' + 1 ≤ 8 * (n + 1) := hlog_c'.trans (Nat.mul_le_mul_left 8 (by omega))
  have hB₀_le : B₀ ≤ B₀c * (n + 1) := by
    dsimp only [B₀, B₀c]
    nlinarith only [hℓ'_le]
  have hsize_pow2 : ∀ a b : ℕ, a ≤ 2 ^ b → a.size ≤ b + 1 := fun a b hab =>
    Nat.size_le.2 (hab.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b)))
  have h1_nK : 1 ≤ (n + 1) ^ K := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hn1_K : n + 1 ≤ (n + 1) ^ K := Nat.le_self_pow (by omega) (n + 1)
  have h2B₀_K0 : (2 * B₀) ^ K0 ≤ (2 * B₀c) ^ K * (n + 1) ^ K0 :=
    ((Nat.pow_le_pow_left (by nlinarith only [hB₀_le] : 2 * B₀ ≤ 2 * B₀c * (n + 1)) K0).trans_eq
      (Nat.mul_pow _ _ _)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by dsimp only [B₀c]; positivity) (by omega)))
  have hgates_sz : q.1.gates.length.size ≤ ((2 * B₀c) ^ K + 1) * (n + 1) ^ K := by
    have h1 := hsize_pow2 _ _ hqgates
    have h2 : (n + 1) ^ K0 ≤ (n + 1) ^ K :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h3 : (2 * B₀) ^ K0 ≤ (2 * B₀c) ^ K * (n + 1) ^ K :=
      h2B₀_K0.trans (Nat.mul_le_mul_left _ h2)
    nlinarith only [h1, h3, h1_nK]
  have hth_sz : q.2.thresh.size ≤ 19 * (n + 1) ^ K := by
    have h1 := hsize_pow2 _ _ hqth.le
    nlinarith only [h1, hℓ'_le, hn1_K, h1_nK]
  have hmods_sz : ∀ M₀ ∈ q.2.mods,
      M₀.size ≤ ((B₀c + 2) * (2 * B₀c) ^ K + 1) * (n + 1) ^ K := by
    intro M₀ hM₀
    have h1 := hsize_pow2 _ _ (hqmods_bound M₀ hM₀)
    have hB2 : B₀ + 2 ≤ (B₀c + 2) * (n + 1) := by nlinarith only [hB₀_le]
    have hpowK : (n + 1) ^ K0 * (n + 1) = (n + 1) ^ K := by rw [hK_eq, pow_succ]
    have hmul : (B₀ + 2) * (2 * B₀) ^ K0 ≤ (B₀c + 2) * (2 * B₀c) ^ K * (n + 1) ^ K := by
      calc (B₀ + 2) * (2 * B₀) ^ K0
          ≤ ((B₀c + 2) * (n + 1)) * ((2 * B₀c) ^ K * (n + 1) ^ K0) :=
            Nat.mul_le_mul hB2 h2B₀_K0
        _ = (B₀c + 2) * (2 * B₀c) ^ K * ((n + 1) ^ K0 * (n + 1)) := by ring
        _ = (B₀c + 2) * (2 * B₀c) ^ K * (n + 1) ^ K := by rw [hpowK]
    nlinarith only [h1, hmul, h1_nK]
  have hout_len : (encSymOutParam q.2).length ≤
      (38 + (d + 2) * (m + 2) * (2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) + 1) *
        (n + 1) ^ K := by
    have h1 := length_encSymOutParam_le q.2 hmods_sz
    have h2 : q.2.mods.length *
        (2 * (((B₀c + 2) * (2 * B₀c) ^ K + 1) * (n + 1) ^ K) + 1) ≤
        (d + 2) * (m + 2) *
          (2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) * (n + 1) ^ K := by
      have hinner : 2 * (((B₀c + 2) * (2 * B₀c) ^ K + 1) * (n + 1) ^ K) + 1 ≤
          (2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) * (n + 1) ^ K := by
        nlinarith only [h1_nK]
      calc _ ≤ (d + 2) * (m + 2) *
            ((2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) * (n + 1) ^ K) :=
            Nat.mul_le_mul hqmods_len hinner
        _ = _ := by ring
    nlinarith only [h1, hth_sz, h2, h1_nK]
  have hqn_le : q.1.n ≤ (n + 1) ^ K := by
    rw [hqn, orExpand_n, hn]; omega
  dsimp only [P_const]
  nlinarith only [hqn_le, hout_len, hgates_sz, h1_nK]

/-- An upper bound `x ≤ a * 2 ^ ℓ` raised to the `k`-th power. -/
private theorem pow_le_pow_mul_two_pow {x a ℓ : ℕ} (h : x ≤ a * 2 ^ ℓ) (k : ℕ) :
    x ^ k ≤ a ^ k * 2 ^ (k * ℓ) :=
  (Nat.pow_le_pow_left h k).trans_eq (by rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm ℓ])

/-- Pure arithmetic integer bounds on every pipeline stage for a guarded input. -/
private theorem acc0_guarded_nat_bounds (K dg dr C_exp C_comp C_sat c_expLen c_compLen : ℕ)
    (hK2 : 2 ≤ K) (n ℓ L s c'n c's len_c' len_x : ℕ)
    (hL_le : L ≤ 2 ^ (ℓ + 1)) (hn_le_L : n ≤ L) (hs_le_L : s ≤ L)
    (hc'n : c'n = n - ℓ) (hc's : c's = 2 ^ ℓ * s + 3)
    (hexpLen : len_c' ≤ c_expLen * ((L + (L + 1) ^ dr + (L + 2 ^ ℓ + ℓ + 1) ^ C_exp) + 1))
    (hcompLen : len_x ≤ c_compLen *
      ((L + (L + 1) ^ dr + (L + 2 ^ ℓ + ℓ + 1) ^ C_exp) +
        (len_c' + 1) ^ C_comp * 2 ^ (C_comp * (Nat.log 2 (c'n + c's) + 2) ^ K) + 1)) :
    let E_exp := C_exp * (dr + 1) + dr + 10
    let E_comp := C_comp * (C_exp + dr + 1) + C_comp * 8 ^ K + 10
    let E_all := (C_sat + 1) * (E_comp + E_exp + dg + dr + 10)
    let C_raw := 4 * (c_compLen + 2) *
      ((2 * c_expLen + 2) * (6 ^ (C_exp + dr + dg + 2) + 2)) ^ (C_comp + 2) + 4
    let T_e := L + (L + 1) ^ dr + (L + 2 ^ ℓ + ℓ + 1) ^ C_exp
    let T_c := (len_c' + 1) ^ C_comp * 2 ^ (C_comp * (Nat.log 2 (c'n + c's) + 2) ^ K)
    Nat.log 2 (c'n + c's) + 2 ≤ 8 * (ℓ + 1) ∧
      (L + 1) ^ dg ≤ C_raw * 2 ^ (E_all * (ℓ + 1) ^ K) ∧
      T_e ≤ C_raw * 2 ^ ((E_comp + E_exp) * (ℓ + 1) ^ K) ∧
      T_c ≤ C_raw * 2 ^ ((E_comp + E_exp) * (ℓ + 1) ^ K) ∧
      len_x + 1 ≤ C_raw * 2 ^ ((E_comp + E_exp) * (ℓ + 1) ^ K) := by
  intro E_exp E_comp E_all C_raw T_e T_c
  have h2ℓ : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
  have h2ℓ_pos : 1 ≤ 2 ^ ℓ := Nat.one_le_pow _ _ (by decide)
  have hℓ_le_2ℓ : ℓ ≤ 2 ^ ℓ := Nat.lt_two_pow_self.le
  have hL1_le : L + 1 ≤ 3 * 2 ^ ℓ := by omega
  have hlog_c' : Nat.log 2 (c'n + c's) + 2 ≤ 8 * (ℓ + 1) := by
    have h4 : 2 ^ (2 * ℓ + 4) = 16 * (2 ^ ℓ * 2 ^ ℓ) := by ring
    have h5 : 2 ^ ℓ * s ≤ 2 ^ ℓ * (2 * 2 ^ ℓ) := Nat.mul_le_mul_left _ (by omega)
    have hlog : Nat.log 2 (c'n + c's) < 2 * ℓ + 4 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).2 (by
        rw [h4, hc's]; nlinarith only [h5, h2ℓ_pos, (by omega : c'n ≤ 2 * 2 ^ ℓ)])
    omega
  have h2le : ∀ k ≤ C_exp + dr + 1, 2 ^ (k * ℓ) ≤ 2 ^ ((C_exp + dr + 1) * ℓ) := fun k hk =>
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right ℓ hk)
  have h6le : ∀ a k, a ≤ 6 → k ≤ C_exp + dr → a ^ k ≤ 6 ^ (C_exp + dr) := fun a k ha hk =>
    (Nat.pow_le_pow_left ha k).trans (Nat.pow_le_pow_right (by decide) hk)
  have hT_exp_le : T_e ≤ 6 ^ (C_exp + dr + 1) * 2 ^ ((C_exp + dr + 1) * ℓ) := by
    have hA1 : L ≤ 2 * (6 ^ (C_exp + dr) * 2 ^ ((C_exp + dr + 1) * ℓ)) :=
      (by rw [Nat.one_mul]; omega : L ≤ 2 * 2 ^ (1 * ℓ)).trans (Nat.mul_le_mul_left 2
        ((h2le 1 (by omega)).trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by decide)))))
    have hA2 := (pow_le_pow_mul_two_pow hL1_le dr).trans
      (Nat.mul_le_mul (h6le 3 dr (by decide) (by omega)) (h2le dr (by omega)))
    have hA3 := (pow_le_pow_mul_two_pow (by omega : L + 2 ^ ℓ + ℓ + 1 ≤ 5 * 2 ^ ℓ) C_exp).trans
      (Nat.mul_le_mul (h6le 5 C_exp (by decide) (by omega)) (h2le C_exp (by omega)))
    dsimp only [T_e]
    rw [pow_succ', Nat.mul_assoc]
    omega
  have hlen_c' : len_c' + 1 ≤
      (2 * c_expLen + 2) * 6 ^ (C_exp + dr + 1) * 2 ^ ((C_exp + dr + 1) * ℓ) := by
    have h1 : 1 ≤ 6 ^ (C_exp + dr + 1) * 2 ^ ((C_exp + dr + 1) * ℓ) :=
      Nat.mul_pos (Nat.one_le_pow _ _ (by decide)) (Nat.two_pow_pos _)
    have hle1 :=
      hexpLen.trans (Nat.mul_le_mul_left c_expLen (Nat.add_le_add_right hT_exp_le 1))
    rw [Nat.mul_assoc]
    nlinarith only [hle1, h1]
  have hℓ_powK : ℓ ≤ (ℓ + 1) ^ K :=
    (Nat.le_succ ℓ).trans (Nat.le_self_pow (by omega) (ℓ + 1))
  have hT_comp_le : T_c ≤
      ((2 * c_expLen + 2) * 6 ^ (C_exp + dr + 1)) ^ C_comp *
        2 ^ ((C_comp * (C_exp + dr + 1) + C_comp * 8 ^ K) * (ℓ + 1) ^ K) := by
    have hlog_pow : (Nat.log 2 (c'n + c's) + 2) ^ K ≤ 8 ^ K * (ℓ + 1) ^ K :=
      (Nat.pow_le_pow_left hlog_c' K).trans_eq (Nat.mul_pow _ _ _)
    have hexp_le : C_comp * ((C_exp + dr + 1) * ℓ) +
        C_comp * (Nat.log 2 (c'n + c's) + 2) ^ K ≤
        (C_comp * (C_exp + dr + 1) + C_comp * 8 ^ K) * (ℓ + 1) ^ K := by
      nlinarith only [Nat.mul_le_mul_left (C_comp * (C_exp + dr + 1)) hℓ_powK,
        Nat.mul_le_mul_left C_comp hlog_pow]
    dsimp only [T_c]
    calc _ ≤ ((2 * c_expLen + 2) * 6 ^ (C_exp + dr + 1)) ^ C_comp *
          2 ^ (C_comp * ((C_exp + dr + 1) * ℓ) + C_comp * (Nat.log 2 (c'n + c's) + 2) ^ K) := by
          rw [pow_add 2 (C_comp * ((C_exp + dr + 1) * ℓ)), ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (pow_le_pow_mul_two_pow hlen_c' C_comp)
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp_le)
  have hE_exp_ge : (C_exp + dr + 1) * ℓ ≤ (E_comp + E_exp) * (ℓ + 1) ^ K := by
    have hA : C_exp + dr + 1 ≤ E_comp + E_exp := by
      dsimp only [E_comp, E_exp]
      have hce : C_exp ≤ C_exp * (dr + 1) := Nat.le_mul_of_pos_right C_exp (Nat.succ_pos dr)
      omega
    exact Nat.mul_le_mul hA hℓ_powK
  have hE_comp_ge : (C_comp * (C_exp + dr + 1) + C_comp * 8 ^ K) * (ℓ + 1) ^ K ≤
      (E_comp + E_exp) * (ℓ + 1) ^ K := by
    refine Nat.mul_le_mul_right _ ?_
    dsimp only [E_comp, E_exp]; omega
  set base := (2 * c_expLen + 2) * (6 ^ (C_exp + dr + dg + 2) + 2)
  have hbase_pos : 1 ≤ base := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have h6_base : ∀ k ≤ C_exp + dr + dg + 2, 6 ^ k ≤ 6 ^ (C_exp + dr + dg + 2) + 2 := fun k hk =>
    (Nat.pow_le_pow_right (by decide) hk).trans (Nat.le_add_right _ 2)
  have hbase_self : base ≤ base ^ (C_comp + 2) := Nat.le_self_pow (by omega) base
  have hpow_le : ((2 * c_expLen + 2) * 6 ^ (C_exp + dr + 1)) ^ C_comp ≤ base ^ (C_comp + 2) :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (h6_base _ (by omega))) C_comp).trans
      (Nat.pow_le_pow_right hbase_pos (by omega))
  have h6_le_pow : 6 ^ (C_exp + dr + 1) ≤ base ^ (C_comp + 2) :=
    ((h6_base _ (by omega)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))).trans hbase_self
  have hC_raw_eq : C_raw = 4 * (c_compLen + 2) * base ^ (C_comp + 2) + 4 := rfl
  have hpow_le_Craw : base ^ (C_comp + 2) ≤ C_raw := by
    rw [hC_raw_eq]
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right _ 4)
  have hguard_le : (L + 1) ^ dg ≤ C_raw * 2 ^ (E_all * (ℓ + 1) ^ K) := by
    have h2 : 3 ^ dg ≤ C_raw := (Nat.pow_le_pow_left (by decide : 3 ≤ 6) dg).trans
      ((h6_base dg (by omega)).trans
        ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (hbase_self.trans hpow_le_Craw)))
    have h3 : dg * ℓ ≤ E_all * (ℓ + 1) ^ K :=
      Nat.mul_le_mul (by
        dsimp only [E_all]
        exact (by omega : dg ≤ E_comp + E_exp + dg + dr + 10).trans
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos C_sat))) hℓ_powK
    exact (pow_le_pow_mul_two_pow hL1_le dg).trans
      (Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by decide) h3))
  set W := 2 ^ ((E_comp + E_exp) * (ℓ + 1) ^ K)
  have hT1' : T_e ≤ base ^ (C_comp + 2) * W :=
    hT_exp_le.trans (Nat.mul_le_mul h6_le_pow (Nat.pow_le_pow_right (by decide) hE_exp_ge))
  have hT2' : T_c ≤ base ^ (C_comp + 2) * W :=
    hT_comp_le.trans (Nat.mul_le_mul hpow_le (Nat.pow_le_pow_right (by decide) hE_comp_ge))
  have hlen_x : len_x + 1 ≤ C_raw * W := by
    have h1_BW : 1 ≤ base ^ (C_comp + 2) * W :=
      Nat.mul_pos (Nat.one_le_pow _ _ hbase_pos) (Nat.two_pow_pos _)
    have hle := hcompLen.trans (Nat.mul_le_mul_left c_compLen
      (by omega : T_e + T_c + 1 ≤ 3 * (base ^ (C_comp + 2) * W)))
    rw [hC_raw_eq]
    nlinarith only [hle, h1_BW]
  exact ⟨hlog_c', hguard_le, hT1'.trans (Nat.mul_le_mul_right _ hpow_le_Craw),
    hT2'.trans (Nat.mul_le_mul_right _ hpow_le_Craw), hlen_x⟩

/-- Pure real-analytic combination of the guarded pipeline stage bounds into the Williams
`O(2 ^ (n - (1 / 2) * n ^ (1 / p_root)))` envelope. -/
private theorem acc0_guarded_real_combine (K p_root C_sat E_sum E_all C_raw P_const : ℕ)
    (hK_pos : 0 < K) (hp_pos : 0 < p_root) (hp2 : 2 ≤ p_root) (h2K_le : 2 * K ≤ p_root)
    (hE_le : E_sum ≤ E_all) (hE_sat_le : C_sat * E_sum ≤ E_all) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ (n T_g T_e T_c len_x P_term : ℕ),
      let ℓ := Nat.nthRoot p_root n
      T_g ≤ C_raw * 2 ^ (E_all * (ℓ + 1) ^ K) →
      T_e ≤ C_raw * 2 ^ (E_sum * (ℓ + 1) ^ K) →
      T_c ≤ C_raw * 2 ^ (E_sum * (ℓ + 1) ^ K) →
      len_x + 1 ≤ C_raw * 2 ^ (E_sum * (ℓ + 1) ^ K) →
      P_term ≤ P_const * (n + 1) ^ K →
      ((T_g + (T_e + T_c + (2 ^ (n - ℓ) + (len_x + 1) ^ C_sat) * P_term ^ C_sat) : ℕ) : ℝ) ≤
        M * (2 : ℝ) ^ ((n : ℝ) - (1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) + M := by
  let D_poly : ℕ := K * C_sat + 1
  obtain ⟨M_poly, hM_poly_pos, hM_poly⟩ := pow_le_mul_two_rpow_half_rpow p_root D_poly hp_pos
  let A_real : ℝ := (E_all : ℝ) * (2 : ℝ) ^ K + 1
  let B_real : ℝ := 2 * (E_all : ℝ) * (2 : ℝ) ^ K + 10
  obtain ⟨M_sub, hM_sub_pos, hM_sub⟩ :=
    two_rpow_sqrt_le_mul_two_rpow_sub A_real B_real (by positivity) p_root hp2
  let M_real : ℝ := 3 * (C_raw : ℝ) * M_sub +
      (P_const : ℝ) ^ C_sat * (2 * M_poly + (C_raw : ℝ) ^ C_sat * M_poly * M_sub) + 2
  obtain ⟨M, hM⟩ := exists_nat_ge M_real
  have hM2 : 2 ≤ M := by
    have hnn : (0 : ℝ) ≤ 3 * (C_raw : ℝ) * M_sub +
        (P_const : ℝ) ^ C_sat * (2 * M_poly + (C_raw : ℝ) ^ C_sat * M_poly * M_sub) := by
      positivity
    have hle : (2 : ℝ) ≤ (M : ℝ) := by dsimp only [M_real] at hM; linarith
    exact_mod_cast hle
  refine ⟨M, hM2, fun n T_g T_e T_c len_x P_term hguard_le hT1_le hT2_le hlen_x hP_le => ?_⟩
  set ℓ := Nat.nthRoot p_root n
  have hℓ_le_n : ℓ ≤ n := nthRoot_le_self hp_pos n
  set target : ℝ := (2 : ℝ) ^ ((n : ℝ) - (1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹))
  have htarget_pos : 0 < target := Real.rpow_pos_of_pos (by norm_num) _
  have hpow2_ell : ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) *
      (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) ≤ M_sub * target := by
    have hℓ_rpow : (ℓ : ℝ) ≤ (n : ℝ) ^ ((p_root : ℝ)⁻¹) :=
      Nat.cast_nthRoot_le_rpow p_root n hp_pos.ne'
    have hℓ1_pow : ((ℓ : ℝ) + 1) ^ K ≤
        (2 : ℝ) ^ K * (((n : ℝ) ^ ((p_root : ℝ)⁻¹)) ^ K + 1) := by
      have h1 : ((ℓ : ℝ) + 1) ^ K ≤ ((n : ℝ) ^ ((p_root : ℝ)⁻¹) + 1) ^ K :=
        pow_le_pow_left₀ (by positivity) (by linarith) K
      exact h1.trans (add_one_pow_le_two_pow_mul _ K (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    have hrpow_K : ((n : ℝ) ^ ((p_root : ℝ)⁻¹)) ^ K ≤ (n : ℝ) ^ (1 / 2 : ℝ) + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      have hpos : (0 : ℝ) < (p_root : ℝ)⁻¹ * (K : ℝ) := by positivity
      have hle : (p_root : ℝ)⁻¹ * (K : ℝ) ≤ 1 / 2 := by
        rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hcast : (2 : ℝ) * (K : ℝ) ≤ (p_root : ℝ) := by exact_mod_cast h2K_le
        linarith
      exact nat_rpow_le_rpow_add_one n hpos hle
    have hroot_half : (n : ℝ) ^ ((p_root : ℝ)⁻¹) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + 1 := by
      have hp_inv : (p_root : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hp2)
      exact nat_rpow_le_rpow_add_one n (by positivity) hp_inv
    have hexp_bound : ((E_all * (ℓ + 1) ^ K : ℕ) : ℝ) +
        (1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹) ≤
        A_real * (n : ℝ) ^ (1 / 2 : ℝ) + B_real := by
      push_cast
      have hE0 : (0 : ℝ) ≤ (E_all : ℝ) := Nat.cast_nonneg E_all
      have h2K0 : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
      have hn_half : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hcomb : ((ℓ : ℝ) + 1) ^ K ≤ (2 : ℝ) ^ K * ((n : ℝ) ^ (1 / 2 : ℝ) + 2) := by
        nlinarith only [hℓ1_pow, hrpow_K, h2K0]
      have hmul := mul_le_mul_of_nonneg_left hcomb hE0
      dsimp only [A_real, B_real]
      nlinarith only [hmul, hroot_half, hn_half]
    calc ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) *
          (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹))
        = (2 : ℝ) ^ (((E_all * (ℓ + 1) ^ K : ℕ) : ℝ) +
            (1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (A_real * (n : ℝ) ^ (1 / 2 : ℝ) + B_real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_bound
      _ ≤ M_sub * target := hM_sub n
  have hpow2_ell_alone : ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) ≤ M_sub * target := by
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hpos : (0 : ℝ) ≤ ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) := by positivity
    nlinarith only [hpow2_ell, hge1, hpos]
  have hpoly_real : (((n + 1) ^ (K * C_sat) : ℕ) : ℝ) ≤
      M_poly * (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) := by
    have h1 : (((n + 1) ^ (K * C_sat) : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ D_poly := by
      push_cast
      have hge : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      exact pow_le_pow_right₀ hge (by dsimp only [D_poly]; omega)
    exact h1.trans (hM_poly n)
  have h2sub_real : ((2 ^ (n - ℓ) : ℕ) : ℝ) ≤
      2 * (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹)) := by
    have hlt := Real.rpow_lt_natCast_nthRoot_add_one p_root n hp_pos.ne'
    have hsub : ((n - ℓ : ℕ) : ℝ) ≤ (n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹) + 1 := by
      rw [Nat.cast_sub hℓ_le_n]
      linarith
    calc ((2 ^ (n - ℓ) : ℕ) : ℝ) = (2 : ℝ) ^ ((n - ℓ : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsub
      _ = 2 * (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, mul_comm]
  have hE_sat : C_sat * (E_sum * (ℓ + 1) ^ K) ≤ E_all * (ℓ + 1) ^ K := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hE_sat_le
  have hterm : ∀ v E : ℕ, E ≤ E_all → v ≤ C_raw * 2 ^ (E * (ℓ + 1) ^ K) →
      (v : ℝ) ≤ (C_raw : ℝ) * M_sub * target := fun v E hE hv => by
    have hcast : (v : ℝ) ≤ (C_raw : ℝ) * ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) := by
      exact_mod_cast hv.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hE)))
    nlinarith only [hcast, hpow2_ell_alone, (Nat.cast_nonneg C_raw : (0 : ℝ) ≤ C_raw)]
  set T_s : ℕ := (2 ^ (n - ℓ) + (len_x + 1) ^ C_sat) * P_term ^ C_sat
  have hterm_sat : (T_s : ℝ) ≤
      ((P_const : ℝ) ^ C_sat * (2 * M_poly + (C_raw : ℝ) ^ C_sat * M_poly * M_sub)) * target := by
    have hP_pow : P_term ^ C_sat ≤ P_const ^ C_sat * (n + 1) ^ (K * C_sat) := by
      calc _ ≤ (P_const * (n + 1) ^ K) ^ C_sat := Nat.pow_le_pow_left hP_le C_sat
        _ = P_const ^ C_sat * ((n + 1) ^ K) ^ C_sat := Nat.mul_pow _ _ _
        _ = P_const ^ C_sat * (n + 1) ^ (K * C_sat) := by rw [← pow_mul]
    have hx_pow : (len_x + 1) ^ C_sat ≤ C_raw ^ C_sat * 2 ^ (E_all * (ℓ + 1) ^ K) := by
      calc _ ≤ (C_raw * 2 ^ (E_sum * (ℓ + 1) ^ K)) ^ C_sat := Nat.pow_le_pow_left hlen_x C_sat
        _ = C_raw ^ C_sat * (2 ^ (E_sum * (ℓ + 1) ^ K)) ^ C_sat := Nat.mul_pow _ _ _
        _ = C_raw ^ C_sat * 2 ^ (C_sat * (E_sum * (ℓ + 1) ^ K)) := by
            rw [← pow_mul, Nat.mul_comm _ C_sat]
        _ ≤ C_raw ^ C_sat * 2 ^ (E_all * (ℓ + 1) ^ K) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hE_sat)
    have hnat : T_s ≤ (2 ^ (n - ℓ) + C_raw ^ C_sat * 2 ^ (E_all * (ℓ + 1) ^ K)) *
        (P_const ^ C_sat * (n + 1) ^ (K * C_sat)) :=
      Nat.mul_le_mul (Nat.add_le_add_left hx_pow _) hP_pow
    have hcast : (T_s : ℝ) ≤
        (((2 ^ (n - ℓ) : ℕ) : ℝ) +
          (C_raw : ℝ) ^ C_sat * ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ)) *
          ((P_const : ℝ) ^ C_sat * (((n + 1) ^ (K * C_sat) : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    have hpart1 : ((2 ^ (n - ℓ) : ℕ) : ℝ) * (((n + 1) ^ (K * C_sat) : ℕ) : ℝ) ≤
        2 * M_poly * target := by
      have hadd : (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹)) *
          (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹)) = target := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring
      calc _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((p_root : ℝ)⁻¹))) *
            (M_poly * (2 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ) ^ ((p_root : ℝ)⁻¹))) :=
          mul_le_mul h2sub_real hpoly_real (by positivity) (by positivity)
        _ = 2 * M_poly * target := by rw [← hadd]; ring
    have hpart2 : ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ) * (((n + 1) ^ (K * C_sat) : ℕ) : ℝ) ≤
        M_poly * M_sub * target :=
      (mul_le_mul_of_nonneg_left hpoly_real
        (by positivity : (0 : ℝ) ≤ ((2 ^ (E_all * (ℓ + 1) ^ K) : ℕ) : ℝ))).trans
        (by nlinarith only [hpow2_ell, hM_poly_pos])
    have hP0 : (0 : ℝ) ≤ (P_const : ℝ) ^ C_sat := by positivity
    linarith only [hcast, mul_le_mul_of_nonneg_left hpart1 hP0, mul_le_mul_of_nonneg_left hpart2
      (mul_nonneg hP0 (by positivity : (0 : ℝ) ≤ (C_raw : ℝ) ^ C_sat))]
  have hcoeff_le : 3 * (C_raw : ℝ) * M_sub +
      (P_const : ℝ) ^ C_sat * (2 * M_poly + (C_raw : ℝ) ^ C_sat * M_poly * M_sub) ≤ M_real :=
    le_add_of_nonneg_right zero_le_two
  have hM_nonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsum_cast : ((T_g + (T_e + T_c + T_s) : ℕ) : ℝ) =
      (T_g : ℝ) + (T_e : ℝ) + (T_c : ℝ) + (T_s : ℝ) := by push_cast; ring
  nlinarith only [hsum_cast, hterm T_g E_all le_rfl hguard_le, hterm T_e E_sum hE_le hT1_le,
    hterm T_c E_sum hE_le hT2_le, hterm_sat, hcoeff_le, hM, htarget_pos, hM_nonneg]

/-- Analytical upper bound on the combined pipeline cost for guarded `ACC⁰[m]` inputs. -/
private theorem acc0_guarded_real_bound (d : ℕ) {m : ℕ} (hm : 0 < m)
    (dg dr C_exp C_comp C_sat c_expLen c_compLen : ℕ) :
    let K := 5 ^ ((d + 2) * (m + 2)) + 1
    let p_root := 2 * K + 2
    let q_root := 4 * K + 4
    (∀ c : Σ n, Circuit Unbounded.extSignature n 1,
      (Unbounded.encExtCircuit 1 (orExpand (Nat.nthRoot p_root c.1) c)).length ≤
        c_expLen * (((Unbounded.encExtCircuit 1 c).length +
          ((Unbounded.encExtCircuit 1 c).length + 1) ^ dr +
          ((Unbounded.encExtCircuit 1 c).length +
            2 ^ min (Nat.nthRoot p_root c.1) c.1 +
            Nat.nthRoot p_root c.1 + 1) ^ C_exp) + 1)) →
    (∀ c : Σ n, Circuit Unbounded.extSignature n 1,
      let c' := orExpand (Nat.nthRoot p_root c.1) c
      let T_e := (Unbounded.encExtCircuit 1 c).length +
        ((Unbounded.encExtCircuit 1 c).length + 1) ^ dr +
        ((Unbounded.encExtCircuit 1 c).length +
          2 ^ min (Nat.nthRoot p_root c.1) c.1 + Nat.nthRoot p_root c.1 + 1) ^ C_exp
      let T_c := ((Unbounded.encExtCircuit 1 c').length + 1) ^ C_comp *
        2 ^ (C_comp * (Nat.log 2 (c'.1 + c'.2.size) + 2) ^ K)
      (encPair encSymAndInstance encSymOutParam (compileSymAndFixed (d + 2) m c')).length ≤
        c_compLen * (T_e + T_c + 1)) →
    ∃ M : ℕ, 2 ≤ M ∧ ∀ c : Σ n, Circuit Unbounded.extSignature n 1,
      acc0Guard d q_root c = true →
      let c' := orExpand (Nat.nthRoot p_root c.1) c
      let q := compileSymAndFixed (d + 2) m c'
      let T_e := (Unbounded.encExtCircuit 1 c).length +
        ((Unbounded.encExtCircuit 1 c).length + 1) ^ dr +
        ((Unbounded.encExtCircuit 1 c).length +
          2 ^ min (Nat.nthRoot p_root c.1) c.1 + Nat.nthRoot p_root c.1 + 1) ^ C_exp
      let T_c := ((Unbounded.encExtCircuit 1 c').length + 1) ^ C_comp *
        2 ^ (C_comp * (Nat.log 2 (c'.1 + c'.2.size) + 2) ^ K)
      let T_s := (2 ^ q.1.n + ((encSymAndInstance q.1).length + 1) ^ C_sat) *
        (q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1) ^ C_sat
      ((((Unbounded.encExtCircuit 1 c).length + 1) ^ dg + (T_e + T_c + T_s) : ℕ) : ℝ) ≤
        M * (2 : ℝ) ^ ((c.1 : ℝ) - (1 / 2 : ℝ) * (c.1 : ℝ) ^ ((p_root : ℝ)⁻¹)) + M := by
  intro K p_root q_root hexpLen hcompLen
  have hK2 : 2 ≤ K := by
    have : 1 ≤ 5 ^ ((d + 2) * (m + 2)) := Nat.one_le_pow _ _ (by decide)
    dsimp only [K]; omega
  have hK_pos : 0 < K := by omega
  have hp_pos : 0 < p_root := by dsimp only [p_root]; omega
  have hp2 : 2 ≤ p_root := by dsimp only [p_root]; omega
  have h2K_le : 2 * K ≤ p_root := by dsimp only [p_root]; omega
  have hq_ge : p_root ≤ q_root := by dsimp only [p_root, q_root]; omega
  let B₀c : ℕ := 24 * ((m + 1) ^ 2 + 2)
  let P_const : ℕ := 40 + (d + 2) * (m + 2) * (2 * ((B₀c + 2) * (2 * B₀c) ^ K + 1) + 1) +
    ((2 * B₀c) ^ K + 1) + 4
  let E_exp : ℕ := C_exp * (dr + 1) + dr + 10
  let E_comp : ℕ := C_comp * (C_exp + dr + 1) + C_comp * 8 ^ K + 10
  let E_all : ℕ := (C_sat + 1) * (E_comp + E_exp + dg + dr + 10)
  let C_raw : ℕ := 4 * (c_compLen + 2) *
      ((2 * c_expLen + 2) * (6 ^ (C_exp + dr + dg + 2) + 2)) ^ (C_comp + 2) + 4
  have hE_sum_le : E_comp + E_exp ≤ E_comp + E_exp + dg + dr + 10 := by omega
  obtain ⟨M, hM2, hcomb⟩ := acc0_guarded_real_combine K p_root C_sat (E_comp + E_exp) E_all
    C_raw P_const hK_pos hp_pos hp2 h2K_le
    (hE_sum_le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos C_sat)))
    (Nat.mul_le_mul (Nat.le_succ C_sat) hE_sum_le)
  refine ⟨M, hM2, fun c hguard => ?_⟩
  obtain ⟨_, hL_bound⟩ := (acc0Guard_eq_true_iff d q_root c).1 hguard
  have hℓ_le_n : Nat.nthRoot p_root c.1 ≤ c.1 := nthRoot_le_self hp_pos c.1
  have hmin_ℓ : min (Nat.nthRoot p_root c.1) c.1 = Nat.nthRoot p_root c.1 :=
    Nat.min_eq_left hℓ_le_n
  have hq_le_ℓ : Nat.nthRoot q_root c.1 ≤ Nat.nthRoot p_root c.1 := nthRoot_anti hp_pos hq_ge c.1
  have hL_le : (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot p_root c.1 + 1) :=
    hL_bound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hq_le_ℓ 1))
  have hn_le_L : c.1 ≤ (Unbounded.encExtCircuit 1 c).length :=
    Circuit.le_length_encCircuit (σ := Unbounded.extSignature) Unbounded.encExtOp c
  have hs_le_L : c.2.size ≤ (Unbounded.encExtCircuit 1 c).length :=
    Circuit.size_le_length_encCircuit (σ := Unbounded.extSignature) Unbounded.encExtOp c
  have hc'n : (orExpand (Nat.nthRoot p_root c.1) c).1 = c.1 - Nat.nthRoot p_root c.1 := by
    rw [orExpand_n, hmin_ℓ]
  have hc's : (orExpand (Nat.nthRoot p_root c.1) c).2.size =
      2 ^ Nat.nthRoot p_root c.1 * c.2.size + 3 := by
    rw [orExpand_size, hmin_ℓ]
  have hqn : (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c)).1.n =
      c.1 - Nat.nthRoot p_root c.1 := by
    rw [compileSymAndFixed_n, hc'n]
  have hlen_x_le :
      (encSymAndInstance
        (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c)).1).length ≤
      (encPair encSymAndInstance encSymOutParam
        (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c))).length := by
    rw [length_encPair]; omega
  have hexp_c := hexpLen c
  have hcomp_c := hcompLen c
  dsimp only at hexp_c hcomp_c ⊢
  rw [hmin_ℓ] at hexp_c hcomp_c ⊢
  have hcomp_c' := hlen_x_le.trans hcomp_c
  obtain ⟨hlog_c', hguard_le, hT1_le, hT2_le, hlen_x⟩ :=
    acc0_guarded_nat_bounds K dg dr C_exp C_comp C_sat c_expLen c_compLen hK2 _ _ _ _ _ _ _ _
      hL_le hn_le_L hs_le_L hc'n hc's hexp_c hcomp_c'
  have hP_le : c.1 - Nat.nthRoot p_root c.1 +
      (encSymOutParam
        (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c)).2).length +
      (compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c)).1.gates.length.size +
      1 ≤ P_const * (c.1 + 1) ^ K := by
    rw [← hqn]
    exact acc0_pipe_poly_bound d hm c.1 (Nat.nthRoot p_root c.1) c rfl hℓ_le_n hlog_c'
  rw [hqn]
  exact hcomb c.1 _ _ _ _ _ hguard_le hT1_le hT2_le hlen_x hP_le

/-- Combined resource bound for `acc0Decider`: on guarded inputs (`acc0Guard d q_root c = true`)
both time and space are `O(2 ^ (c.1 - (1 / 2) * c.1 ^ (1 / p_root)))`, and on unguarded inputs
both are polynomial in `|enc c|`. -/
private theorem computableInO_acc0Decider (d : ℕ) {m : ℕ} (hm : 0 < m) :
    let K := 5 ^ ((d + 2) * (m + 2)) + 1
    let p_root := 2 * K + 2
    let q_root := 4 * K + 4
    ∃ (T : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ) (e M : ℕ),
      ComputableInO (acc0Decider d m p_root q_root) (Unbounded.encExtCircuit 1) encBool T T ∧
      (∀ c, acc0Guard d q_root c = true →
        (T c : ℝ) ≤ M * (2 : ℝ) ^ ((c.1 : ℝ) - (1 / 2 : ℝ) * (c.1 : ℝ) ^ ((p_root : ℝ)⁻¹)) + M) ∧
      (∀ c, acc0Guard d q_root c = false →
        (T c : ℝ) ≤ M * ((Unbounded.encExtCircuit 1 c).length + 1 : ℝ) ^ e + M) := by
  set K := 5 ^ ((d + 2) * (m + 2)) + 1
  set p_root := 2 * K + 2
  set q_root := 4 * K + 4
  have hp_pos : 0 < p_root := by omega
  obtain ⟨dg, _, hguardDeg⟩ := (computableInPolyTime_acc0Guard d q_root).exists_degree
  obtain ⟨dr, _, hrootDeg⟩ := (computableInPolyTime_nthRoot_unary p_root hp_pos).exists_degree
  obtain ⟨C_exp, hexp⟩ := computableInO_orExpand
  have hpairRoot : ComputableInO
      (fun c : Σ n, Circuit Unbounded.extSignature n 1 => (c, Nat.nthRoot p_root c.1))
      (Unbounded.encExtCircuit 1) (encPair (Unbounded.encExtCircuit 1) encUnary) _ _ :=
    (ComputableInO.id' (encMid := Unbounded.encExtCircuit 1)).prod hrootDeg.inO
  have hstage1 := hexp.comp hpairRoot
  obtain ⟨c_expLen, hexpLen⟩ := hstage1.length_le
  obtain ⟨C_comp, hcomp⟩ := computableInO_compileSymAndFixed (d + 2) m
  have hstage2 := hcomp.comp hstage1
  obtain ⟨c_compLen, hcompLen⟩ := hstage2.length_le
  obtain ⟨C_sat, hsat⟩ := computableInO_symAndSAT
  have hpipe : ComputableInO (acc0Pipeline d m p_root) (Unbounded.encExtCircuit 1) encBool _ _ :=
    (hsat.comp hstage2).of_enc_eq fun c => congrArg encBool rfl
  have hite := hguardDeg.inO.ite hpipe (ComputableInO.const false)
  have hite_eq : (fun c : Σ n, Circuit Unbounded.extSignature n 1 =>
      if acc0Guard d q_root c then acc0Pipeline d m p_root c else false) =
      acc0Decider d m p_root q_root := rfl
  rw [hite_eq] at hite
  let T_exp : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ := fun c =>
    (Unbounded.encExtCircuit 1 c).length + ((Unbounded.encExtCircuit 1 c).length + 1) ^ dr +
      ((Unbounded.encExtCircuit 1 c).length + 2 ^ min (Nat.nthRoot p_root c.1) c.1 +
        Nat.nthRoot p_root c.1 + 1) ^ C_exp
  let T_comp : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ := fun c =>
    let c' := orExpand (Nat.nthRoot p_root c.1) c
    ((Unbounded.encExtCircuit 1 c').length + 1) ^ C_comp *
      2 ^ (C_comp * (Nat.log 2 (c'.1 + c'.2.size) + 2) ^ K)
  let T_sat : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ := fun c =>
    let q := compileSymAndFixed (d + 2) m (orExpand (Nat.nthRoot p_root c.1) c)
    (2 ^ q.1.n + ((encSymAndInstance q.1).length + 1) ^ C_sat) *
      (q.1.n + (encSymOutParam q.2).length + q.1.gates.length.size + 1) ^ C_sat
  let T : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ := fun c =>
    ((Unbounded.encExtCircuit 1 c).length + 1) ^ dg +
      if acc0Guard d q_root c then T_exp c + T_comp c + T_sat c
      else (Unbounded.encExtCircuit 1 c).length
  have hT_machine : ComputableInO (acc0Decider d m p_root q_root)
      (Unbounded.encExtCircuit 1) encBool T T := by
    refine hite.mono 2 (fun c => ?_) (fun c => ?_)
    all_goals
      dsimp only [T, T_exp, T_comp, T_sat, K, Function.comp_apply]
      split_ifs <;> omega
  obtain ⟨M, hM2, hguarded⟩ := acc0_guarded_real_bound d hm dg dr C_exp C_comp C_sat
    c_expLen c_compLen
    (fun c => by simpa only [Function.comp_apply, p_root, K] using hexpLen c)
    (fun c => by simpa only [Function.comp_apply, p_root, K] using hcompLen c)
  refine ⟨T, dg + 1, M, hT_machine, fun c hguard => ?_, fun c hnoguard => ?_⟩
  · dsimp only [T, T_exp, T_comp, T_sat, p_root, q_root, K] at hguard ⊢
    rw [hguard]; simp only [↓reduceIte]
    exact hguarded c hguard
  · dsimp only [T, q_root, K] at hnoguard ⊢
    rw [hnoguard]; simp only [Bool.false_eq_true, ↓reduceIte]
    set E := (Unbounded.encExtCircuit 1 c).length
    have hge : (1 : ℝ) ≤ (E : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E]
    have h1 : (E : ℝ) + 1 ≤ ((E : ℝ) + 1) ^ (dg + 1) := le_self_pow₀ hge (Nat.succ_ne_zero dg)
    have h2 : ((E : ℝ) + 1) ^ dg ≤ ((E : ℝ) + 1) ^ (dg + 1) := pow_le_pow_right₀ hge dg.le_succ
    have hM2' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    push_cast
    nlinarith only [h1, h2, hM2', hge]

private abbrev acc0RootP (d m : ℕ) : ℕ := 2 * (5 ^ ((d + 2) * (m + 2)) + 1) + 2
private abbrev acc0RootQ (d m : ℕ) : ℕ := 4 * (5 ^ ((d + 2) * (m + 2)) + 1) + 4

private theorem acc0RootParams_spec (d m : ℕ) :
    0 < acc0RootQ d m ∧ (0 : ℝ) < acc0RootQ d m ∧
      (acc0RootQ d m : ℝ)⁻¹ < (acc0RootP d m : ℝ)⁻¹ ∧ (acc0RootP d m : ℝ)⁻¹ < 1 := by
  have hp_pos : (0 : ℝ) < acc0RootP d m := by positivity
  have hq_pos : (0 : ℝ) < acc0RootQ d m := by positivity
  have hp_lt_q : (acc0RootP d m : ℝ) < acc0RootQ d m := by
    exact_mod_cast (by unfold acc0RootP acc0RootQ; omega : acc0RootP d m < acc0RootQ d m)
  have hp_gt1 : (1 : ℝ) < acc0RootP d m := by
    exact_mod_cast (by unfold acc0RootP; omega : 1 < acc0RootP d m)
  exact ⟨by unfold acc0RootQ; omega, hq_pos, inv_strictAnti₀ hp_pos hp_lt_q,
    inv_lt_one_of_one_lt₀ hp_gt1⟩

/-- **Williams's Theorem 4.1 (promise form)** ([Williams2014], Theorem 4.1, Section 4.2, p. 17):
for every constant depth `d` and modulus `m > 0`, there exist `0 < ε < δ < 1` and `c₀ > 0` and a
native multi-tape Turing machine decider `decideSAT` (running in time and space `O(T)`) such that
for every single-output `ACC⁰[m]` circuit `c` of depth at most `d` and encoding length at most
`2 ^ (c.1 ^ ε)`, `decideSAT c` decides satisfiability of `c` in time and space
`O(2 ^ (c.1 - c₀ * c.1 ^ δ))`. -/
theorem exists_acc0SAT_decider (d : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (ε δ c₀ : ℝ), 0 < ε ∧ ε < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∃ (decideSAT : (Σ n, Circuit Unbounded.extSignature n 1) → Bool)
        (T : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ),
        ComputableInO decideSAT (Unbounded.encExtCircuit 1) encBool T T ∧
        (∀ c, c.2.depth ≤ d →
          ((Unbounded.encExtCircuit 1 c).length : ℝ) ≤ (2 : ℝ) ^ ((c.1 : ℝ) ^ ε) →
          (decideSAT c = true ↔
            c ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)))) ∧
        ∃ M : ℕ, ∀ c, c.2.depth ≤ d →
          ((Unbounded.encExtCircuit 1 c).length : ℝ) ≤ (2 : ℝ) ^ ((c.1 : ℝ) ^ ε) →
          (T c : ℝ) ≤ M * (2 : ℝ) ^ ((c.1 : ℝ) - c₀ * (c.1 : ℝ) ^ δ) + M := by
  obtain ⟨hq_nat, hq_pos, hpq_inv, hp_inv_lt1⟩ := acc0RootParams_spec d m
  obtain ⟨T, _, M, hcomp, hT_guard, _⟩ := computableInO_acc0Decider d hm
  refine ⟨(acc0RootQ d m : ℝ)⁻¹, (acc0RootP d m : ℝ)⁻¹, 1 / 2,
    inv_pos.2 hq_pos, hpq_inv, hp_inv_lt1, by norm_num,
    acc0Decider d m (acc0RootP d m) (acc0RootQ d m), T, hcomp,
    fun c hd hsize => ?_, M, fun c hd hsize => ?_⟩
  · have hguard := acc0Guard_of_rpow hq_nat.ne' c hd hsize
    rw [acc0Decider_eq_true_iff d hm (acc0RootP d m) (acc0RootQ d m) c]
    have hL := (acc0Guard_eq_true_iff d (acc0RootQ d m) c).1 hguard
    simp only [ACC0SAT, Set.mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hd, hL.2⟩⟩
  · exact hT_guard c (acc0Guard_of_rpow hq_nat.ne' c hd hsize)

/-- **Williams's Theorem 4.1 (`DecidableInTimeO` language form)**: for every constant depth `d` and
modulus `m > 0`, there exist `q > 0`, `0 < δ < 1`, `c₀ > 0`, and `e` such that `ACC0SAT d m q`
(which contains all satisfiable depth-`≤ d` `ACC⁰[m]` circuits of encoding length at most
`2 ^ (n ^ (1 / q))`) is decidable in time `O(2 ^ (n - c₀ * n ^ δ))` on guarded instances plus
`O((|enc c| + 1) ^ e)`. -/
theorem decidableInTimeO_ACC0SAT (d : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (q : ℕ) (δ c₀ : ℝ) (e : ℕ), 0 < q ∧ (q : ℝ)⁻¹ < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      DecidableInTimeO (ACC0SAT d m q) (Unbounded.encExtCircuit 1) fun c =>
        (if c.2.depth ≤ d ∧ (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot q c.1 + 1)
          then (2 : ℝ) ^ ((c.1 : ℝ) - c₀ * (c.1 : ℝ) ^ δ) else 0) +
        ((Unbounded.encExtCircuit 1 c).length + 1 : ℝ) ^ e := by
  obtain ⟨hq_nat, _, hpq_inv, hp_inv_lt1⟩ := acc0RootParams_spec d m
  obtain ⟨T, e, M, hcomp, hT_guard, hT_noguard⟩ := computableInO_acc0Decider d hm
  refine ⟨acc0RootQ d m, (acc0RootP d m : ℝ)⁻¹, 1 / 2, e, hq_nat,
    hpq_inv, hp_inv_lt1, by norm_num, ?_⟩
  have hbase : DecidableInTimeO (ACC0SAT d m (acc0RootQ d m)) (Unbounded.encExtCircuit 1)
      (fun c => (T c : ℝ)) :=
    DecidableInTimeO.of_computableInO hcomp
      (fun c => (acc0Decider_eq_true_iff d hm (acc0RootP d m) (acc0RootQ d m) c).symm)
      (fun _ => le_rfl)
  refine hbase.mono M (fun c => ?_) (fun c => by split_ifs <;> positivity)
  by_cases hg : c.2.depth ≤ d ∧
      (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot (acc0RootQ d m) c.1 + 1)
  · have htrue : acc0Guard d (acc0RootQ d m) c = true :=
      (acc0Guard_eq_true_iff d (acc0RootQ d m) c).2 hg
    have hle := hT_guard c htrue
    simp only [hg, and_self, ↓reduceIte]
    have hpos : (0 : ℝ) ≤ ((Unbounded.encExtCircuit 1 c).length + 1 : ℝ) ^ e := by positivity
    nlinarith only [hle, hpos, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  · have hfalse : acc0Guard d (acc0RootQ d m) c = false := by
      cases h : acc0Guard d (acc0RootQ d m) c
      · rfl
      · exact absurd ((acc0Guard_eq_true_iff d (acc0RootQ d m) c).1 h) hg
    have hle := hT_noguard c hfalse
    simp only [hg, ↓reduceIte, zero_add]
    exact hle

end Cslib.Circuits.Boolean.SymAnd
