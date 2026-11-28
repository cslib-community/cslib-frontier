/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.SAT
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Tests for algorithmic `ACC⁰ → SYM ∘ AND` compilation and Williams's `ACC⁰-SAT`

Concrete and non-vacuous checks for
`CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.Compile` (Williams Lemma 4.1) and
`CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.SAT` (Williams Theorem 4.1):

* `SymOutParam.nestedMod` and `SymOutParam.eval` on nested moduli;
* `orExpand` on a satisfiable `MOD_3` circuit, an unsatisfiable `x₀ ∧ ¬x₀` circuit, and the
  boundary case `ℓ > n` (where all inputs are expanded);
* `compileToSymAnd` agreeing with `Circuit.toSymAnd` on a composite-modulus (`MOD_6`) circuit;
* `symAndSAT` evaluated on concrete satisfiable and unsatisfiable `(SymAndInstance, SymOutParam)`
  instances;
* non-vacuity of `exists_acc0SAT_decider` and `decidableInTimeO_ACC0SAT`: for depth `d = 1` and
  composite modulus `m = 6`, there exist both a satisfiable circuit and an unsatisfiable circuit
  satisfying the exact depth and `2 ^ (n ^ ε)` encoding-length bounds, on which the decider outputs
  `true` and `false` respectively.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0.SAT

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.SymAnd
  Cslib.Complexity Turing.MultiTapeTM

/-! ### `SymOutParam` evaluation -/

/-- Nested modulus reduction applies right-to-left: `(30 % 27) % 4 = 3 % 4 = 3`. -/
example : SymOutParam.nestedMod [4, 27] 30 = 3 := by decide

/-- `SymOutParam.eval` takes both `true` and `false` values. -/
example : SymOutParam.eval ⟨5, [4, 27]⟩ 30 = true ∧
    SymOutParam.eval ⟨5, [4, 27]⟩ 29 = false := by decide

/-! ### `orExpand` on satisfiable, unsatisfiable, and boundary (`ℓ > n`) circuits -/

/-- One `MOD_q` gate on two inputs. -/
def modTwo : Circuit Unbounded.extSignature 2 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.gate 2) id

/-- Unsatisfiable 2-input circuit computing `x₀ ∧ ¬x₀`. -/
def unsatTwo : Circuit Unbounded.extSignature 2 1 :=
  let p1 : Program Unbounded.extSignature 2 1 :=
    Program.gate Program.empty ⟨.ac .not, fun _ => Wire.input 0⟩
  let p2 : Program Unbounded.extSignature 2 2 :=
    Program.gate p1 ⟨.ac (.and 2), ![Wire.input 0, Wire.gate 0]⟩
  ⟨p2, fun _ => Wire.gate ⟨1, by decide⟩⟩

example : (orExpand 1 ⟨2, modTwo⟩).1 = 1 := by rw [orExpand_n]; rfl
example : (orExpand 1 ⟨2, modTwo⟩).2.size = 5 := by
  rw [orExpand_size]; simp [modTwo, Circuit.size_oneGate]
example : (orExpand 1 ⟨2, modTwo⟩).2.depth ≤ 3 :=
  (depth_orExpand_le 1 ⟨2, modTwo⟩).trans (by simp [modTwo, Circuit.depth_oneGate])

/-- Boundary witness: `ℓ = 5 > n = 2` expands all `2` inputs to a `0`-input circuit of size `7`. -/
example : (orExpand 5 ⟨2, modTwo⟩).1 = 0 := by rw [orExpand_n]; rfl
example : (orExpand 5 ⟨2, modTwo⟩).2.size = 7 := by
  rw [orExpand_size]; simp [modTwo, Circuit.size_oneGate]

/-- `orExpand 1` preserves satisfiability of `MOD_3` on 2 inputs. -/
theorem orExpand_mod3_sat :
    orExpand 1 ⟨2, modTwo⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate 3)) := by
  rw [orExpand_mem_SignatureCircuitSAT_iff]
  exact ⟨![true, false], by decide⟩

/-- `orExpand 5` (`ℓ > n`) preserves satisfiability of `MOD_3` on 2 inputs. -/
theorem orExpand_mod3_all_sat :
    orExpand 5 ⟨2, modTwo⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate 3)) := by
  rw [orExpand_mem_SignatureCircuitSAT_iff]
  exact ⟨![true, false], by decide⟩

/-- `unsatTwo` is unsatisfiable, and `orExpand 1` preserves unsatisfiability. -/
theorem orExpand_unsatTwo_unsat :
    orExpand 1 ⟨2, unsatTwo⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate 6)) := by
  rw [orExpand_mem_SignatureCircuitSAT_iff, mem_SignatureCircuitSAT]
  rintro ⟨x, hx⟩
  have h0 : unsatTwo.eval (Unbounded.extInterpretation (modGate 6)) x 0 =
      (x 0 && !x 0) := by
    simp only [unsatTwo, Circuit.eval, Function.comp_apply]
    change (Program.gate
      (Program.gate (Program.empty : Program Unbounded.extSignature 2 0)
        ⟨Unbounded.ExtOp.ac .not, fun _ => Wire.input 0⟩)
      ⟨Unbounded.ExtOp.ac (.and 2), ![Wire.input 0, Wire.gate 0]⟩).trace
      (Unbounded.extInterpretation (modGate 6)) x (Wire.gate (Fin.last 1)) = _
    rw [Program.trace_gate_last]
    have hgate0 : (Program.gate (Program.empty : Program Unbounded.extSignature 2 0)
        ⟨Unbounded.ExtOp.ac .not, fun _ => Wire.input 0⟩).trace
        (Unbounded.extInterpretation (modGate 6)) x (Wire.gate 0) = !x 0 := by
      change (Program.gate (Program.empty : Program Unbounded.extSignature 2 0)
        ⟨Unbounded.ExtOp.ac .not, fun _ => Wire.input 0⟩).trace
        (Unbounded.extInterpretation (modGate 6)) x (Wire.gate (Fin.last 0)) = !x 0
      rw [Program.trace_gate_last]
      rfl
    cases hx0 : x 0 <;> simp [Unbounded.extInterpretation, hgate0, hx0, Fin.forall_fin_two]
  rw [h0] at hx
  cases x 0 <;> simp at hx

/-! ### `compileToSymAnd` (Williams Lemma 4.1) -/

/-- `compileToSymAnd` agrees with `Circuit.toSymAnd` on a composite-modulus (`MOD_6`) circuit and
evaluates faithfully on both a true and a false input. -/
theorem compileToSymAnd_mod6_faithful :
    let res := compileToSymAnd 1 6 ⟨2, modTwo⟩
    let hn : res.1.n = 2 := compileToSymAnd_n 1 6 ⟨2, modTwo⟩
    (hn ▸ res.1.toSymAnd res.2.eval) = modTwo.toSymAnd 6 ∧
    (hn ▸ res.1.toSymAnd res.2.eval).eval ![true, false] = true ∧
    (hn ▸ res.1.toSymAnd res.2.eval).eval ![false, false] = false := by
  have hd : modTwo.depth ≤ 1 := by simp [modTwo, Circuit.depth_oneGate]
  let hn : (compileToSymAnd 1 6 ⟨2, modTwo⟩).1.n = 2 := compileToSymAnd_n 1 6 ⟨2, modTwo⟩
  have heq : (hn ▸ (compileToSymAnd 1 6 ⟨2, modTwo⟩).1.toSymAnd
      (compileToSymAnd 1 6 ⟨2, modTwo⟩).2.eval) = modTwo.toSymAnd 6 :=
    compileToSymAnd_eq_toSymAnd 1 (m := 6) (by decide) ⟨2, modTwo⟩ hd
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, Circuit.eval_toSymAnd _ (by decide)]; decide
  · rw [heq, Circuit.eval_toSymAnd _ (by decide)]; decide

/-- Type-checked instantiation of Williams's Lemma 4.1 (`computableInO_compileToSymAnd`) at depth 2
and composite modulus 6. -/
example : ∃ C, ComputableInO (compileToSymAnd 2 6) (Unbounded.encExtCircuit 1)
    (encPair encSymAndInstance encSymOutParam)
    (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
      2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (2 * (6 + 2)) + 1)))
    (fun c => ((Unbounded.encExtCircuit 1 c).length + 1) ^ C *
      2 ^ (C * (Nat.log 2 (c.1 + c.2.size) + 2) ^ (5 ^ (2 * (6 + 2)) + 1))) :=
  computableInO_compileToSymAnd 2 6

/-! ### `symAndSAT` on concrete instances -/

/-- Satisfiable `SYM ∘ AND` instance: two inputs, gates `{0}` and `{1}`, threshold `> 1` mod `4`. -/
def satSymInst : SymAndInstance where
  n := 2
  gates := [[true, false], [false, true]]

/-- `symAndSAT` returns `true` when threshold `3 < 2 * 2 = 4` (attained at `(true, true)`) and
`false` when threshold `4 < 2 * cnt` is unattainable (`cnt ≤ 2`). -/
example : symAndSAT (satSymInst, ⟨3, [4]⟩) = true ∧
    symAndSAT (satSymInst, ⟨4, [4]⟩) = false := by decide +kernel

/-! ### Non-vacuity of Williams's Theorem 4.1 -/

/-- A 1-gate depth-1 circuit on `n` inputs outputting constant `true` (`AND` of `0` arguments). -/
def constTrueExt (n : ℕ) : Σ n', Circuit Unbounded.extSignature n' 1 :=
  ⟨n, Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.and 0)) Fin.elim0⟩

/-- A 1-gate depth-1 circuit on `n` inputs outputting constant `false` (`OR` of `0` arguments). -/
def constFalseExt (n : ℕ) : Σ n', Circuit Unbounded.extSignature n' 1 :=
  ⟨n, Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.or 0)) Fin.elim0⟩

private theorem length_encExtCircuit_const_le (op : Unbounded.ExtOp)
    (har : Unbounded.extSignature.Arity op = 0) (n : ℕ) :
    (Unbounded.encExtCircuit 1 ⟨n, Circuit.oneGate op fun i => (har ▸ i).elim0⟩).length ≤
      4 * n + 8 * op.toNat + 24 := by
  set c : Circuit Unbounded.extSignature n 1 := Circuit.oneGate op fun i => (har ▸ i).elim0
  have hcode : c.code = ([(op, [])], [n]) := by
    refine Prod.ext ?_ ?_
    · simp only [c, Circuit.oneGate, Circuit.code, Program.code_gate, Program.code_empty,
        List.nil_append, Line.code]
      congr 2
      refine List.ext_getElem
        (by simp only [List.length_ofFn, List.length_nil]; exact har) fun i hi _ => ?_
      have hi' : i < op.arity := by simpa only [List.length_ofFn] using hi
      have har' : op.arity = 0 := har
      omega
    · simp [c, Circuit.oneGate, Circuit.code, Wire.toNat_gate]
  rw [Circuit.encCircuit_apply, hcode, length_encPair, encUnary_apply, List.length_replicate,
    Circuit.encCode, length_encPair, encList_cons, encList_nil, List.append_nil, encList_cons,
    encList_nil, List.append_nil, length_frame, length_frame, Circuit.encGate, length_encPair,
    encList_nil, List.length_nil]
  dsimp only
  have hop : (Unbounded.encExtOp op).length = op.toNat := by
    simp [Unbounded.encExtOp, encUnary_apply]
  have hn : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len n]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  omega

private theorem exists_linear_le_two_rpow (A B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, A * (n : ℝ) + B ≤ (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkε : 1 ≤ (k : ℝ) * ε := by
    have := (div_lt_iff₀ hε).1 hk
    linarith
  set c : ℝ := Real.log 2
  have hc : 0 < c := Real.log_pos (by norm_num)
  set coeff : ℝ := c ^ (2 * k) / ((2 * k).factorial : ℝ)
  have hcoeff : 0 < coeff := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((max A 0 + max B 0 + 1) / coeff + 1)
  refine ⟨max N 1, ?_⟩
  set n : ℕ := max N 1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right N 1
  have hnN : ((max A 0 + max B 0 + 1) / coeff + 1 : ℝ) < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast le_max_left N 1)
  have hlin : A * (n : ℝ) + B ≤ coeff * (n : ℝ) ^ 2 := by
    have h1 : A * (n : ℝ) + B ≤ (max A 0 + max B 0 + 1) * (n : ℝ) := by
      have hA : A ≤ max A 0 := le_max_left A 0
      have hB : B ≤ max B 0 := le_max_left B 0
      have hB0 : 0 ≤ max B 0 := le_max_right B 0
      nlinarith
    have h2 : max A 0 + max B 0 + 1 ≤ coeff * (n : ℝ) := by
      have := (div_lt_iff₀ hcoeff).1 (by linarith : (max A 0 + max B 0 + 1) / coeff < (n : ℝ))
      linarith
    nlinarith
  have hpow_le : (n : ℝ) ^ 2 ≤ ((n : ℝ) ^ ε) ^ (2 * k) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ε) (2 * k), ← Real.rpow_mul (by linarith)]
    have hexp : (2 : ℝ) ≤ ε * ((2 * k : ℕ) : ℝ) := by push_cast; linarith
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hexp_n : (2 : ℝ) ^ ((n : ℝ) ^ ε) = Real.exp (c * (n : ℝ) ^ ε) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hfac := Real.pow_div_factorial_le_exp (c * (n : ℝ) ^ ε) (by positivity) (2 * k)
  rw [← hexp_n, mul_pow] at hfac
  have hrew : coeff * ((n : ℝ) ^ ε) ^ (2 * k) =
      c ^ (2 * k) * ((n : ℝ) ^ ε) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    dsimp only [coeff]; ring
  calc A * (n : ℝ) + B ≤ coeff * (n : ℝ) ^ 2 := hlin
    _ ≤ coeff * ((n : ℝ) ^ ε) ^ (2 * k) := mul_le_mul_of_nonneg_left hpow_le hcoeff.le
    _ ≤ (2 : ℝ) ^ ((n : ℝ) ^ ε) := by rw [hrew]; exact hfac

/-- **Non-vacuity of `exists_acc0SAT_decider`**: for depth `1` and composite modulus `6`,
Williams's Theorem 4.1 produces a decider `decideSAT` and exponents `0 < ε < δ < 1`, `c₀ > 0`
together with concrete circuits `c_sat` and `c_unsat` that both meet the depth and `2 ^ (n ^ ε)`
encoding-length bounds, with `decideSAT c_sat = true` and `decideSAT c_unsat = false`. -/
theorem acc0SAT_decider_nonvacuous :
    ∃ (ε δ c₀ : ℝ), 0 < ε ∧ ε < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∃ (decideSAT : (Σ n, Circuit Unbounded.extSignature n 1) → Bool)
        (T : (Σ n, Circuit Unbounded.extSignature n 1) → ℕ),
        ComputableInO decideSAT (Unbounded.encExtCircuit 1) encBool T T ∧
        ∃ c_sat c_unsat,
          c_sat.2.depth ≤ 1 ∧
          ((Unbounded.encExtCircuit 1 c_sat).length : ℝ) ≤ (2 : ℝ) ^ ((c_sat.1 : ℝ) ^ ε) ∧
          decideSAT c_sat = true ∧
          c_unsat.2.depth ≤ 1 ∧
          ((Unbounded.encExtCircuit 1 c_unsat).length : ℝ) ≤ (2 : ℝ) ^ ((c_unsat.1 : ℝ) ^ ε) ∧
          decideSAT c_unsat = false := by
  obtain ⟨ε, δ, c₀, hε, hεδ, hδ1, hc₀, decideSAT, T, hcomp, hspec, -⟩ :=
    exists_acc0SAT_decider 1 (m := 6) (by decide)
  obtain ⟨n, hn⟩ := exists_linear_le_two_rpow 4 40 ε hε
  have hlen_sat : ((Unbounded.encExtCircuit 1 (constTrueExt n)).length : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
    have hlen := length_encExtCircuit_const_le (.ac (.and 0)) rfl n
    have hcast : ((Unbounded.encExtCircuit 1 (constTrueExt n)).length : ℝ) ≤ 4 * (n : ℝ) + 40 := by
      exact_mod_cast (hlen.trans (by simp [Unbounded.ExtOp.toNat]))
    exact hcast.trans hn
  have hlen_unsat : ((Unbounded.encExtCircuit 1 (constFalseExt n)).length : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
    have hlen := length_encExtCircuit_const_le (.ac (.or 0)) rfl n
    have hcast : ((Unbounded.encExtCircuit 1 (constFalseExt n)).length : ℝ) ≤ 4 * (n : ℝ) + 40 := by
      exact_mod_cast (hlen.trans (by simp [Unbounded.ExtOp.toNat]))
    exact hcast.trans hn
  refine ⟨ε, δ, c₀, hε, hεδ, hδ1, hc₀, decideSAT, T, hcomp,
    constTrueExt n, constFalseExt n, ?_, hlen_sat, ?_, ?_, hlen_unsat, ?_⟩
  · simp [constTrueExt, Circuit.depth_oneGate]
  · exact (hspec (constTrueExt n) (by simp [constTrueExt, Circuit.depth_oneGate]) hlen_sat).2
      ⟨fun _ => false, by simp [constTrueExt, Circuit.eval_oneGate, Unbounded.extInterpretation]⟩
  · simp [constFalseExt, Circuit.depth_oneGate]
  · have hiff := hspec (constFalseExt n) (by simp [constFalseExt, Circuit.depth_oneGate]) hlen_unsat
    cases hd : decideSAT (constFalseExt n)
    · rfl
    · obtain ⟨x, hx⟩ := hiff.1 hd
      have hev : (Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.or 0)) Fin.elim0).eval
          (Unbounded.extInterpretation (modGate 6)) (x : BitString n) 0 = false := by
        rw [Circuit.eval_oneGate]
        rfl
      exact absurd (hev.symm.trans hx) (by decide)

/-- Type-checked instantiation of the `DecidableInTimeO` language form at depth `1` and modulus `6`.
-/
example : ∃ (q : ℕ) (δ c₀ : ℝ) (e : ℕ), 0 < q ∧ (q : ℝ)⁻¹ < δ ∧ δ < 1 ∧ 0 < c₀ ∧
    DecidableInTimeO (ACC0SAT 1 6 q) (Unbounded.encExtCircuit 1) fun c =>
      (if c.2.depth ≤ 1 ∧ (Unbounded.encExtCircuit 1 c).length ≤ 2 ^ (Nat.nthRoot q c.1 + 1)
        then (2 : ℝ) ^ ((c.1 : ℝ) - c₀ * (c.1 : ℝ) ^ δ) else 0) +
      ((Unbounded.encExtCircuit 1 c).length + 1 : ℝ) ^ e :=
  decidableInTimeO_ACC0SAT 1 (m := 6) (by decide)

end CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.ACC0.SAT
