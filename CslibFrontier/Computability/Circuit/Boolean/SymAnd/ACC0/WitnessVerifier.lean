/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.ACC0.SAT
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.FineNondeterministicExponentialTime
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Encoding.Check
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Encoding.PolyTime
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.Nat.LogRpow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Witness verification and `NTIME` diagonalization transfer for `ACC⁰`

This module formalizes the constant-depth witness-verification and nondeterministic-time
diagonalization bridge from Williams's proof that `ACC⁰-SAT` algorithms imply witness-circuit lower
bounds ([Williams2014], Section 3, Theorem 3.2, statement p. 8 and proof p. 13 of the author's
July 31, 2012 version).

Given a succinct 3-CNF decoder circuit `D` over `Unbounded.extSignature` (`ACC⁰[m]`) on `q` inputs
describing `2 ^ q` clauses over `2 ^ r` variables in the interleaved address/sign layout of
`Cslib.Circuits.Boolean.SuccinctVerifier`, and a candidate witness circuit `W` on `r` inputs:

1. **Constant-depth bad-clause verifier (`badClauseExt`)**: plugs three copies of `W` and one copy
   of `D` into the embedded 3-literal violation test `SuccinctVerifier.violationTest`. The resulting
   `ACC⁰[m]` circuit has `q` inputs, `D.size + 3 * W.size + 17` gates, depth at most
   `D.depth + W.depth + 5`, and is unsatisfiable precisely when `W`'s truth table satisfies
   `toCNFExt m D` (`not_mem_SignatureCircuitSAT_badClauseExt_iff`).
2. **Depth-capped certificate compilation (`decodeExtWitness`, `certificateCircuitExt`)**: decodes
   a framed canonical circuit code at the start of a bit string to a valid depth-`≤ d` witness
   circuit `W` (rejecting non-canonical or malformed codes and circuits exceeding depth `d` by
   emitting the always-satisfiable constant-`true` circuit), with a native polynomial-time
   compilation certificate (`computableInPolyTime_certificateCircuitExt`).
3. **Subexponential-savings `NTIME` simulation (`smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT`)**:
   combines `certificateCircuitExt` with Williams's `ACC⁰-SAT` algorithm (`exists_acc0SAT_decider`,
   [Williams2014], Theorem 4.1) to decide in `NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)` whether a quasilinear
   uniform depth-`≤ dD` `ACC⁰[m]` succinct 3-CNF has a satisfying assignment computable by a
   depth-`≤ dW` `ACC⁰[m]` circuit of code length at most `2 ^ Nat.nthRoot r_w n`.
4. **Hard-witness transfer (`exists_hard_acc0Witness_of_quasilinear_reduction`)**: combines the
   simulation with the fine nondeterministic exponential time hierarchy
   (`Cslib.Complexity.NTIME_two_pow_sub_rpow_ssubset`, [Zak1983]) to produce a single language
   `H ∈ NTIME(2 ^ n)` such that every polynomial-time uniform depth-`≤ dD` `ACC⁰[m]` quasilinear
   succinct 3-CNF reduction of `H` has a satisfiable instance `x ∈ H` admitting no depth-`≤ dW`,
   code-length-`≤ 2 ^ Nat.nthRoot r_w |x|` `ACC⁰[m]` satisfying witness circuit.

## Scope note

This module proves the witness-verifier and diagonalization-transfer steps unconditionally. It does
not construct the quasilinear `O(T log T)` succinct 3-CNF reduction for `NTIME(2 ^ n)`
([Williams2014], Fact 3.1) or the nondeterministic `ACC⁰` compression of De Morgan circuits
([Williams2014], Lemma 3.1), so it does not claim the full `E^NP ⊄ ACC⁰` or `NEXP ⊄ ACC⁰`
separations ([Williams2014], Theorems 1.1–1.2).

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.clauseExt`, `Cslib.Circuits.Boolean.SymAnd.toCNFExt`:
  succinct 3-CNF represented by an `ACC⁰[m]` decoder circuit.
* `Cslib.Circuits.Boolean.SymAnd.badClauseExt`: constant-depth `ACC⁰[m]` bad-clause verifier.
* `Cslib.Circuits.Boolean.SymAnd.decodeExtWitness`,
  `Cslib.Circuits.Boolean.SymAnd.certificateCircuitExt`: depth-capped witness decoder and total
  verifier circuit compiler.
* `Cslib.Circuits.Boolean.SymAnd.smallACC0WitnessLanguage`: language of inputs whose succinct
  3-CNF admits a small constant-depth `ACC⁰[m]` satisfying witness circuit.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.size_badClauseExt`,
  `Cslib.Circuits.Boolean.SymAnd.depth_badClauseExt_le`,
  `Cslib.Circuits.Boolean.SymAnd.eval_badClauseExt`,
  `Cslib.Circuits.Boolean.SymAnd.not_mem_SignatureCircuitSAT_badClauseExt_iff`: size, depth, and
  correctness of `badClauseExt`.
* `Cslib.Circuits.Boolean.SymAnd.exists_cert_not_mem_SignatureCircuitSAT_iff`,
  `Cslib.Circuits.Boolean.SymAnd.computableInPolyTime_certificateCircuitExt`: witness equivalence
  and native polynomial-time compilation.
* `Cslib.Circuits.Boolean.SymAnd.smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT`: unconditional
  `NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)` upper bound via `exists_acc0SAT_decider`.
* `Cslib.Circuits.Boolean.SymAnd.exists_hard_acc0Witness_of_quasilinear_reduction`: witness-circuit
  lower bound for every quasilinear `ACC⁰[m]` succinct 3-CNF reduction of a hard language in
  `NTIME(2 ^ n)`.

## References

* [R. Williams, *Non-Uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Section 3,
  Theorem 3.2 (pp. 8, 13) and Section 4, Theorem 4.1 (p. 17)][Williams2014]
* [S. Žák, *A Turing Machine Time Hierarchy*][Zak1983]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Logic.PL Filter

/-! ### 1. Succinct 3-CNF over `Unbounded.extSignature` and `badClauseExt` -/

section BadClause

variable {q r : ℕ}

/-- The clause at address `x` decoded by an `ACC⁰[m]` circuit `D` on `q` inputs, using the
interleaved address/sign layout of `SuccinctVerifier`. -/
@[expose] def clauseExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (x : BitString q) : Clause (BitString r) :=
  List.ofFn fun j : Fin 3 =>
    (fun i => D.eval (Unbounded.extInterpretation (modGate m)) x
        (SuccinctVerifier.addressWire r j i),
      D.eval (Unbounded.extInterpretation (modGate m)) x (SuccinctVerifier.signWire r j))

/-- Expand every `q`-bit clause address of an `ACC⁰[m]` decoder `D` into a 3-CNF on `2 ^ r`
variables. -/
@[expose] def toCNFExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1))) :
    CNF (BitString r) :=
  (BitString.enum q).map (clauseExt m D)

/-- The expanded formula `toCNFExt m D` holds on an assignment `a` iff every clause address is
satisfied. -/
theorem eval_toCNFExt_eq_true_iff (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (a : BitString r → Bool) :
    (toCNFExt m D).eval a = true ↔ ∀ x : BitString q, (clauseExt m D x).eval a = true := by
  simp [toCNFExt, CNF.eval_map_eq_true_iff]

/-- The De Morgan signature embedded into `Unbounded.extSignature`. -/
private def deMorganToExt : Boolean.signature.Hom Unbounded.extSignature :=
  Unbounded.toExt.comp Unbounded.deMorganToUnbounded

private instance preserves_deMorganToExt (m : ℕ) :
    deMorganToExt.Preserves Boolean.interpretation (Unbounded.extInterpretation (modGate m)) :=
  Signature.Hom.Preserves.comp (Unbounded.preserves_toExt (modGate m))
    Unbounded.preserves_deMorganToUnbounded

/-- Fixed 17-gate, depth-5 three-literal violation test over `Unbounded.extSignature`, lifted from
`SuccinctVerifier.violationTest`. -/
private def violationTestExt : Circuit Unbounded.extSignature 6 1 :=
  SuccinctVerifier.violationTest.toCircuit.mapOp deMorganToExt

private theorem size_violationTestExt : violationTestExt.size = 17 := by
  simp [violationTestExt, Circuit.size_mapOp]

private theorem depth_violationTestExt_le : violationTestExt.depth ≤ 5 := by
  rw [violationTestExt, Circuit.depth_mapOp]
  exact SuccinctVerifier.violationTest.depth_toCircuit_le.trans (by decide)

private theorem eval_violationTestExt (m : ℕ) (values signs : Fin 3 → Bool) :
    violationTestExt.eval (Unbounded.extInterpretation (modGate m))
      (Fin.append values signs) 0 =
      ((values 0 ^^ signs 0) && ((values 1 ^^ signs 1) && (values 2 ^^ signs 2))) := by
  rw [violationTestExt,
    @Circuit.eval_mapOp _ _ _ _ _ deMorganToExt Boolean.interpretation
      (Unbounded.extInterpretation (modGate m)) (preserves_deMorganToExt m),
    Formula.eval_toCircuit]
  exact SuccinctVerifier.eval_violationTest values signs

/-- **Constant-depth `ACC⁰` bad-clause circuit**: evaluates the decoder `D` once, feeds each of
the three decoded variable addresses into a copy of `W`, and checks whether all three literals of
the addressed clause are violated. -/
def badClauseExt (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) : Circuit Unbounded.extSignature q 1 :=
  (violationTestExt.comp
    ((Circuit.pi fun j : Fin 3 =>
        W.comp (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j))).append
      (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)))).comp D

/-- **Exact gate count of `badClauseExt`.** -/
@[simp] theorem size_badClauseExt (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).size = D.size + 3 * W.size + 17 := by
  simp [badClauseExt, size_violationTestExt, Finset.sum_const, Nat.mul_comm, Nat.add_assoc]

/-- **Constant additive depth overhead of `badClauseExt`.** -/
theorem depth_badClauseExt_le (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).depth ≤ D.depth + W.depth + 5 := by
  unfold badClauseExt
  let wAddr (j : Fin 3) := Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j)
  let wSign := Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)
  let piC := Circuit.pi fun j : Fin 3 => W.comp (wAddr j)
  have hpi : piC.depth ≤ W.depth :=
    Circuit.depth_pi_le _ fun j => by simpa [wAddr] using Circuit.depth_comp_le W (wAddr j)
  have happ : (piC.append wSign).depth ≤ W.depth :=
    hpi.trans' (by simpa [wSign] using Circuit.depth_append_le piC wSign)
  have houter := Circuit.depth_comp_le (violationTestExt.comp (piC.append wSign)) D
  have hmid := Circuit.depth_comp_le violationTestExt (piC.append wSign)
  have hv := depth_violationTestExt_le
  change ((violationTestExt.comp (piC.append wSign)).comp D).depth ≤ _
  omega

/-- **Pointwise correctness of `badClauseExt`**: returns `true` on clause address `x` iff `W`'s
truth table violates clause `x`. -/
theorem eval_badClauseExt (m : ℕ) (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) (x : BitString q) :
    (badClauseExt D W).eval (Unbounded.extInterpretation (modGate m)) x 0 =
      !(clauseExt m D x).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) := by
  simp only [badClauseExt, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_pi,
    Circuit.eval_wiring, eval_violationTestExt, Function.comp_def]
  simp only [clauseExt, List.ofFn_succ, List.ofFn_zero, Clause.eval_cons, Clause.eval_nil,
    Literal.eval_mk, Bool.or_false]
  simp only [← Bool.bne_eq_xor, bne, Bool.not_or, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

/-- **Verification by `ACC⁰` circuit unsatisfiability**: `badClauseExt D W` is unsatisfiable iff
`W`'s truth table satisfies `toCNFExt m D`. -/
theorem not_mem_SignatureCircuitSAT_badClauseExt_iff (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (⟨q, badClauseExt D W⟩ ∉ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      (toCNFExt m D).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  simp [mem_SignatureCircuitSAT, eval_badClauseExt, eval_toCNFExt_eq_true_iff]

end BadClause

/-! ### 2. Total certificate decoding and polynomial-time verifier compilation -/

section CertDecode

/-- Bijective inverse of `Unbounded.ExtOp.toNat` on `ℕ`. -/
private def extOpOfNat : ℕ → Unbounded.ExtOp
  | 0 => .ac .not
  | n + 1 =>
    match n % 3 with
    | 0 => .ac (.and (n / 3))
    | 1 => .ac (.or (n / 3))
    | _ => .gate (n / 3)

private theorem extOpOfNat_toNat (op : Unbounded.ExtOp) : extOpOfNat op.toNat = op := by
  rcases op with (_ | m | m) | m <;> simp only [Unbounded.ExtOp.toNat, extOpOfNat]
  · simp [Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 3)]
  · rw [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1) / 3 = m by omega]; rfl
  · rw [show (3 * m + 2) % 3 = 2 by omega, show (3 * m + 2) / 3 = m by omega]; rfl

private theorem toNat_extOpOfNat (k : ℕ) : (extOpOfNat k).toNat = k := by
  rcases k with _ | n
  · rfl
  · simp only [extOpOfNat]
    have := Nat.div_add_mod n 3
    have := Nat.mod_lt n (by decide : 0 < 3)
    rcases hm : n % 3 with _ | _ | _ | r <;> simp only [Unbounded.ExtOp.toNat] <;> omega

/-- Total polynomial-time decoder for `Unbounded.encExtOp`. -/
private def decExtOp : Decoder Unbounded.encExtOp :=
  Decoder.map Decoder.unary extOpOfNat Unbounded.ExtOp.toNat extOpOfNat_toNat fun k =>
    congrArg encUnary (toNat_extOpOfNat k)

/-- Total polynomial-time decoder for raw `Unbounded.extSignature` circuit codes. -/
private def decExtCode : Decoder (Circuit.encCode Unbounded.encExtOp) :=
  Decoder.pair (Decoder.list (Decoder.pair decExtOp (Decoder.list Decoder.nat)))
    (Decoder.list Decoder.nat)

private theorem extArity_eq (op : Unbounded.ExtOp) :
    Unbounded.extSignature.Arity op = if op.toNat = 0 then 1 else (op.toNat - 1) / 3 := by
  rcases op with (_ | m | m) | m
  · rfl
  · simp [Unbounded.ExtOp.arity, Unbounded.Op.arity, Unbounded.ExtOp.toNat]
  · simp [Unbounded.ExtOp.arity, Unbounded.Op.arity, Unbounded.ExtOp.toNat]; omega
  · simp [Unbounded.ExtOp.arity, Unbounded.ExtOp.toNat]; omega

private theorem computableInPolyTime_extArity :
    ComputableInPolyTime Unbounded.extSignature.Arity Unbounded.encExtOp encNat := by
  have h1 : ComputableInPolyTime (fun op : Unbounded.ExtOp =>
      if op.toNat = 0 then 1 else (op.toNat - 1) / 3) Unbounded.encExtOp encUnary := by
    have htest : ComputableInPolyTime (fun op : Unbounded.ExtOp => decide (op.toNat = 0))
        Unbounded.encExtOp encBool := by fun_prop
    have hdiv : ComputableInPolyTime (fun op : Unbounded.ExtOp => (op.toNat - 1) / 3)
        Unbounded.encExtOp encUnary :=
      (ComputableInPolyTime.unary_div_const 3).comp (by fun_prop)
    exact (htest.ite (ComputableInPolyTime.const 1) hdiv).of_enc_eq fun op => by
      simp only [decide_eq_true_eq]
  exact (ComputableInPolyTime.unary_to_binary.comp h1).of_enc_eq fun op =>
    congrArg encNat (extArity_eq op)

/-- Decode a raw certificate bit string `w` into a valid `r`-input single-output `ACC⁰` witness
circuit of depth at most `d`, reading the canonical framed code at the start of `w` via `unframe w`.
Returns `none` on non-canonical words, malformed codes, wrong output count, out-of-range wires,
or depth `> d`. -/
def decodeExtWitness (d r : ℕ) (w : List Bool) :
    Option (Circuit Unbounded.extSignature r 1) :=
  let u := unframe w
  let code := decExtCode.decode u
  if Circuit.encCode Unbounded.encExtOp code = u then
    match Circuit.ofCode (σ := Unbounded.extSignature) r 1 code with
    | some W => if W.depth ≤ d then some W else none
    | none => none
  else none

/-- Decoding a framed encoding of a valid depth-`≤ d` circuit recovers it regardless of trailing
padding bits. -/
theorem decodeExtWitness_frame_append {d r : ℕ} (W : Circuit Unbounded.extSignature r 1)
    (hdepth : W.depth ≤ d) (pad : List Bool) :
    decodeExtWitness d r (frame (Circuit.encCode Unbounded.encExtOp W.code) ++ pad) = some W := by
  simp only [decodeExtWitness, unframe_frame_append, decExtCode.decode_enc, ↓reduceIte,
    Circuit.ofCode_code, hdepth]

/-- Decoding rejects a valid circuit whose depth exceeds the cap `d`. -/
theorem decodeExtWitness_eq_none_of_depth_gt {d r : ℕ} (W : Circuit Unbounded.extSignature r 1)
    (hdepth : d < W.depth) (pad : List Bool) :
    decodeExtWitness d r (frame (Circuit.encCode Unbounded.encExtOp W.code) ++ pad) = none := by
  have hnot : ¬ W.depth ≤ d := Nat.not_le.mpr hdepth
  simp only [decodeExtWitness, unframe_frame_append, decExtCode.decode_enc, ↓reduceIte,
    Circuit.ofCode_code, hnot]

/-- Decoding rejects the empty (non-canonical) certificate word. -/
theorem decodeExtWitness_nil (d r : ℕ) : decodeExtWitness d r [] = none := by
  unfold decodeExtWitness
  dsimp only [unframe]
  split_ifs with h
  · have := congrArg List.length h
    simp [Circuit.encCode] at this
  · rfl

/-- Any circuit returned by `decodeExtWitness d r w` has depth at most `d` and canonical code
length at most `w.length / 2`. -/
theorem depth_and_codeLength_of_decodeExtWitness_eq_some {d r : ℕ} {w : List Bool}
    {W : Circuit Unbounded.extSignature r 1} (h : decodeExtWitness d r w = some W) :
    W.depth ≤ d ∧ 2 * (Circuit.encCode Unbounded.encExtOp W.code).length ≤ w.length := by
  unfold decodeExtWitness at h
  dsimp only at h
  split_ifs at h with hcan
  rcases hof : Circuit.ofCode (σ := Unbounded.extSignature) r 1 (decExtCode.decode (unframe w))
    with _ | W'
  · simp [hof] at h
  · simp only [hof] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [Circuit.code_of_ofCode_eq_some hof, hcan]
    have := length_unframe_add_dropFrame_le w
    exact ⟨hd, by omega⟩

/-- Constant `true` circuit on `q` inputs over `Unbounded.extSignature` (one nullary AND gate,
depth `1`, always satisfiable). -/
private def constTrueExt (q : ℕ) : Circuit Unbounded.extSignature q 1 :=
  Circuit.oneGate (σ := Unbounded.extSignature) (.ac (.and 0)) Fin.elim0

private theorem depth_constTrueExt (q : ℕ) : (constTrueExt q).depth ≤ 1 := by
  simp [constTrueExt, Circuit.depth_oneGate]

private theorem constTrueExt_mem_SignatureCircuitSAT (m q : ℕ) :
    ⟨q, constTrueExt q⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  rw [mem_SignatureCircuitSAT]
  refine ⟨fun _ => false, ?_⟩
  simp only [constTrueExt, Circuit.eval_oneGate]
  exact decide_eq_true fun j => j.elim0

/-- **Total depth-capped verifier circuit**: decodes `w` as a depth-`≤ d` witness circuit `W` and
emits `badClauseExt D W`; if `w` is malformed or exceeds depth `d`, emits the always-satisfiable
constant-`true` circuit so the verifier rejects `w`. -/
def certificateCircuitExt {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    Circuit Unbounded.extSignature q 1 :=
  match decodeExtWitness d r w with
  | some W => badClauseExt D W
  | none => constTrueExt q

/-- `certificateCircuitExt D d w` always has depth at most `D.depth + d + 5`. -/
theorem depth_certificateCircuitExt_le {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    (certificateCircuitExt D d w).depth ≤ D.depth + d + 5 := by
  unfold certificateCircuitExt
  cases h : decodeExtWitness d r w with
  | none => exact (depth_constTrueExt q).trans (by omega)
  | some W =>
    have hW := (depth_and_codeLength_of_decodeExtWitness_eq_some h).1
    exact (depth_badClauseExt_le D W).trans (by omega)

/-- `certificateCircuitExt D d w` is unsatisfiable iff `w` decodes to a depth-`≤ d` witness
circuit whose truth table satisfies `toCNFExt m D`. -/
theorem not_mem_SignatureCircuitSAT_certificateCircuitExt_iff {q r : ℕ} (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d : ℕ) (w : List Bool) :
    (⟨q, certificateCircuitExt D d w⟩ ∉
        SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      ∃ W : Circuit Unbounded.extSignature r 1, decodeExtWitness d r w = some W ∧
        (toCNFExt m D).eval
          (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  unfold certificateCircuitExt
  cases h : decodeExtWitness d r w with
  | none =>
    simp [constTrueExt_mem_SignatureCircuitSAT]
  | some W =>
    simp only [Option.some.injEq, exists_eq_left']
    exact not_mem_SignatureCircuitSAT_badClauseExt_iff m D W

/-- **Certificate-length witness equivalence**: a certificate `w` of exact length `2 * L + 1` makes
`certificateCircuitExt D d w` unsatisfiable iff there is a depth-`≤ d` `ACC⁰[m]` witness circuit
`W` of code length at most `L` whose truth table satisfies `toCNFExt m D`. -/
theorem exists_cert_not_mem_SignatureCircuitSAT_iff {q r : ℕ} (m : ℕ)
    (D : Circuit Unbounded.extSignature q (3 * (r + 1))) (d L : ℕ) :
    (∃ w : List Bool, w.length = 2 * L + 1 ∧
      ⟨q, certificateCircuitExt D d w⟩ ∉
        SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
    ∃ W : Circuit Unbounded.extSignature r 1,
      W.depth ≤ d ∧ (Circuit.encCode Unbounded.encExtOp W.code).length ≤ L ∧
      (toCNFExt m D).eval
        (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  constructor
  · rintro ⟨w, hwlen, hunsat⟩
    obtain ⟨W, hdec, hsat⟩ :=
      (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff m D d w).1 hunsat
    obtain ⟨hdepth, hlen⟩ := depth_and_codeLength_of_decodeExtWitness_eq_some hdec
    exact ⟨W, hdepth, by omega, hsat⟩
  · rintro ⟨W, hdepth, hlen, hsat⟩
    set u := Circuit.encCode Unbounded.encExtOp W.code
    set w := frame u ++ List.replicate (2 * L + 1 - (frame u).length) false
    have hflen : (frame u).length ≤ 2 * L + 1 := by rw [length_frame]; omega
    refine ⟨w, ?_, (not_mem_SignatureCircuitSAT_certificateCircuitExt_iff m D d w).2
      ⟨W, decodeExtWitness_frame_append W hdepth _, hsat⟩⟩
    simp only [w, List.length_append, List.length_replicate]
    omega

/-- Raw code builder matching `(badClauseExt D W).code`. -/
private def badClauseExtCode (q r : ℕ)
    (Dcode Wcode : List (Unbounded.ExtOp × List ℕ) × List ℕ) :
    List (Unbounded.ExtOp × List ℕ) × List ℕ :=
  let nMid := 3 * (r + 1)
  let c0 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 0 * (r + 1) + i)
  let c1 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 1 * (r + 1) + i)
  let c2 := Circuit.compCode nMid Wcode ([], (List.range r).map fun i => 2 * (r + 1) + i)
  let piCode := Circuit.appendCodes nMid [c0, c1, c2]
  let signCode : List (Unbounded.ExtOp × List ℕ) × List ℕ :=
    ([], [0 * (r + 1) + r, 1 * (r + 1) + r, 2 * (r + 1) + r])
  let appCode := Circuit.appendCode nMid piCode signCode
  let midCode := Circuit.compCode nMid violationTestExt.code appCode
  Circuit.compCode q midCode Dcode

private theorem code_badClauseExt {q r : ℕ}
    (D : Circuit Unbounded.extSignature q (3 * (r + 1)))
    (W : Circuit Unbounded.extSignature r 1) :
    (badClauseExt D W).code = badClauseExtCode q r D.code W.code := by
  have haddr (j : Fin 3) :
      (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.addressWire r j)).code =
        ([], (List.range r).map fun i => j.val * (r + 1) + i) :=
    Circuit.code_wiring_eq_map fun _ => rfl
  have hsign : (Circuit.wiring Unbounded.extSignature (SuccinctVerifier.signWire r)).code =
      ([], [0 * (r + 1) + r, 1 * (r + 1) + r, 2 * (r + 1) + r]) := by
    simp only [Circuit.code_wiring, List.ofFn_succ, List.ofFn_zero, SuccinctVerifier.signWire,
      Fin.val_zero, Fin.succ_zero_eq_one, Fin.val_one, Fin.succ_one_eq_two, Fin.val_two]
  unfold badClauseExt badClauseExtCode
  simp only [Circuit.code_comp, Circuit.code_append, Circuit.code_pi, hsign,
    List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, haddr,
    Fin.val_zero, Fin.val_one, Fin.val_two]

private theorem validRaw_iff {r : ℕ} (code : List (Unbounded.ExtOp × List ℕ) × List ℕ) :
    (codeCheck Unbounded.extSignature r code.1 && decide (code.2.length = 1) &&
        decide (code.2.getD 0 0 < r + code.1.length)) = true ↔
      (Circuit.ofCode (σ := Unbounded.extSignature) r 1 code).isSome := by
  rw [Circuit.isSome_ofCode_iff, Bool.and_eq_true, Bool.and_eq_true, codeCheck_eq_true_iff]
  rcases code.2 with _ | ⟨a, _ | _⟩ <;> simp

private theorem computableInPolyTime_badClauseExtCode :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ((List (Unbounded.ExtOp × List ℕ) × List ℕ) ×
          (List (Unbounded.ExtOp × List ℕ) × List ℕ)) =>
        badClauseExtCode p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encUnary)
        (encPair (Circuit.encCode Unbounded.encExtOp) (Circuit.encCode Unbounded.encExtOp)))
      (Circuit.encCode Unbounded.encExtOp) := by
  let Code := List (Unbounded.ExtOp × List ℕ) × List ℕ
  let In := (ℕ × ℕ) × (Code × Code)
  let encC := Circuit.encCode Unbounded.encExtOp
  let encIn := encPair (encPair encUnary encUnary) (encPair encC encC)
  have hqBin : ComputableInPolyTime (fun p : In => p.1.1) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun p : In => p.1.2) encIn encUnary := by fun_prop
  have hD : ComputableInPolyTime (fun p : In => p.2.1) encIn encC := by fun_prop
  have hW : ComputableInPolyTime (fun p : In => p.2.2) encIn encC := by fun_prop
  have hnMidBin : ComputableInPolyTime (fun p : In => 3 * (p.1.2 + 1)) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have haddr (k : ℕ) : ComputableInPolyTime
      (fun p : In => (([] : List (Unbounded.ExtOp × List ℕ)),
        (List.range p.1.2).map fun i => k * (p.1.2 + 1) + i)) encIn encC :=
    (ComputableInPolyTime.const []).prod <|
      ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hr)
        (ComputableInPolyTime.unary_to_binary.comp
          (show ComputableInPolyTime (fun q : ((ℕ × ℕ) × (Code × Code)) × ℕ =>
            k * (q.1.1.2 + 1) + q.2) _ _ by fun_prop))
  have hc (k : ℕ) := Circuit.computableInPolyTime_compCode hnMidBin hW (haddr k)
  have hpi := Circuit.computableInPolyTime_appendCodes hnMidBin
    ((hc 0).cons' ((hc 1).cons' ((hc 2).cons' (.const []))))
  have hs (k : ℕ) : ComputableInPolyTime (fun p : In => k * (p.1.2 + 1) + p.1.2) encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hsign : ComputableInPolyTime
      (fun p : In => (([] : List (Unbounded.ExtOp × List ℕ)),
        [0 * (p.1.2 + 1) + p.1.2, 1 * (p.1.2 + 1) + p.1.2, 2 * (p.1.2 + 1) + p.1.2]))
      encIn encC :=
    (ComputableInPolyTime.const []).prod ((hs 0).cons' ((hs 1).cons' ((hs 2).cons' (.const []))))
  exact Circuit.computableInPolyTime_compCode hqBin
    (Circuit.computableInPolyTime_compCode hnMidBin (.const violationTestExt.code)
      (Circuit.computableInPolyTime_appendCode hnMidBin hpi hsign)) hD

/-- **Native polynomial-time compilation of `certificateCircuitExt`**: given any polynomial-time
uniform family of `ACC⁰` succinct 3-CNF decoders `D` and fixed depth cap `d`, compiling `(x, w)`
to `⟨q x, certificateCircuitExt (D x) d w⟩` is computable in polynomial time. -/
theorem computableInPolyTime_certificateCircuitExt
    {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (hq : ComputableInPolyTime q encBits encUnary)
    (hr : ComputableInPolyTime r encBits encUnary)
    (hD : ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp))
    (d : ℕ) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (⟨q p.1, certificateCircuitExt (D p.1) d p.2⟩ : Σ n, Circuit Unbounded.extSignature n 1))
      (encPair encBits encBits) (Unbounded.encExtCircuit 1) := by
  let P := List Bool × List Bool
  let encP := encPair encBits encBits
  let encC := Circuit.encCode Unbounded.encExtOp
  let encRaw := encPair encUnary encC
  let dec (p : P) := decExtCode.decode (unframe p.2)
  have hqP : ComputableInPolyTime (fun p : P => q p.1) encP encUnary :=
    hq.comp (.fst encBits encBits)
  have hrP : ComputableInPolyTime (fun p : P => r p.1) encP encUnary :=
    hr.comp (.fst encBits encBits)
  have hDP : ComputableInPolyTime (fun p : P => (D p.1).code) encP encC :=
    hD.comp (.fst encBits encBits)
  have hu : ComputableInPolyTime (fun p : P => unframe p.2) encP encBits :=
    Internal.DecoderWords.unframe_degree.computableInPolyTime.comp (.snd encBits encBits)
  have hcode : ComputableInPolyTime dec encP encC := decExtCode.computableInPolyTime.comp hu
  have hcan : ComputableInPolyTime
      (fun p : P => decide (Circuit.encCode Unbounded.encExtOp (dec p) = unframe p.2))
      encP encBool :=
    ComputableInPolyTime.decide_eq' (hcode.of_enc_eq (encD := encBits) fun _ => rfl) hu
  have hck := Circuits.computableInPolyTime_codeCheck computableInPolyTime_extArity hrP hcode.fst'
  have hlen1 : ComputableInPolyTime (fun p : P => decide ((dec p).2.length = 1)) encP encBool :=
    ComputableInPolyTime.decide_eq'
      ((ComputableInPolyTime.length encNat).comp hcode.snd') (.const 1)
  have hhead0 : ComputableInPolyTime (fun p : P => (dec p).2.getD 0 0) encP encNat :=
    ((ComputableInPolyTime.headD (encA := encNat) (encL := encList encNat) 0).comp
      hcode.snd').of_enc_eq fun p => congrArg encNat <| by
        dsimp only [Function.comp_apply, dec]
        cases (dec p).2 <;> rfl
  have houtLt : ComputableInPolyTime
      (fun p : P => decide ((dec p).2.getD 0 0 < r p.1 + (dec p).1.length)) encP encBool :=
    ComputableInPolyTime.binary_lt' hhead0
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.unary_add' hrP
          ((ComputableInPolyTime.length (Circuit.encGate Unbounded.encExtOp)).comp hcode.fst')))
  have hvalid := ComputableInPolyTime.bool_and' hcan
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hck hlen1) houtLt)
  let rawOpt (p : P) : Option (Σ n, Circuit Unbounded.extSignature n 1) :=
    if Circuit.encCode Unbounded.encExtOp (dec p) = unframe p.2 then
      (Circuit.ofCode (σ := Unbounded.extSignature) (r p.1) 1 (dec p)).map fun W => ⟨r p.1, W⟩
    else none
  have hrawOpt : ComputableInPolyTime rawOpt encP (encOption (Unbounded.encExtCircuit 1)) := by
    refine (hvalid.ite ((ComputableInPolyTime.optionSome encRaw).comp (hrP.prod hcode))
      (.const none)).of_enc_eq fun p => ?_
    dsimp only [rawOpt, Function.comp_apply]
    by_cases hcanp : Circuit.encCode Unbounded.encExtOp (dec p) = unframe p.2
    · have hval : (codeCheck Unbounded.extSignature (r p.1) (dec p).1 &&
          decide ((dec p).2.length = 1) &&
          decide ((dec p).2.getD 0 0 < r p.1 + (dec p).1.length)) =
          (Circuit.ofCode (σ := Unbounded.extSignature) (r p.1) 1 (dec p)).isSome :=
        Bool.eq_iff_iff.mpr (validRaw_iff _)
      simp only [hcanp, ↓reduceIte, decide_true, Bool.true_and, hval]
      rcases hof : Circuit.ofCode (σ := Unbounded.extSignature) (r p.1) 1 (dec p) with _ | W
      · simp
      · simp [Unbounded.encExtCircuit, Circuit.encCircuit_apply,
          Circuit.code_of_ofCode_eq_some hof, encRaw, encC, dec]
    · simp only [hcanp, ↓reduceIte, decide_false, Bool.false_and, Bool.false_eq_true,
        encOption_none]
  let witnessOpt : List Bool × List Bool → Option (Σ n, Circuit Unbounded.extSignature n 1) :=
    fun p => (decodeExtWitness d (r p.1) p.2).map fun W => ⟨r p.1, W⟩
  have hwitnessOpt : ComputableInPolyTime witnessOpt encP
      (encOption (Unbounded.encExtCircuit 1)) := by
    have hbody : ComputableInPolyTime
        (fun q : (List Bool × List Bool) × (Σ n, Circuit Unbounded.extSignature n 1) =>
          if decide (q.2.2.depth ≤ d) then some q.2 else none)
        (encPair encP (Unbounded.encExtCircuit 1)) (encOption (Unbounded.encExtCircuit 1)) :=
      (ComputableInPolyTime.unary_le'
          (computableInPolyTime_extCircuit_depth.comp (ComputableInPolyTime.snd _ _))
          (ComputableInPolyTime.const d)).ite
        ((ComputableInPolyTime.optionSome _).comp (ComputableInPolyTime.snd _ _))
        (ComputableInPolyTime.const none)
    have helim := hrawOpt.optionElimWithInput
      (body := fun _ c => if decide (c.2.depth ≤ d) then some c else none)
      (ComputableInPolyTime.const none) hbody
    refine helim.of_enc_eq fun p => congrArg (encOption (Unbounded.encExtCircuit 1)) ?_
    dsimp only [witnessOpt, rawOpt, decodeExtWitness, dec]
    split_ifs with hcanp
    · cases hof : Circuit.ofCode (σ := Unbounded.extSignature) (r p.1) 1
          (decExtCode.decode (unframe p.2)) with
      | none => rfl
      | some W =>
        simp only [Option.map_some, Option.elim_some, decide_eq_true_eq]
        split_ifs <;> rfl
    · rfl
  have hconstCode : ComputableInPolyTime
      (fun p : List Bool × List Bool => (q p.1, (constTrueExt (q p.1)).code))
      encP encRaw := by
    have h1 : ComputableInPolyTime (fun p : List Bool × List Bool => (constTrueExt (q p.1)).code)
        encP (Circuit.encCode Unbounded.encExtOp) := by
      have hcodeConst (k : ℕ) : (constTrueExt k).code = ([(.ac (.and 0), [])], [k]) := by
        simp [constTrueExt, Circuit.code_oneGate]
      simp only [hcodeConst]
      exact (ComputableInPolyTime.const [(Unbounded.ExtOp.ac (.and 0), ([] : List ℕ))]).prod
        ((ComputableInPolyTime.unary_to_binary.comp hqP).cons' (ComputableInPolyTime.const []))
    exact hqP.prod h1
  have hbadBody : ComputableInPolyTime
      (fun s : (List Bool × List Bool) × (Σ n, Circuit Unbounded.extSignature n 1) =>
        (q s.1.1, badClauseExtCode (q s.1.1) (r s.1.1) (D s.1.1).code s.2.2.code))
      (encPair encP (Unbounded.encExtCircuit 1)) encRaw := by
    have hWcode : ComputableInPolyTime
        (fun s : (List Bool × List Bool) × (Σ n, Circuit Unbounded.extSignature n 1) => s.2.2.code)
        (encPair encP (Unbounded.encExtCircuit 1)) (Circuit.encCode Unbounded.encExtOp) :=
      (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
        Unbounded.encExtOp 1).snd'.comp (ComputableInPolyTime.snd _ _)
    have hqS := hqP.comp (ComputableInPolyTime.fst encP (Unbounded.encExtCircuit 1))
    have hrS := hrP.comp (ComputableInPolyTime.fst encP (Unbounded.encExtCircuit 1))
    have hDS := hDP.comp (ComputableInPolyTime.fst encP (Unbounded.encExtCircuit 1))
    exact hqS.prod
      (computableInPolyTime_badClauseExtCode.comp ((hqS.prod hrS).prod (hDS.prod hWcode)))
  have hfinal := hwitnessOpt.optionElimWithInput
    (body := fun p c => (q p.1, badClauseExtCode (q p.1) (r p.1) (D p.1).code c.2.code))
    hconstCode hbadBody
  refine hfinal.of_enc_eq fun p => ?_
  dsimp only [witnessOpt, certificateCircuitExt]
  cases h : decodeExtWitness d (r p.1) p.2 with
  | none =>
    simp only [Option.map_none, Option.elim_none, Unbounded.encExtCircuit, Circuit.encCircuit_apply,
      encRaw, encC]
  | some W =>
    simp only [Option.map_some, Option.elim_some, Unbounded.encExtCircuit, Circuit.encCircuit_apply,
      code_badClauseExt, encRaw, encC]

end CertDecode

/-! ### 3. Input padding and asymptotic estimates -/

section PadAndAsymptotics

/-- Pad a single-output circuit on `q` inputs with unused dummy inputs up to `max q n`. -/
private def padInputs {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (n : ℕ) :
    Circuit Unbounded.extSignature (max q n) 1 :=
  C.comp (Circuit.wiring Unbounded.extSignature (Fin.castLE (le_max_left q n)))

private theorem depth_padInputs_le {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (n : ℕ) :
    (padInputs C n).depth ≤ C.depth := by
  unfold padInputs
  have h := Circuit.depth_comp_le C
    (Circuit.wiring Unbounded.extSignature (Fin.castLE (le_max_left q n)))
  simpa only [Circuit.depth_wiring, Nat.add_zero] using h

private theorem padInputs_mem_SignatureCircuitSAT_iff {q : ℕ} (m : ℕ)
    (C : Circuit Unbounded.extSignature q 1) (n : ℕ) :
    (⟨max q n, padInputs C n⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m))) ↔
      ⟨q, C⟩ ∈ SignatureCircuitSAT (Unbounded.extInterpretation (modGate m)) := by
  simp only [mem_SignatureCircuitSAT, padInputs, Circuit.eval_comp, Circuit.eval_wiring]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i => x (Fin.castLE (le_max_left q n) i), hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun i => if hi : i.val < q then y ⟨i.val, hi⟩ else false, ?_⟩
    have hfun : (fun i : Fin q =>
        if hi : (Fin.castLE (le_max_left q n) i).val < q then y ⟨(Fin.castLE _ i).val, hi⟩
        else false) = y := by
      funext i
      simp [i.isLt]
    simpa only [Function.comp_def, hfun] using hy

private theorem code_padInputs {q : ℕ} (C : Circuit Unbounded.extSignature q 1) (n : ℕ) :
    (padInputs C n).code = Circuit.compCode (max q n) C.code ([], List.range q) := by
  have hw : (Circuit.wiring Unbounded.extSignature (Fin.castLE (le_max_left q n))).code =
      ([], List.range q) := by
    simpa using Circuit.code_wiring_eq_map (σ := Unbounded.extSignature)
      (f := Fin.castLE (le_max_left q n)) (g := id) fun _ => rfl
  simp only [padInputs, Circuit.code_comp, hw]

attribute [local irreducible] ComputableInPolyTime in
private theorem computableInPolyTime_padCertificateCircuitExt
    {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (hq : ComputableInPolyTime q encBits encUnary)
    (hr : ComputableInPolyTime r encBits encUnary)
    (hD : ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp))
    (d : ℕ) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (⟨max (q p.1) p.1.length, padInputs (certificateCircuitExt (D p.1) d p.2) p.1.length⟩ :
          Σ n, Circuit Unbounded.extSignature n 1))
      (encPair encBits encBits) (Unbounded.encExtCircuit 1) := by
  let encP := encPair encBits encBits
  have hcert := computableInPolyTime_certificateCircuitExt D hq hr hD d
  have hcertCode : ComputableInPolyTime
      (fun p : List Bool × List Bool => (certificateCircuitExt (D p.1) d p.2).code)
      encP (Circuit.encCode Unbounded.encExtOp) :=
    (Circuit.computableInPolyTime_arity_code (σ := Unbounded.extSignature)
      Unbounded.encExtOp 1).snd'.comp hcert
  have hqP : ComputableInPolyTime (fun p : List Bool × List Bool => q p.1) encP encUnary :=
    hq.comp (ComputableInPolyTime.fst encBits encBits)
  have hlenP : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length) encP encUnary :=
    ((ComputableInPolyTime.encoding_length encBits).comp
      (ComputableInPolyTime.fst encBits encBits)).of_enc_eq fun _ => rfl
  have hmax : ComputableInPolyTime (fun p : List Bool × List Bool => max (q p.1) p.1.length)
      encP encUnary :=
    ((ComputableInPolyTime.unary_le' hqP hlenP).ite hlenP hqP).of_enc_eq fun p =>
      congrArg encUnary (by
        simp only [decide_eq_true_eq]
        split_ifs with h
        · rw [Nat.max_eq_right h]
        · rw [Nat.max_eq_left (Nat.le_of_not_ge h)])
  have hrange : ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        (([] : List (Unbounded.ExtOp × List ℕ)), List.range (q p.1)))
      encP (Circuit.encCode Unbounded.encExtOp) :=
    (ComputableInPolyTime.const []).prod
      ((ComputableInPolyTime.unary_to_binary.map.comp
        (ComputableInPolyTime.range.comp hqP)).of_enc_eq fun p =>
        congrArg (encList encNat) (by simp only [Function.comp_apply, List.map_id']))
  have hmaxBin : ComputableInPolyTime (fun p : List Bool × List Bool => max (q p.1) p.1.length)
      encP encNat :=
    (ComputableInPolyTime.unary_to_binary.comp hmax).of_enc_eq fun _ => rfl
  have hcomp := Circuit.computableInPolyTime_compCode hmaxBin hcertCode hrange
  exact (hmax.prod hcomp).of_enc_eq fun p => by
    rw [Unbounded.encExtCircuit, Circuit.encCircuit_apply, code_padInputs]

private theorem nthRoot_le_rpow_real {r_w : ℕ} (hr : 0 < r_w) (n : ℕ) :
    (Nat.nthRoot r_w n : ℝ) ≤ (n : ℝ) ^ ((r_w : ℝ)⁻¹) := by
  have hpow : (Nat.nthRoot r_w n : ℝ) ^ r_w ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := r_w) (a := n) (Or.inl hr.ne')
  calc (Nat.nthRoot r_w n : ℝ)
      = ((Nat.nthRoot r_w n : ℝ) ^ r_w) ^ ((r_w : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), Real.rpow_one]
    _ ≤ (n : ℝ) ^ ((r_w : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _) hpow (by positivity)

/-- For any real exponents `a < b` and real constant `c`, `c * n ^ a ≤ n ^ b` eventually. -/
private theorem eventually_mul_rpow_le_rpow {a b : ℝ} (hab : a < b) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop c, eventually_ge_atTop 1] with n hn h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc c * (n : ℝ) ^ a
      ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hn0.le a)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hn0, sub_add_cancel]

/-- For `(r_w : ℝ)⁻¹ < ε`, any `C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n)` is eventually
bounded by `2 ^ (n ^ ε)`. -/
private theorem eventually_poly_mul_two_pow_nthRoot_le {r_w : ℕ} (hr : 0 < r_w) {ε : ℝ}
    (hlt : (r_w : ℝ)⁻¹ < ε) (C d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
  have hε : 0 < ε := lt_trans (by positivity) hlt
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (b := 2) Nat.one_lt_two 1 1 1
    (K := (2 * (C.size + d + 1) : ℝ)) (by positivity) hε
  have hbound := eventually_mul_rpow_le_rpow hlt (2 * ((d : ℝ) + 1))
  filter_upwards [hlog, hbound] with n hln hsn
  have hC : C ≤ 2 ^ C.size := (Nat.lt_size_self C).le
  have hnp : (n + 1) ^ d ≤ 2 ^ (d * (Nat.log 2 (n + 1) + 1)) := by
    have h1 : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
      (Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 1)).le
    calc (n + 1) ^ d ≤ (2 ^ (Nat.log 2 (n + 1) + 1)) ^ d := Nat.pow_le_pow_left h1 d
      _ = 2 ^ (d * (Nat.log 2 (n + 1) + 1)) := by rw [← pow_mul, mul_comm]
  have hnat : C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) ≤
      2 ^ (C.size + d * (Nat.log 2 (n + 1) + 1) + d * Nat.nthRoot r_w n) := by
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hC hnp)
  have hcast : ((C * (n + 1) ^ d * 2 ^ (d * Nat.nthRoot r_w n) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((C.size + d * (Nat.log 2 (n + 1) + 1) + d * Nat.nthRoot r_w n : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  refine hcast.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  rw [pow_one] at hln
  push_cast at hln ⊢
  have hlog_nn : (0 : ℝ) ≤ Nat.log 2 (n + 1) := Nat.cast_nonneg _
  have hnr_nn : (0 : ℝ) ≤ Nat.nthRoot r_w n := Nat.cast_nonneg _
  have hmul : 2 * ((d : ℝ) + 1) * (Nat.nthRoot r_w n : ℝ) ≤ (n : ℝ) ^ ε :=
    (mul_le_mul_of_nonneg_left (nthRoot_le_rpow_real hr n) (by positivity)).trans hsn
  have hCsz : (C.size : ℝ) ≤ (C.size : ℝ) * ((Nat.log 2 (n + 1) : ℝ) + 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  nlinarith

/-- For `0 < ε < δ < 1`, `0 < c₀`, and `c : ℕ`, eventually:
(a) `(n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ`,
(b) `c * (log₂(n + 2) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ`, and
(c) `1 ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)`. -/
private theorem eventually_subexp_envelope {ε δ c₀ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ1 : δ < 1)
    (hc₀ : 0 < c₀) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ ∧
      (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ ∧
      (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ) := by
  have hδ : 0 < δ := lt_trans hε hεδ
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (b := 2) Nat.one_lt_two 2 1 1
    (K := (2 * ((c : ℝ) + 1)) / c₀) (by positivity) hδ
  have hs1 := eventually_mul_rpow_le_rpow (lt_trans hεδ hδ1) (2 : ℝ)
  have hs2 := eventually_mul_rpow_le_rpow hδ1 (c₀ + 1)
  filter_upwards [hlog, hs1, hs2] with n hln h1 h2
  rw [Real.rpow_one] at h1 h2
  have hc0le : (c₀ / 2) * (n : ℝ) ^ δ ≤ (1 / 2 : ℝ) * (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hpart1 : (n : ℝ) ^ ε ≤ (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ := by linarith
  have hpart2 : (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) ≤ (c₀ / 2) * (n : ℝ) ^ δ := by
    rw [pow_one] at hln
    have hmul := mul_le_mul_of_nonneg_left hln (show (0 : ℝ) ≤ c₀ / 2 by positivity)
    have hcancel : (c₀ / 2) * (2 * ((c : ℝ) + 1) / c₀) = (c : ℝ) + 1 := by
      field_simp
    rw [← mul_assoc, hcancel] at hmul
    have hnn : (0 : ℝ) ≤ (Nat.log 2 (n + 2) : ℝ) + 1 := by positivity
    nlinarith
  have hpart3 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ) :=
    Real.one_le_rpow (by norm_num) (by linarith [Real.rpow_nonneg (Nat.cast_nonneg n) ε])
  exact ⟨hpart1, hpart2, hpart3⟩

end PadAndAsymptotics

/-! ### 4. Unconditional `NTIME` simulation and hard-witness transfer -/

section WitnessTransfer

/-- **Small-`ACC⁰`-witness language** of a succinct 3-CNF family `D`: the set of inputs `x` whose
represented 3-CNF `toCNFExt m (D x)` has a satisfying assignment computable by an `ACC⁰[m]` circuit
of depth at most `dW` and canonical code length at most `L x`. -/
@[expose] def smallACC0WitnessLanguage (m dW : ℕ) {q r : List Bool → ℕ}
    (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
    (L : List Bool → ℕ) : Set (List Bool) :=
  {x | ∃ W : Circuit Unbounded.extSignature (r x) 1,
    W.depth ≤ dW ∧ (Circuit.encCode Unbounded.encExtOp W.code).length ≤ L x ∧
    (toCNFExt m (D x)).eval
      (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true}

/-- **Subexponential-savings `NTIME` simulation of small `ACC⁰` witnesses** ([Williams2014],
Theorem 3.2 witness-checking step combined with Theorem 4.1 `exists_acc0SAT_decider`): for every
constant decoder depth `dD`, witness depth `dW`, and modulus `m > 0`, there exist `r_w > 0`,
`0 < δ < 1`, and `c₀ > 0` (depending only on `dD`, `dW`, and `m`) such that for every
polynomial-time uniform depth-`≤ dD` `ACC⁰[m]` succinct 3-CNF family `D` with quasilinear
clause-index count `q x ≤ |x| + c * Nat.log 2 (|x| + 2) + c`, deciding whether `toCNFExt m (D x)`
has a depth-`≤ dW`, code-length-`≤ 2 ^ Nat.nthRoot r_w |x|` `ACC⁰[m]` satisfying witness lies in
`NTIME(⌊2 ^ (n - c₀ * n ^ δ)⌋₊)`. -/
theorem smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT (dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (δ c₀ : ℝ), 0 < r_w ∧ 0 < δ ∧ δ < 1 ∧ 0 < c₀ ∧
      ∀ {q r : List Bool → ℕ}
        (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
        (c : ℕ),
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp) →
        (∀ x, (D x).depth ≤ dD) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        smallACC0WitnessLanguage m dW D (fun x => 2 ^ Nat.nthRoot r_w x.length) ∈
          NTIME encBits fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ := by
  classical
  obtain ⟨ε, δ, c₀, hε, hεδ, hδ1, hc₀, decideSAT, T_sat, hSAT_O, hSAT_corr, M_sat, hSAT_time⟩ :=
    exists_acc0SAT_decider (dD + dW + 5) hm
  set r_w : ℕ := Nat.ceil (2 / ε) + 1
  have hrw_pos : 0 < r_w := Nat.succ_pos _
  have hrw_lt : (r_w : ℝ)⁻¹ < ε := by
    rw [inv_lt_comm₀ (by positivity) hε]
    have : 2 / ε ≤ (Nat.ceil (2 / ε) : ℝ) := Nat.le_ceil _
    have : 1 / ε < 2 / ε := by
      gcongr
      norm_num
    dsimp only [r_w]
    push_cast
    linarith [one_div ε]
  refine ⟨r_w, δ, c₀ / 2, hrw_pos, lt_trans hε hεδ, hδ1, by positivity, ?_⟩
  intro q r D c hq hr hD hdepth hq_le
  let padCert : List Bool × List Bool → Σ n, Circuit Unbounded.extSignature n 1 := fun p =>
    ⟨max (q p.1) p.1.length, padInputs (certificateCircuitExt (D p.1) dW p.2) p.1.length⟩
  have hpad_poly : ComputableInPolyTime padCert (encPair encBits encBits)
      (Unbounded.encExtCircuit 1) :=
    computableInPolyTime_padCertificateCircuitExt D hq hr hD dW
  obtain ⟨Tc, Sc, hTc, hSc, hpadO⟩ := hpad_poly.exists_computableInO
  obtain ⟨_, d_out, hdeg⟩ := hpad_poly.exists_degree
  obtain ⟨C_out, hC_out⟩ := hdeg.2
  obtain ⟨Ct, dt, hTc_le⟩ := hTc.exists_le
  -- 1. Certificate length `ℓ x = 2 * 2 ^ Nat.nthRoot r_w x.length + 1` in unary
  have hnr_self (k : ℕ) : Nat.nthRoot r_w k ≤ k :=
    (Nat.le_self_pow hrw_pos.ne' _).trans
      (Nat.pow_nthRoot_le (n := r_w) (a := k) (Or.inl hrw_pos.ne'))
  let ℓ : List Bool → ℕ := fun x => 2 * 2 ^ Nat.nthRoot r_w x.length + 1
  have hroot : ComputableInPolyTime (fun x : List Bool => Nat.nthRoot r_w x.length)
      encBits encUnary := by
    have hlen_bits : ComputableInPolyTime (fun x : List Bool => x.length) encBits encUnary := by
      fun_prop
    have hbin := ComputableInPolyTime.binary_nthRoot'
      (ComputableInPolyTime.const (encIn := encBits) r_w)
      (ComputableInPolyTime.unary_to_binary.comp hlen_bits)
    exact ComputableInPolyTime.binary_to_unary_bounded hbin hlen_bits
      (fun x => hnr_self x.length)
  obtain ⟨Tr, Sr, hTr, hSr, hrootO⟩ := hroot.exists_computableInO
  obtain ⟨Cr, dr, hTr_le⟩ := hTr.exists_le
  have hpowO := ComputableInO.unary_two_pow.comp hrootO
  have h2p1_poly : ComputableInPolyTime (fun k : ℕ => 2 * k + 1) encUnary encUnary := by fun_prop
  obtain ⟨Tm, Sm, hTm, hSm, hmO⟩ := h2p1_poly.exists_computableInO
  obtain ⟨Cm, dm, hTm_le⟩ := hTm.exists_le
  have hℓO : ComputableInO ℓ encBits encUnary _ _ := hmO.comp hpowO
  -- 2. Asymptotic threshold `M₀` where `|enc (padCert (x, w))| ≤ 2 ^ (n ^ ε)`
  have hpair_le (x w : List Bool) (hw : w.length = ℓ x) :
      (encPair encBits encBits (x, w)).length + 1 ≤
        7 * (x.length + 1) * 2 ^ Nat.nthRoot r_w x.length := by
    set n := x.length with hn
    set P := 2 ^ Nat.nthRoot r_w n with hP
    have hP1 : 1 ≤ P := Nat.one_le_two_pow
    simp only [length_encPair, encBits_apply, hw, ℓ]
    rw [← hn, ← hP]
    have h1 : 2 * n + 3 ≤ 5 * (n + 1) * P :=
      (by omega : 2 * n + 3 ≤ 5 * (n + 1)).trans (Nat.le_mul_of_pos_right _ hP1)
    have h2 : 2 * P ≤ 2 * (n + 1) * P := Nat.mul_le_mul_right P (by omega)
    have : 7 * (n + 1) * P = 5 * (n + 1) * P + 2 * (n + 1) * P := by ring
    omega
  let C_enc : ℕ := (C_out + 1) * 7 ^ d_out
  have henc_ev := eventually_poly_mul_two_pow_nthRoot_le hrw_pos hrw_lt C_enc d_out
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp henc_ev
  have hpad_len_bound (x w : List Bool) (hw : w.length = ℓ x) :
      (Unbounded.encExtCircuit 1 (padCert (x, w))).length ≤
        C_enc * (x.length + 1) ^ d_out * 2 ^ (d_out * Nat.nthRoot r_w x.length) := by
    set n := x.length with hn
    set P := 2 ^ Nat.nthRoot r_w n with hP
    have hpair : (encPair encBits encBits (x, w)).length + 1 ≤ 7 * (n + 1) * P :=
      hpair_le x w hw
    have h1 := hC_out (x, w)
    calc (Unbounded.encExtCircuit 1 (padCert (x, w))).length
        ≤ C_out * ((encPair encBits encBits (x, w)).length + 1) ^ d_out := h1
      _ ≤ (C_out + 1) * (7 * (n + 1) * P) ^ d_out :=
          Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_left hpair d_out)
      _ = ((C_out + 1) * 7 ^ d_out) * (n + 1) ^ d_out * P ^ d_out := by
          rw [Nat.mul_pow, Nat.mul_pow]; ring
      _ = C_enc * (n + 1) ^ d_out * 2 ^ (d_out * Nat.nthRoot r_w n) := by
          rw [show P ^ d_out = 2 ^ (d_out * Nat.nthRoot r_w n) by
            dsimp only [P]; rw [← pow_mul, mul_comm]]
  have hpad_guarded (x w : List Bool) (hx : M₀ ≤ x.length) (hw : w.length = ℓ x) :
      (padCert (x, w)).2.depth ≤ dD + dW + 5 ∧
        ((Unbounded.encExtCircuit 1 (padCert (x, w))).length : ℝ) ≤
          (2 : ℝ) ^ (((padCert (x, w)).1 : ℝ) ^ ε) := by
    refine ⟨(depth_padInputs_le _ _).trans
      ((depth_certificateCircuitExt_le (D x) dW w).trans (by have := hdepth x; omega)), ?_⟩
    have h1 : ((Unbounded.encExtCircuit 1 (padCert (x, w))).length : ℝ) ≤
        ((C_enc * (x.length + 1) ^ d_out * 2 ^ (d_out * Nat.nthRoot r_w x.length) : ℕ) : ℝ) := by
      exact_mod_cast hpad_len_bound x w hw
    have h2 := hM₀ x.length hx
    have h3 : (2 : ℝ) ^ ((x.length : ℝ) ^ ε) ≤ (2 : ℝ) ^ (((padCert (x, w)).1 : ℝ) ^ ε) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε.le
      exact_mod_cast le_max_right (q x) x.length
    exact (h1.trans h2).trans h3
  -- 3. Finite lookup table for `x.length < M₀`, and verifier `V`
  let L_target := smallACC0WitnessLanguage m dW D fun y => 2 ^ Nat.nthRoot r_w y.length
  let S_fin : List (List Bool) :=
    ((List.range M₀).flatMap BitString.enumList).filter fun x => decide (x ∈ L_target)
  have hS_fin (x : List Bool) (hx : x.length < M₀) : x ∈ S_fin ↔ x ∈ L_target := by
    simp only [S_fin, List.mem_filter, List.mem_flatMap, List.mem_range, BitString.mem_enumList,
      decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨x.length, hx, rfl⟩, h⟩⟩
  let V : List Bool × List Bool → Bool := fun p =>
    if p.1.length < M₀ then decide (p.1 ∈ S_fin) else !decideSAT (padCert p)
  have hguard_poly : ComputableInPolyTime
      (fun p : List Bool × List Bool => decide (p.1.length < M₀))
      (encPair encBits encBits) encBool := by fun_prop
  obtain ⟨Tg, Sg, hTg, hSg, hguardO⟩ := hguard_poly.exists_computableInO
  obtain ⟨Cg, dg, hTg_le⟩ := hTg.exists_le
  have hfin_poly : ComputableInPolyTime (fun p : List Bool × List Bool => decide (p.1 ∈ S_fin))
      (encPair encBits encBits) encBool :=
    ComputableInPolyTime.decide_mem (ComputableInPolyTime.const S_fin)
      (ComputableInPolyTime.fst encBits encBits)
  obtain ⟨Tf, Sf, hTf, hSf, hfinO⟩ := hfin_poly.exists_computableInO
  obtain ⟨Cf, df, hTf_le⟩ := hTf.exists_le
  have hnotSAT : ComputableInO (fun p : List Bool × List Bool => !decideSAT (padCert p))
      (encPair encBits encBits) encBool _ _ :=
    (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
      fun b : Bool => !b).inO_one.comp (hSAT_O.comp hpadO)
  have hVO := (hguardO.ite hfinO hnotSAT).of_enc_eq (g := V) fun p => congrArg encBool (by
    simp only [V, decide_eq_true_eq])
  -- 4. Exactness of the verifier language
  have hlang : {x | ∃ w : List Bool, w.length = ℓ x ∧ V (x, w) = true} = L_target := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x.length < M₀
    · simp only [V, hx, ↓reduceIte, decide_eq_true_eq, hS_fin x hx]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨List.replicate (ℓ x) false, by simp, h⟩⟩
    · simp only [V, hx, ↓reduceIte, Bool.not_eq_true', ← Bool.not_eq_true]
      refine (exists_congr fun w => and_congr_right fun hw => ?_).trans
        (exists_cert_not_mem_SignatureCircuitSAT_iff m (D x) dW (2 ^ Nat.nthRoot r_w x.length))
      obtain ⟨hd, hl⟩ := hpad_guarded x w (Nat.le_of_not_lt hx) hw
      exact not_congr ((hSAT_corr _ hd hl).trans (padInputs_mem_SignatureCircuitSAT_iff m _ _))
  -- 5. Uniform time envelope for `setOf_exists_mem_NTIME`
  let D_all : ℕ := dr + dm + dg + df + dt + 2
  let C_poly : ℕ := (10 + Cr + Cm * 2 ^ dm + Cg * 7 ^ dg + Cf * 7 ^ df + Ct * 7 ^ dt) * 4
  have hev_poly := eventually_poly_mul_two_pow_nthRoot_le hrw_pos hrw_lt C_poly D_all
  have hev_env := eventually_subexp_envelope hε hεδ hδ1 hc₀ c
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hev_poly.and hev_env)
  set M_cut := max M₀ M₁
  let tBound : ℕ → ℕ := fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)⌋₊
  -- Coarse `n`-only upper bound valid for ALL `n < M_cut` (and polynomial part for all `n`)
  let polyEnv : ℕ → ℕ := fun n =>
    C_poly * (n + 1) ^ D_all * 2 ^ (D_all * Nat.nthRoot r_w n)
  let satEnv : ℕ → ℕ := fun n =>
    (M_sat + 1) * 2 ^ (n + c * Nat.log 2 (n + 2) + c) + M_sat + 1
  let B_fin : ℕ := (Finset.range M_cut).sup fun n => polyEnv n + satEnv n + 4
  let C_total : ℕ := max (2 * M_sat + 4) (B_fin + M_sat + 4)
  change L_target ∈ NTIME encBits tBound
  rw [← hlang]
  refine setOf_exists_mem_NTIME hℓO hVO (C := C_total) fun x w hw => ?_
  set n := x.length with hn
  set P := 2 ^ Nat.nthRoot r_w n with hP
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hnr_le : Nat.nthRoot r_w n ≤ n := hnr_self n
  have hpair : (encPair encBits encBits (x, w)).length + 1 ≤ 7 * (n + 1) * P := hpair_le x w hw
  have hpow_le (k : ℕ) (hk : k ≤ D_all) :
      ((n + 1) ^ k * P ^ k) ≤ (n + 1) ^ D_all * 2 ^ (D_all * Nat.nthRoot r_w n) := by
    have h1 : (n + 1) ^ k ≤ (n + 1) ^ D_all := Nat.pow_le_pow_right (Nat.succ_pos _) hk
    have h2 : P ^ k ≤ 2 ^ (D_all * Nat.nthRoot r_w n) := by
      dsimp only [P]
      rw [← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.mul_le_mul_right _ hk)
    exact Nat.mul_le_mul h1 h2
  set E_base := (n + 1) ^ D_all * 2 ^ (D_all * Nat.nthRoot r_w n)
  have hE1 : 1 ≤ E_base := Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) Nat.one_le_two_pow
  have hPairPow (k : ℕ) (hk : k ≤ D_all) :
      ((encPair encBits encBits (x, w)).length + 1) ^ k ≤ 7 ^ k * E_base := by
    calc ((encPair encBits encBits (x, w)).length + 1) ^ k
        ≤ (7 * (n + 1) * P) ^ k := Nat.pow_le_pow_left hpair k
      _ = 7 ^ k * ((n + 1) ^ k * P ^ k) := by rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc]
      _ ≤ 7 ^ k * E_base := Nat.mul_le_mul_left _ (hpow_le k hk)
  have hTr_b : Tr x ≤ Cr * E_base :=
    (hTr_le x).trans <| Nat.mul_le_mul_left Cr <|
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos hP1)).trans
        (hpow_le dr (by dsimp only [D_all]; omega))
  have h1_b : (n + 1) * P ≤ E_base := by
    simpa using hpow_le 1 (by dsimp only [D_all]; omega)
  have hExp_b : (Nat.nthRoot r_w n + 1) * P ≤ E_base :=
    (Nat.mul_le_mul_right P (by omega)).trans h1_b
  have hn_b : n ≤ E_base :=
    ((Nat.le_succ n).trans (Nat.le_mul_of_pos_right _ hP1)).trans h1_b
  have hTm_b : Tm P ≤ Cm * 2 ^ dm * E_base := by
    have h1 := hTm_le P
    simp only [encUnary_apply, List.length_replicate] at h1
    have h3 : P ^ dm ≤ E_base :=
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos n))).trans
        (hpow_le dm (by dsimp only [D_all]; omega))
    calc Tm P ≤ Cm * (P + 1) ^ dm := h1
      _ ≤ Cm * (2 * P) ^ dm := Nat.mul_le_mul_left Cm (Nat.pow_le_pow_left (by omega) dm)
      _ = Cm * 2 ^ dm * P ^ dm := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ Cm * 2 ^ dm * E_base := Nat.mul_le_mul_left _ h3
  have hPairB {T : List Bool × List Bool → ℕ} {C d : ℕ}
      (hT : ∀ p, T p ≤ C * ((encPair encBits encBits p).length + 1) ^ d) (hd : d ≤ D_all) :
      T (x, w) ≤ C * 7 ^ d * E_base := by
    rw [Nat.mul_assoc]
    exact (hT (x, w)).trans (Nat.mul_le_mul_left C (hPairPow d hd))
  have hTg_b := hPairB hTg_le (by dsimp only [D_all]; omega)
  have hTf_b := hPairB hTf_le (by dsimp only [D_all]; omega)
  have hTc_b := hPairB hTc_le (by dsimp only [D_all]; omega)
  have hpoly_sum : n + (Tr x + (Nat.nthRoot r_w n + 1) * P + Tm P) +
      (Tg (x, w) + max (Tf (x, w)) (Tc (x, w) + 2)) ≤ polyEnv n := by
    have heq : polyEnv n =
        4 * ((10 * E_base + Cr * E_base + Cm * 2 ^ dm * E_base + Cg * 7 ^ dg * E_base +
          Cf * 7 ^ df * E_base + Ct * 7 ^ dt * E_base)) := by
      dsimp only [polyEnv, C_poly, E_base]; ring
    omega
  -- Split on `n < M_cut` vs `M_cut ≤ n`
  simp only [encBits_apply, encBool_apply, List.length_singleton]
  rw [← hn]
  by_cases hsmall : n < M_cut
  · -- Small `n < M_cut`: either `n < M₀` (finite lookup) or `M₀ ≤ n < M_cut` (guarded SAT)
    have hB : polyEnv n + satEnv n + 4 ≤ B_fin :=
      Finset.le_sup (f := fun k => polyEnv k + satEnv k + 4) (Finset.mem_range.mpr hsmall)
    by_cases hlt0 : n < M₀
    · simp only [hlt0, decide_true, ↓reduceIte]
      have hCge : B_fin ≤ C_total := by dsimp only [C_total]; omega
      omega
    · simp only [hlt0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hge0 : M₀ ≤ n := Nat.le_of_not_lt hlt0
      obtain ⟨hd, hl⟩ := hpad_guarded x w hge0 hw
      have hsatR := hSAT_time (padCert (x, w)) hd hl
      have hq'le : ((padCert (x, w)).1 : ℝ) ≤ ((n + c * Nat.log 2 (n + 2) + c : ℕ) : ℝ) :=
        mod_cast max_le
          (by simpa only [← hn] using hq_le x)
          (by dsimp only; omega)
      have hpowR : (2 : ℝ) ^ (((padCert (x, w)).1 : ℝ) - c₀ * ((padCert (x, w)).1 : ℝ) ^ δ) ≤
          (2 : ℝ) ^ (n + c * Nat.log 2 (n + 2) + c) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by
            have hnn := mul_nonneg hc₀.le (Real.rpow_nonneg (Nat.cast_nonneg (padCert (x, w)).1) δ)
            linarith)
      have hTsat_nat : T_sat (padCert (x, w)) ≤ satEnv n := mod_cast
        (by
          have hmul := mul_le_mul_of_nonneg_left hpowR (Nat.cast_nonneg (α := ℝ) M_sat)
          dsimp only [satEnv]
          push_cast
          linarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (n + c * Nat.log 2 (n + 2) + c) by positivity] :
          (T_sat (padCert (x, w)) : ℝ) ≤ (satEnv n : ℝ))
      have hCge : B_fin ≤ C_total := by dsimp only [C_total]; omega
      omega
  · -- Large `n ≥ M_cut`: both `M₀ ≤ n` and `M₁ ≤ n` hold!
    have hge_cut : M_cut ≤ n := Nat.le_of_not_lt hsmall
    have hge0 : M₀ ≤ n := (le_max_left M₀ M₁).trans hge_cut
    have hge1 : M₁ ≤ n := (le_max_right M₀ M₁).trans hge_cut
    have hnotlt0 : ¬ n < M₀ := by omega
    simp only [hnotlt0, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hpolyR, hε_le, hlog_le, htarget_ge1⟩ := hM₁ n hge1
    set target : ℝ := (2 : ℝ) ^ ((n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ)
    have htarget_le_floor : target ≤ 2 * (tBound n : ℝ) := by
      have hlt : target < (tBound n : ℝ) + 1 := Nat.lt_floor_add_one target
      have h1nat : 1 ≤ tBound n :=
        Nat.le_floor (by simpa only [Nat.cast_one] using htarget_ge1)
      have h1 : (1 : ℝ) ≤ (tBound n : ℝ) := by exact_mod_cast h1nat
      linarith
    have hpoly_le_target : (polyEnv n : ℝ) ≤ target :=
      hpolyR.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hε_le)
    obtain ⟨hd, hl⟩ := hpad_guarded x w hge0 hw
    have hsatR := hSAT_time (padCert (x, w)) hd hl
    have hq'_ge : n ≤ (padCert (x, w)).1 := le_max_right (q x) n
    have hq'_le : (padCert (x, w)).1 ≤ n + c * Nat.log 2 (n + 2) + c :=
      max_le (by simpa only [← hn] using hq_le x) (by dsimp only; omega)
    have hexp_sat : ((padCert (x, w)).1 : ℝ) - c₀ * ((padCert (x, w)).1 : ℝ) ^ δ ≤
        (n : ℝ) - (c₀ / 2) * (n : ℝ) ^ δ := by
      have h1 : ((padCert (x, w)).1 : ℝ) ≤ (n : ℝ) + (c : ℝ) * ((Nat.log 2 (n + 2) : ℝ) + 1) := by
        have hcast : ((padCert (x, w)).1 : ℝ) ≤ ((n + c * Nat.log 2 (n + 2) + c : ℕ) : ℝ) := by
          exact_mod_cast hq'_le
        push_cast at hcast
        linarith
      have h2 : (n : ℝ) ^ δ ≤ ((padCert (x, w)).1 : ℝ) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hq'_ge) (lt_trans hε hεδ).le
      have h3 : c₀ * (n : ℝ) ^ δ ≤ c₀ * ((padCert (x, w)).1 : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left h2 hc₀.le
      linarith
    have hsat_le_target : (T_sat (padCert (x, w)) : ℝ) ≤ (M_sat : ℝ) * target + (M_sat : ℝ) :=
      hsatR.trans (by
        have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_sat
        have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) M_sat)
        linarith)
    have hsum_nat : polyEnv n + T_sat (padCert (x, w)) + 2 ≤
        (2 * M_sat + 4) * tBound n + (M_sat + 4) := by
      have hR : ((polyEnv n + T_sat (padCert (x, w)) + 2 : ℕ) : ℝ) ≤
          (((2 * M_sat + 4) * tBound n + (M_sat + 4) : ℕ) : ℝ) := by
        push_cast
        have hMnn : (0 : ℝ) ≤ (M_sat : ℝ) := Nat.cast_nonneg _
        have htb_nn : (0 : ℝ) ≤ (tBound n : ℝ) := Nat.cast_nonneg _
        nlinarith only [hpoly_le_target, hsat_le_target, htarget_le_floor, hMnn, htb_nn]
      exact_mod_cast hR
    have hC1 : 2 * M_sat + 4 ≤ C_total := le_max_left _ _
    have hC2 : M_sat + 4 ≤ C_total :=
      (by omega : M_sat + 4 ≤ B_fin + M_sat + 4).trans (le_max_right _ _)
    have hmul : (2 * M_sat + 4) * tBound n ≤ C_total * tBound n := Nat.mul_le_mul_right _ hC1
    omega

/-- **Hard-witness transfer for quasilinear `ACC⁰` succinct 3-CNF reductions** ([Williams2014],
Section 3, Theorem 3.2 diagonalization step): for every constant decoder depth `dD`, witness
depth `dW`, and modulus `m > 0`, there exist `r_w > 0` and a single language
`H ∈ NTIME encBits (2 ^ n)` such that every polynomial-time uniform depth-`≤ dD` `ACC⁰[m]`
quasilinear succinct 3-CNF reduction `D` of `H` has a satisfiable instance `x ∈ H` whose
represented 3-CNF `toCNFExt m (D x)` admits **no** satisfying assignment computable by a
depth-`≤ dW` `ACC⁰[m]` circuit of code length at most `2 ^ Nat.nthRoot r_w x.length`. -/
theorem exists_hard_acc0Witness_of_quasilinear_reduction (dD dW : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (r_w : ℕ) (H : Set (List Bool)), 0 < r_w ∧ H ∈ NTIME encBits (fun n => 2 ^ n) ∧
      ∀ {q r : List Bool → ℕ}
        (D : (x : List Bool) → Circuit Unbounded.extSignature (q x) (3 * (r x + 1)))
        (c : ℕ),
        ComputableInPolyTime q encBits encUnary →
        ComputableInPolyTime r encBits encUnary →
        ComputableInPolyTime (fun x => (D x).code) encBits (Circuit.encCode Unbounded.encExtOp) →
        (∀ x, (D x).depth ≤ dD) →
        (∀ x, q x ≤ x.length + c * Nat.log 2 (x.length + 2) + c) →
        (∀ x, x ∈ H ↔ (toCNFExt m (D x)).Satisfiable) →
        ∃ x ∈ H, ¬ ∃ W : Circuit Unbounded.extSignature (r x) 1,
          W.depth ≤ dW ∧
          (Circuit.encCode Unbounded.encExtOp W.code).length ≤ 2 ^ Nat.nthRoot r_w x.length ∧
          (toCNFExt m (D x)).eval
            (fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0) = true := by
  obtain ⟨r_w, δ, c₀, hrw_pos, hδ, _, hc₀, hsim⟩ :=
    smallACC0WitnessLanguage_mem_NTIME_of_acc0SAT dD dW hm
  have hss := NTIME_two_pow_sub_rpow_ssubset hδ hc₀
  obtain ⟨H, hH_mem, hH_notMem⟩ := Set.exists_of_ssubset hss
  refine ⟨r_w, H, hrw_pos, hH_mem, ?_⟩
  intro q r D c hq hr hD hdepth hq_le hred
  by_contra hno
  push Not at hno
  have heq : H = smallACC0WitnessLanguage m dW D (fun x => 2 ^ Nat.nthRoot r_w x.length) := by
    ext x
    constructor
    · exact hno x
    · rintro ⟨W, _, _, hsat⟩
      exact (hred x).2 ⟨fun y => W.eval (Unbounded.extInterpretation (modGate m)) y 0, hsat⟩
  rw [heq] at hH_notMem
  exact hH_notMem (hsim D c hq hr hD hdepth hq_le)

end WitnessTransfer

end Cslib.Circuits.Boolean.SymAnd
